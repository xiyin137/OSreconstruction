import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Hdiff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedNormalEOW
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz

/-!
# Reduced Normal to OS45 Common-Edge Coordinates

This file records the concrete coordinate bridge needed by the local
Jost/Ruelle step in the OS reconstruction locality proof.  A reduced adjacent
normal point is represented by fixing the discarded pair center to zero,
reconstructing an absolute source configuration, and then passing to the OS45
flat common-edge chart.

The lemmas below do not assert the missing analytic branch data.  They expose
the exact remaining leaf: construct a Figure-2-4 source patch containing this
absolute representative.  Once that is supplied, the induced reduced-normal
collar is open and the two OS45 real branch domains contain the real collar.
-/

open scoped Classical NNReal
open MeasureTheory

noncomputable section

namespace SCV

/-- Complexify a real continuous linear coordinate map by applying it to real
and imaginary parts separately. -/
noncomputable def realCLMComplexification {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ)) :
    ComplexChartSpace q →L[ℂ] ComplexChartSpace r where
  toFun := fun z a =>
    (L (fun b => (z b).re) a : ℂ) +
      Complex.I * (L (fun b => (z b).im) a : ℂ)
  map_add' := by
    intro z w
    ext a
    change
      (L ((fun b => (z b).re) + fun b => (w b).re) a : ℂ) +
          Complex.I *
            (L ((fun b => (z b).im) + fun b => (w b).im) a : ℂ) =
        ((L (fun b => (z b).re) a : ℂ) +
            Complex.I * (L (fun b => (z b).im) a : ℂ)) +
          ((L (fun b => (w b).re) a : ℂ) +
            Complex.I * (L (fun b => (w b).im) a : ℂ))
    rw [map_add, map_add]
    simp [Pi.add_apply]
    ring_nf
  map_smul' := by
    intro c z
    ext a
    change
      (L (c.re • (fun b => (z b).re) -
            c.im • (fun b => (z b).im)) a : ℂ) +
          Complex.I *
            (L (c.re • (fun b => (z b).im) +
              c.im • (fun b => (z b).re)) a : ℂ) =
        c * ((L (fun b => (z b).re) a : ℂ) +
          Complex.I * (L (fun b => (z b).im) a : ℂ))
    rw [map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  cont := by
    fun_prop

@[simp]
theorem realCLMComplexification_realEmbed {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ))
    (x : Fin q → ℝ) :
    realCLMComplexification L (realEmbed x) = realEmbed (L x) := by
  ext a
  change
    (L x a : ℂ) + Complex.I * (L (0 : Fin q → ℝ) a : ℂ) =
      (L x a : ℂ)
  rw [map_zero]
  simp

/-- Complexification sends a real line with positive imaginary direction to the
corresponding image real line. -/
theorem realCLMComplexification_real_add_imag {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ))
    (x η : Fin q → ℝ) (ε : ℝ) :
    realCLMComplexification L
        (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) =
      fun b => (L x b : ℂ) + (ε : ℂ) * (L η b : ℂ) * Complex.I := by
  ext b
  change
    (L (fun a =>
        ((x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I).re) b : ℂ) +
      Complex.I *
        (L (fun a =>
          ((x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I).im) b : ℂ) =
    (L x b : ℂ) + (ε : ℂ) * (L η b : ℂ) * Complex.I
  have hη : (fun a => ε * η a) = ε • η := by
    ext a
    simp [Pi.smul_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    hη, map_smul]
  ring_nf

/-- Complexification sends a real line with negative imaginary direction to the
corresponding image real line. -/
theorem realCLMComplexification_real_sub_imag {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ))
    (x η : Fin q → ℝ) (ε : ℝ) :
    realCLMComplexification L
        (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) =
      fun b => (L x b : ℂ) - (ε : ℂ) * (L η b : ℂ) * Complex.I := by
  ext b
  change
    (L (fun a =>
        ((x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I).re) b : ℂ) +
      Complex.I *
        (L (fun a =>
          ((x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I).im) b : ℂ) =
    (L x b : ℂ) - (ε : ℂ) * (L η b : ℂ) * Complex.I
  have hηneg : (fun a => -(ε * η a)) = (-ε) • η := by
    ext a
    simp [Pi.smul_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    hηneg, map_smul]
  ring_nf

end SCV

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- On the extended tube, the absolute BHW extension selected from `bvt_F`
agrees with any reduced PET extension of the reduced selected witness after
quotienting by successive differences.

This is the source-side OS-I transfer engine used later by the adjacent normal
route: once a concrete source-side point is known to lie in the extended tube,
its branch value is transported to reduced coordinates by the same reduced PET
extension that controls the canonical reduced ray. -/
theorem extendF_bvt_F_eq_reducedExtension_on_extendedTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d (m + 1)) :
    BHW.extendF (bvt_F OS lgc (m + 1)) z =
      Fred.toFun (BHW.reducedDiffMap (m + 1) d z) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  obtain ⟨Λ, w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  have hF_cinv :
      ∀ (Γ : ComplexLorentzGroup d)
        (y : Fin (m + 1) → Fin (d + 1) → ℂ),
        y ∈ BHW.ForwardTube d (m + 1) →
        BHW.complexLorentzAction Γ y ∈ BHW.ForwardTube d (m + 1) →
        bvt_F OS lgc (m + 1) (BHW.complexLorentzAction Γ y) =
          bvt_F OS lgc (m + 1) y := by
    intro Γ y hy hΓy
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc (m + 1) Γ y
      ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸ hy)
      ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸ hΓy)
  have hext :
      BHW.extendF (bvt_F OS lgc (m + 1)) z =
        bvt_F OS lgc (m + 1) w := by
    simp only [BHW.extendF]
    have hex : ∃ (w' : Fin (m + 1) → Fin (d + 1) → ℂ),
        w' ∈ BHW.ForwardTube d (m + 1) ∧
          ∃ (Γ : ComplexLorentzGroup d),
            z = BHW.complexLorentzAction Γ w' :=
      ⟨w, hw, Λ, hzw⟩
    rw [dif_pos hex]
    rcases hex.choose_spec with ⟨hwc, _Γc, hzc⟩
    exact BHW.extendF_preimage_eq_of_cinv
      (d := d) (n := m + 1) (bvt_F OS lgc (m + 1)) hF_cinv
      hwc hw (hzc.symm.trans hzw)
  have hred_w_forward :
      BHW.reducedDiffMap (m + 1) d w ∈ BHW.ReducedForwardTubeN d m := by
    have hw_pft : w ∈ BHW.PermutedForwardTube d (m + 1) 1 := by
      simpa [BHW.PermutedForwardTube] using hw
    have hpft :=
      BHW.reducedDiffMap_mem_reducedPermutedForwardTube_of_mem_permutedForwardTube
        (d := d) (n := m + 1) (1 : Equiv.Perm (Fin (m + 1))) hw_pft
    rw [BHW.mem_reducedPermutedForwardTube, BHW.permOnReducedDiff_one] at hpft
    simpa [BHW.ReducedForwardTubeN] using hpft
  have hred_w_pet :
      BHW.reducedDiffMap (m + 1) d w ∈
        BHW.reducedPermutedExtendedTube d (m + 1) := by
    simpa [BHW.ReducedPermutedExtendedTubeN] using
      reducedForwardTubeN_subset_reducedPermutedExtendedTubeN
        (d := d) m hred_w_forward
  have hz_pet : z ∈ BHW.PermutedExtendedTube d (m + 1) :=
    BHW.extendedTube_subset_permutedExtendedTube hz
  have hred_z_pet :
      BHW.reducedDiffMap (m + 1) d z ∈
        BHW.reducedPermutedExtendedTube d (m + 1) :=
    ⟨z, hz_pet, rfl⟩
  have hred_eq :
      BHW.reducedDiffMap (m + 1) d z =
        BHW.complexLorentzAction Λ (BHW.reducedDiffMap (m + 1) d w) := by
    rw [hzw]
    exact BHW.reducedDiffMap_action (d := d) (n := m + 1) Λ w
  have hred_action_pet :
      BHW.complexLorentzAction Λ (BHW.reducedDiffMap (m + 1) d w) ∈
        BHW.reducedPermutedExtendedTube d (m + 1) := by
    rw [← hred_eq]
    exact hred_z_pet
  have hFred_lor :
      Fred.toFun (BHW.reducedDiffMap (m + 1) d z) =
        Fred.toFun (BHW.reducedDiffMap (m + 1) d w) := by
    calc
      Fred.toFun (BHW.reducedDiffMap (m + 1) d z)
          = Fred.toFun
              (BHW.complexLorentzAction Λ
                (BHW.reducedDiffMap (m + 1) d w)) := by
              rw [hred_eq]
      _ = Fred.toFun (BHW.reducedDiffMap (m + 1) d w) :=
              Fred.lorentz_invariant Λ (BHW.reducedDiffMap (m + 1) d w)
                hred_w_pet hred_action_pet
  have hw_factor :
      bvt_F OS lgc (m + 1) w =
        Fred.toFun (BHW.reducedDiffMap (m + 1) d w) := by
    calc
      bvt_F OS lgc (m + 1) w
          = bvt_F_reduced (d := d) OS lgc m
              (BHW.reducedDiffMap (m + 1) d w) :=
              bvt_F_eq_bvt_F_reduced_reducedDiffMap
                (d := d) OS lgc m w
      _ = Fred.toFun (BHW.reducedDiffMap (m + 1) d w) :=
              (Fred.agrees_on_reducedForwardTube _ hred_w_forward).symm
  calc
    BHW.extendF (bvt_F OS lgc (m + 1)) z
        = bvt_F OS lgc (m + 1) w := hext
    _ = Fred.toFun (BHW.reducedDiffMap (m + 1) d w) := hw_factor
    _ = Fred.toFun (BHW.reducedDiffMap (m + 1) d z) := hFred_lor.symm

/-- Finite-height source-side value transport after quotienting by reduced
differences, in the support-local form needed for the fixed-test integral
bridge.

The theorem deliberately leaves the tube-membership and coordinate-identification
hypotheses pointwise on the test support.  Those are the real OS45 geometry
obligations; once supplied, the integral is transported through the reduced PET
extension without any further analytic input. -/
theorem integral_extendF_bvt_F_eq_reducedExtension_of_support
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (z : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ)
    (ζ : NPointDomain d (m + 1) → BHW.ReducedNPointConfig d m)
    (φ : NPointDomain d (m + 1) → ℂ)
    (hpoint :
      ∀ u, φ u ≠ 0 →
        z u ∈ BHW.ExtendedTube d (m + 1) ∧
          BHW.reducedDiffMap (m + 1) d (z u) = ζ u) :
    (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (z u) * φ u) =
      ∫ u : NPointDomain d (m + 1),
        Fred.toFun (ζ u) * φ u := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro u
  by_cases hφ : φ u = 0
  · simp [hφ]
  · rcases hpoint u hφ with ⟨huET, hured⟩
    have hext :=
      extendF_bvt_F_eq_reducedExtension_on_extendedTube
        (d := d) OS lgc m Fred (z u) huET
    calc
      BHW.extendF (bvt_F OS lgc (m + 1)) (z u) * φ u =
          Fred.toFun (BHW.reducedDiffMap (m + 1) d (z u)) * φ u := by
        rw [hext]
      _ = Fred.toFun (ζ u) * φ u := by
        rw [hured]

/-- Finite-height transport of a source-side integral to the canonical reduced
branch, once the source-side reduced differences have been identified with the
canonical positive-height ray on the test support. -/
theorem integral_extendF_bvt_F_eq_canonicalReducedBranch_of_support
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d (m + 1) → NPointDomain d m)
    (z : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ)
    (φ : NPointDomain d (m + 1) → ℂ)
    {ε : ℝ} (hε : 0 < ε)
    (hpoint :
      ∀ u, φ u ≠ 0 →
        z u ∈ BHW.ExtendedTube d (m + 1) ∧
          BHW.reducedDiffMap (m + 1) d (z u) =
            fun k μ =>
              (ξ u k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) :
    (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (z u) * φ u) =
      ∫ u : NPointDomain d (m + 1),
        canonicalReducedBranch (d := d) OS lgc m ε (ξ u) * φ u := by
  let ζ : NPointDomain d (m + 1) → BHW.ReducedNPointConfig d m :=
    fun u k μ =>
      (ξ u k μ : ℂ) +
        ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I
  calc
    (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (z u) * φ u) =
      ∫ u : NPointDomain d (m + 1),
        Fred.toFun (ζ u) * φ u := by
        exact
          integral_extendF_bvt_F_eq_reducedExtension_of_support
            (d := d) OS lgc m Fred z ζ φ (by
              intro u hu
              rcases hpoint u hu with ⟨huET, hured⟩
              exact ⟨huET, by simpa [ζ] using hured⟩)
    _ = ∫ u : NPointDomain d (m + 1),
        canonicalReducedBranch (d := d) OS lgc m ε (ξ u) * φ u := by
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall ?_)
        intro u
        have hcan :=
          bvt_F_reduced_canonicalApproach_eq_reducedExtension
            (d := d) OS lgc m Fred (ξ u) hε
        calc
          Fred.toFun (ζ u) * φ u =
              bvt_F_reduced (d := d) OS lgc m (ζ u) * φ u := by
            rw [hcan]
          _ = canonicalReducedBranch (d := d) OS lgc m ε (ξ u) * φ u := by
            rfl

/-- Finite-height transport of a source-side integral to the adjacent-permuted
canonical reduced branch, once the source-side reduced differences have been
identified with the swapped positive-height ray on the test support. -/
theorem integral_extendF_bvt_F_eq_adjacentReducedPermutedBranch_of_support
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d (m + 1) → NPointDomain d m)
    (z : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ)
    (φ : NPointDomain d (m + 1) → ℂ)
    {ε : ℝ} (hε : 0 < ε)
    (hpoint :
      ∀ u, φ u ≠ 0 →
        z u ∈ BHW.ExtendedTube d (m + 1) ∧
          BHW.reducedDiffMap (m + 1) d (z u) =
            fun k μ =>
              (ξ u k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) :
    (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (z u) * φ u) =
      ∫ u : NPointDomain d (m + 1),
        adjacentReducedPermutedBranch (d := d) OS lgc m i j ε (ξ u) *
          φ u := by
  let ζ : NPointDomain d (m + 1) → BHW.ReducedNPointConfig d m :=
    fun u k μ =>
      (ξ u k μ : ℂ) +
        ε *
          permutedCanonicalReducedDirectionC
            (d := d) m (Equiv.swap i j) k μ *
          Complex.I
  calc
    (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (z u) * φ u) =
      ∫ u : NPointDomain d (m + 1),
        Fred.toFun (ζ u) * φ u := by
        exact
          integral_extendF_bvt_F_eq_reducedExtension_of_support
            (d := d) OS lgc m Fred z ζ φ (by
              intro u hu
              rcases hpoint u hu with ⟨huET, hured⟩
              exact ⟨huET, by simpa [ζ] using hured⟩)
    _ = ∫ u : NPointDomain d (m + 1),
        adjacentReducedPermutedBranch (d := d) OS lgc m i j ε (ξ u) *
          φ u := by
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall ?_)
        intro u
        by_cases hφ : φ u = 0
        · simp [hφ]
        · rcases hpoint u hφ with ⟨huET, hured⟩
          have hdomain :
              ζ u ∈ BHW.ReducedPermutedExtendedTubeN d m := by
            refine ⟨z u, BHW.extendedTube_subset_permutedExtendedTube huET, ?_⟩
            simpa [ζ] using hured
          have hperm :=
            bvt_F_reduced_permutedApproach_eq_reducedExtension
              (d := d) OS lgc m i j Fred (ξ u) hε hdomain
          calc
            Fred.toFun (ζ u) * φ u =
                bvt_F_reduced (d := d) OS lgc m (ζ u) * φ u := by
              rw [hperm]
            _ =
                adjacentReducedPermutedBranch (d := d) OS lgc m i j ε
                    (ξ u) * φ u := by
              rfl

/-- A fixed source-side finite-height difference limit becomes the corresponding
canonical-minus-adjacent reduced branch difference limit once both source-side
integrals have been transported through reduced coordinates on the test
support. -/
theorem tendsto_canonicalSubAdjacentReducedBranch_of_sourceSide_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξplus ξminus : NPointDomain d (m + 1) → NPointDomain d m)
    (zplus zminus : ℝ → NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ)
    (φ : NPointDomain d (m + 1) → ℂ)
    (hsource :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (zplus ε u) *
              φ u) -
          ∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (zminus ε u) *
              φ u)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hplus :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u, φ u ≠ 0 →
          zplus ε u ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d (zplus ε u) =
              fun k μ =>
                (ξplus u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)
    (hminus :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u, φ u ≠ 0 →
          zminus ε u ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d (zminus ε u) =
              fun k μ =>
                (ξminus u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ u : NPointDomain d (m + 1),
          canonicalReducedBranch (d := d) OS lgc m ε (ξplus u) *
            φ u) -
        (∫ u : NPointDomain d (m + 1),
          adjacentReducedPermutedBranch (d := d) OS lgc m i j ε
              (ξminus u) *
            φ u)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  refine Filter.Tendsto.congr' ?_ hsource
  filter_upwards [self_mem_nhdsWithin, hplus, hminus] with ε hε hplusε hminusε
  have hplus_eq :
      (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (zplus ε u) * φ u) =
        (∫ u : NPointDomain d (m + 1),
          canonicalReducedBranch (d := d) OS lgc m ε (ξplus u) *
            φ u :=
    integral_extendF_bvt_F_eq_canonicalReducedBranch_of_support
      (d := d) OS lgc m Fred ξplus (zplus ε) φ hε hplusε
  have hminus_eq :
      (∫ u : NPointDomain d (m + 1),
        BHW.extendF (bvt_F OS lgc (m + 1)) (zminus ε u) * φ u) =
        ∫ u : NPointDomain d (m + 1),
          adjacentReducedPermutedBranch (d := d) OS lgc m i j ε
              (ξminus u) *
            φ u :=
    integral_extendF_bvt_F_eq_adjacentReducedPermutedBranch_of_support
      (d := d) OS lgc m i j Fred ξminus (zminus ε) φ hε hminusε
  rw [hplus_eq, hminus_eq]

/-- If a moving absolute source-side path is eventually on the extended tube and
its reduced differences are the canonical reduced ray, then its `extendF`
boundary branch is asymptotic to the canonical reduced branch.

This is the reusable OS-I `(4.12)`--`(4.14)` value-transport step after the
coordinate normal form has identified the source-side reduced differences. -/
theorem tendsto_extendF_bvt_F_sub_canonicalReducedBranch_of_eventually_reducedDiff_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m)
    (z : ℝ → Fin (m + 1) → Fin (d + 1) → ℂ)
    (hET :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        z ε ∈ BHW.ExtendedTube d (m + 1))
    (hred :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.reducedDiffMap (m + 1) d (z ε) =
          fun k μ =>
            (ξ k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          canonicalReducedBranch (d := d) OS lgc m ε ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  have hzero :
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          canonicalReducedBranch (d := d) OS lgc m ε ξ) =ᶠ[l]
        fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, hET, hred] with ε hε hεET hεred
    have hext :=
      extendF_bvt_F_eq_reducedExtension_on_extendedTube
        (d := d) OS lgc m Fred (z ε) hεET
    have hcan :=
      bvt_F_reduced_canonicalApproach_eq_reducedExtension
        (d := d) OS lgc m Fred ξ hε
    calc
      BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          canonicalReducedBranch (d := d) OS lgc m ε ξ
          =
        Fred.toFun (BHW.reducedDiffMap (m + 1) d (z ε)) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
          rw [hext]
          rfl
      _ =
        Fred.toFun
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
          rw [hεred]
          rfl
      _ = 0 := by
          rw [hcan]
          ring
  exact Filter.Tendsto.congr' hzero.symm tendsto_const_nhds

/-- If a moving absolute source-side path is eventually on the extended tube and
its reduced differences are the adjacent-swapped positive-height ray, then its
`extendF` boundary branch is asymptotic to the adjacent-permuted reduced branch.

This is the pointwise lower-side companion to
`tendsto_extendF_bvt_F_sub_canonicalReducedBranch_of_eventually_reducedDiff_eq`:
after the reduced-difference normal form identifies the source path with the
swapped PET ray, the selected reduced branch is transported through the
permuted reduced extension. -/
theorem tendsto_extendF_bvt_F_sub_adjacentReducedPermutedBranch_of_eventually_reducedDiff_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m)
    (z : ℝ → Fin (m + 1) → Fin (d + 1) → ℂ)
    (hET :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        z ε ∈ BHW.ExtendedTube d (m + 1))
    (hred :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.reducedDiffMap (m + 1) d (z ε) =
          fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC
                  (d := d) m (Equiv.swap i j) k μ *
                Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  have hzero :
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ) =ᶠ[l]
        fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, hET, hred] with ε hε hεET hεred
    have hext :=
      extendF_bvt_F_eq_reducedExtension_on_extendedTube
        (d := d) OS lgc m Fred (z ε) hεET
    have hdomain :
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC
                (d := d) m (Equiv.swap i j) k μ *
              Complex.I) ∈ BHW.ReducedPermutedExtendedTubeN d m := by
      refine ⟨z ε, BHW.extendedTube_subset_permutedExtendedTube hεET, ?_⟩
      simpa using hεred
    have hperm :=
      bvt_F_reduced_permutedApproach_eq_reducedExtension
        (d := d) OS lgc m i j Fred ξ hε hdomain
    calc
      BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ
          =
        Fred.toFun (BHW.reducedDiffMap (m + 1) d (z ε)) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) := by
          rw [hext]
          rfl
      _ =
        Fred.toFun
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) := by
          rw [hεred]
          rfl
      _ = 0 := by
          rw [hperm]
          ring
  exact Filter.Tendsto.congr' hzero.symm tendsto_const_nhds

/-- Adjacent-swapped source-side transfer in the exact sign-flip form required
by the reduced-normal EOW packet.

The source-side reduced differences are assumed in the adjacent-swapped
positive-height normal form based at the original reduced-normal point; the
target branch is rewritten to the canonical positive ray based at the
sign-flipped reduced-normal point. -/
theorem tendsto_extendF_bvt_F_sub_signFlipCanonicalBranch_of_eventually_reducedDiff_eq_adjacent
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (z : ℝ → Fin (m + 1) → Fin (d + 1) → ℂ)
    (hET :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        z ε ∈ BHW.ExtendedTube d (m + 1))
    (hred :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.reducedDiffMap (m + 1) d (z ε) =
          fun k μ =>
            (AdjacentNormal.reducedCoordInv (d := d)
                i ⟨i.val + 1, hi⟩
                (AdjacentNormal.reducedAdjacent_succ_ne i hi) p k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC
                  (d := d) m
                  (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i ⟨i.val + 1, hi⟩
              (AdjacentNormal.reducedAdjacent_succ_ne i hi)
              (AdjacentNormal.reducedSignFlip
                (d := d) i ⟨i.val + 1, hi⟩ p)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let ξ : NPointDomain d m :=
    AdjacentNormal.reducedCoordInv (d := d) i j
      (AdjacentNormal.reducedAdjacent_succ_ne i hi) p
  have hswap :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
            adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    exact
      tendsto_extendF_bvt_F_sub_adjacentReducedPermutedBranch_of_eventually_reducedDiff_eq
        (d := d) OS lgc m i j Fred ξ z hET
        (by simpa [j, ξ] using hred)
  refine Filter.Tendsto.congr' ?_ hswap
  filter_upwards with ε
  have hbranch :=
    AdjacentNormal.canonicalReducedBranch_reducedSignFlip_eq_adjacentReducedPermutedBranch
      (d := d) OS lgc i hi p ε
  simp [j, ξ, hbranch]

/-- Moving source-side value transport through a reduced PET extension.

This is the flexible OS-I `(4.12)`--`(4.14)` source-transfer form: the moving
absolute source path need not have reduced differences exactly equal to the
canonical reduced ray.  It is enough that those reduced differences stay in the
reduced PET collar and converge to the same real reduced edge as the canonical
approach. -/
theorem tendsto_extendF_bvt_F_sub_canonicalReducedBranch_of_reducedDiff_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m)
    (z : ℝ → Fin (m + 1) → Fin (d + 1) → ℂ)
    (hξ_pet :
      (fun k μ => (ξ k μ : ℂ)) ∈
        BHW.ReducedPermutedExtendedTubeN d m)
    (hET :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        z ε ∈ BHW.ExtendedTube d (m + 1))
    (hred_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => BHW.reducedDiffMap (m + 1) d (z ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds (fun k μ => (ξ k μ : ℂ)))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          canonicalReducedBranch (d := d) OS lgc m ε ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  let ζcan : ℝ → BHW.ReducedNPointConfig d m := fun ε k μ =>
    (ξ k μ : ℂ) +
      ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I
  have hpos : ∀ᶠ ε : ℝ in l, 0 < ε := by
    exact self_mem_nhdsWithin
  have hcan_pet :
      ∀ᶠ ε : ℝ in l, ζcan ε ∈ BHW.ReducedPermutedExtendedTubeN d m := by
    filter_upwards [hpos] with ε hε
    exact reducedForwardTubeN_subset_reducedPermutedExtendedTubeN
      (d := d) m
      (reducedCanonicalApproach_mem_reducedForwardTube (d := d) m ξ hε)
  have hεC : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (nhds 0) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) l (nhds (0 : ℝ)) := by
      exact Filter.tendsto_id'.2 nhdsWithin_le_nhds
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hid
  have hζcan_tendsto : Filter.Tendsto ζcan l (nhds ξC) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [tendsto_pi_nhds]
    intro μ
    have hterm :
        Filter.Tendsto
          (fun ε : ℝ =>
            (ε : ℂ) * canonicalReducedDirectionC (d := d) m k μ *
              Complex.I) l (nhds 0) := by
      simpa [mul_assoc] using
        (hεC.mul_const
          (canonicalReducedDirectionC (d := d) m k μ * Complex.I))
    simpa [ζcan, ξC] using (tendsto_const_nhds.add hterm)
  have hred_within :
      Filter.Tendsto
        (fun ε : ℝ => BHW.reducedDiffMap (m + 1) d (z ε)) l
        (nhdsWithin ξC (BHW.ReducedPermutedExtendedTubeN d m)) := by
    have hred_pet :
        ∀ᶠ ε : ℝ in l,
          BHW.reducedDiffMap (m + 1) d (z ε) ∈
            BHW.ReducedPermutedExtendedTubeN d m := by
      filter_upwards [hET] with ε hεET
      exact
        ⟨z ε, BHW.extendedTube_subset_permutedExtendedTube hεET, rfl⟩
    exact tendsto_nhdsWithin_iff.mpr ⟨by simpa [ξC] using hred_tendsto, hred_pet⟩
  have hcan_within :
      Filter.Tendsto ζcan l
        (nhdsWithin ξC (BHW.ReducedPermutedExtendedTubeN d m)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hζcan_tendsto, hcan_pet⟩
  have hFred_cont :
      ContinuousWithinAt Fred.toFun
        (BHW.ReducedPermutedExtendedTubeN d m) ξC :=
    Fred.holomorphic.continuousOn.continuousWithinAt (by simpa [ξC] using hξ_pet)
  have hFred_src :
      Filter.Tendsto
        (fun ε : ℝ => Fred.toFun (BHW.reducedDiffMap (m + 1) d (z ε))) l
        (nhds (Fred.toFun ξC)) :=
    hFred_cont.tendsto.comp hred_within
  have hFred_can :
      Filter.Tendsto (fun ε : ℝ => Fred.toFun (ζcan ε)) l
        (nhds (Fred.toFun ξC)) :=
    hFred_cont.tendsto.comp hcan_within
  have hsource_eq :
      (fun ε : ℝ => BHW.extendF (bvt_F OS lgc (m + 1)) (z ε)) =ᶠ[l]
        (fun ε : ℝ => Fred.toFun (BHW.reducedDiffMap (m + 1) d (z ε))) := by
    filter_upwards [hET] with ε hεET
    exact
      extendF_bvt_F_eq_reducedExtension_on_extendedTube
        (d := d) OS lgc m Fred (z ε) hεET
  have hcan_eq :
      (fun ε : ℝ => canonicalReducedBranch (d := d) OS lgc m ε ξ) =ᶠ[l]
        (fun ε : ℝ => Fred.toFun (ζcan ε)) := by
    filter_upwards [hpos] with ε hε
    change bvt_F_reduced (d := d) OS lgc m (ζcan ε) =
      Fred.toFun (ζcan ε)
    simpa [ζcan] using
      bvt_F_reduced_canonicalApproach_eq_reducedExtension
        (d := d) OS lgc m Fred ξ hε
  have hselected_to_ext :
      (fun ε : ℝ =>
        BHW.extendF (bvt_F OS lgc (m + 1)) (z ε) -
          canonicalReducedBranch (d := d) OS lgc m ε ξ) =ᶠ[l]
      (fun ε : ℝ =>
        Fred.toFun (BHW.reducedDiffMap (m + 1) d (z ε)) -
          Fred.toFun (ζcan ε)) := by
    filter_upwards [hsource_eq, hcan_eq] with ε hsrc hcan
    rw [hsrc, hcan]
  refine Filter.Tendsto.congr' hselected_to_ext.symm ?_
  simpa using hFred_src.sub hFred_can

/-- The canonical OS45 flat source-side direction becomes the canonical reduced
imaginary direction after quotienting by reduced differences. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_eq
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ)
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1)))) =
      fun k μ =>
        canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
  ext k μ
  have h :=
    congrFun
      (congrFun
        (BHW.reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id
          (d := d) m) k) μ
  have hdir :
      BHW.reducedDiffMap (m + 1) d
          (fun r ν =>
            (canonicalForwardConeDirection (d := d) (m + 1) r ν : ℂ)) k μ =
        canonicalReducedDirectionC (d := d) m k μ := by
    exact
      congrFun
        (congrFun
          (canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
            (d := d) m) k) μ
  calc
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ)
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1)))) k μ =
        BHW.reducedDiffMap (m + 1) d
          (fun r ν =>
            (canonicalForwardConeDirection (d := d) (m + 1) r ν : ℂ)) k μ *
          Complex.I := h
    _ = canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
      rw [hdir]

/-- Canonical identity-labelled OS45 source-side paths descend to the canonical
reduced side-height ray. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_canonical_id_affine
    (m : ℕ) (ε : ℝ) (u : NPointDomain d (m + 1)) :
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))) u) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))) u) +
        (ε : ℂ) •
          (fun k μ =>
            canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  rw [BHW.reducedDiffMap_os45FlatCommonChartSourceSide_affine]
  rw [reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_eq
    (d := d) m]

/-- Moving the source point by the upper canonical OS45 height puts the
source-side reduced coordinates on the affine OS45 side ray over the
quarter-turned shifted real base.

This is the honest coordinate normal form used by the endpoint DCT step.  The
base term is not the raw canonical finite shell; identifying its boundary
integral with the reduced canonical branch is the remaining analytic
source-transfer leaf. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_canonicalHeight_moved_upper_affine_wickBase
    (m : ℕ) (ε : ℝ) (u : NPointDomain d (m + 1)) :
    let e : NPointDomain d (m + 1) ≃L[ℝ]
        BHW.OS45FlatCommonChartReal d (m + 1) :=
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
    let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
      e (canonicalForwardConeDirection (d := d) (m + 1))
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc
          (e.symm (e u - (((1 : ℝ) * ε) • ηc)))) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.os45QuarterTurnConfig (d := d) (n := m + 1)
          (fun k =>
            wickRotatePoint
              ((e.symm (e u - (((1 : ℝ) * ε) • ηc)) k)))) +
        (ε : ℂ) •
          (fun k μ =>
            canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  intro e ηc
  rw [BHW.reducedDiffMap_os45FlatCommonChartSourceSide_affine]
  rw [reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_eq
    (d := d) m]
  rw [BHW.reducedDiffMap_os45FlatCommonChartSourceSide_zero]
  simp

/-- The negative canonical OS45 side direction descends to the negative
canonical reduced imaginary direction. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_neg_eq
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ)
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1)))) =
      fun k μ =>
        -(canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
      (canonicalForwardConeDirection (d := d) (m + 1))
  have hdir :
      BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ηc =
        -BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ηc := by
    ext k μ
    by_cases hμ : μ = 0
    · subst μ
      simp [BHW.os45FlatCommonChartSourceSideDirection, ηc,
        BHW.os45QuarterTurnCLE_symm_apply, BHW.unflattenCfg]
      ring_nf
    · simp [BHW.os45FlatCommonChartSourceSideDirection, ηc,
        BHW.os45QuarterTurnCLE_symm_apply, BHW.unflattenCfg, hμ,
        add_comm]
  rw [show
      BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))
          (canonicalForwardConeDirection (d := d) (m + 1)) = ηc by
        rfl]
  rw [hdir, map_neg]
  ext k μ
  have hplus :=
    congrFun
      (congrFun
        (reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_eq
          (d := d) m) k) μ
  change
    -((BHW.reducedDiffMap (m + 1) d)
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ηc) k μ) =
      -(canonicalReducedDirectionC (d := d) m k μ * Complex.I)
  simpa [ηc] using congrArg (fun z : ℂ => -z) hplus

/-- Lower moved-source packet in its honest affine reduced-coordinate form.

After applying the adjacent branch permutation, the zero-height base is the
Wick carrier of the moved source reindexed by the branch permutation, and the
side-height direction is the induced reduced permutation of the negative
canonical reduced imaginary direction.  This is the coordinate packet the
endpoint DCT/reindexing leaf must compare with the canonical-after-swap
branch. -/
theorem reducedDiffMap_permAct_os45FlatCommonChartSourceSide_canonicalHeight_moved_lower_affine_wickBase
    (m : ℕ) (τ : Equiv.Perm (Fin (m + 1)))
    (ε : ℝ) (u : NPointDomain d (m + 1)) :
    let e : NPointDomain d (m + 1) ≃L[ℝ]
        BHW.OS45FlatCommonChartReal d (m + 1) :=
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
    let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
      e (canonicalForwardConeDirection (d := d) (m + 1))
    let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
      ((-1 : ℝ) * ε) • ηc
    BHW.reducedDiffMap (m + 1) d
        (BHW.permAct (d := d) τ
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc
            (e.symm (e u - a)))) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.os45QuarterTurnConfig (d := d) (n := m + 1)
          (fun k =>
            wickRotatePoint ((e.symm (e u - a)) (τ k)))) +
        (ε : ℂ) •
          BHW.permOnReducedDiff (d := d) (n := m + 1) τ
            (fun k μ =>
              -(canonicalReducedDirectionC (d := d) m k μ * Complex.I)) := by
  intro e ηc a
  let zε : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.os45FlatCommonChartSourceSide d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc
      (e.symm (e u - a))
  let z0 : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.os45FlatCommonChartSourceSide d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηc
      (e.symm (e u - a))
  let dir : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.os45FlatCommonChartSourceSideDirection
      (d := d) (n := m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ηc
  have hzε :
      BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) τ zε) =
        BHW.permOnReducedDiff (d := d) (n := m + 1) τ
          (BHW.reducedDiffMap (m + 1) d zε) := by
    simpa [zε, BHW.permAct] using
      (BHW.permOnReducedDiff_reducedDiffMap
        (d := d) (n := m + 1) τ zε).symm
  have hz0 :
      BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) τ z0) =
        BHW.permOnReducedDiff (d := d) (n := m + 1) τ
          (BHW.reducedDiffMap (m + 1) d z0) := by
    simpa [z0, BHW.permAct] using
      (BHW.permOnReducedDiff_reducedDiffMap
        (d := d) (n := m + 1) τ z0).symm
  have hsource_aff :
      BHW.reducedDiffMap (m + 1) d zε =
        BHW.reducedDiffMap (m + 1) d z0 +
          (ε : ℂ) • BHW.reducedDiffMap (m + 1) d dir := by
    simpa [zε, z0, dir] using
      BHW.reducedDiffMap_os45FlatCommonChartSourceSide_affine
        (d := d) (n := m + 1)
        (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc
        (e.symm (e u - a))
  have hdir :
      BHW.reducedDiffMap (m + 1) d dir =
        fun k μ =>
          -(canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
    simpa [dir, ηc, e] using
      reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_neg_eq
        (d := d) m
  have hzero_base :
      BHW.permAct (d := d) τ z0 =
        BHW.os45QuarterTurnConfig (d := d) (n := m + 1)
          (fun k =>
            wickRotatePoint ((e.symm (e u - a)) (τ k))) := by
    simpa [z0] using
      BHW.permAct_os45FlatCommonChartSourceSide_zero
        (d := d) (n := m + 1) τ
        (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ηc
        (e.symm (e u - a))
  calc
    BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) τ zε)
        = BHW.permOnReducedDiff (d := d) (n := m + 1) τ
            (BHW.reducedDiffMap (m + 1) d zε) := hzε
    _ = BHW.permOnReducedDiff (d := d) (n := m + 1) τ
          (BHW.reducedDiffMap (m + 1) d z0 +
            (ε : ℂ) • BHW.reducedDiffMap (m + 1) d dir) := by
          rw [hsource_aff]
    _ = BHW.permOnReducedDiff (d := d) (n := m + 1) τ
          (BHW.reducedDiffMap (m + 1) d z0) +
        (ε : ℂ) •
          BHW.permOnReducedDiff (d := d) (n := m + 1) τ
            (BHW.reducedDiffMap (m + 1) d dir) := by
          rw [map_add, map_smul]
    _ = BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) τ z0) +
        (ε : ℂ) •
          BHW.permOnReducedDiff (d := d) (n := m + 1) τ
            (BHW.reducedDiffMap (m + 1) d dir) := by
          rw [← hz0]
    _ = BHW.reducedDiffMap (m + 1) d
          (BHW.os45QuarterTurnConfig (d := d) (n := m + 1)
            (fun k =>
              wickRotatePoint ((e.symm (e u - a)) (τ k)))) +
        (ε : ℂ) •
          BHW.permOnReducedDiff (d := d) (n := m + 1) τ
            (fun k μ =>
              -(canonicalReducedDirectionC (d := d) m k μ * Complex.I)) := by
          rw [hdir]
          rw [hzero_base]

set_option maxHeartbeats 1200000
/-- Uniform compact-source upper ET membership for the canonical OS45
cone-height.

This is the Figure-2-4 local-wedge geometry needed by the integrated endpoint:
one collar radius works for every source point in a compact source window
inside `P.V`. -/
theorem eventually_forall_sourceSide_canonicalHeight_upper_mem_extendedTube_of_compact_source
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    {Ksrc : Set (NPointDomain d (m + 1))}
    (hKsrc : IsCompact Ksrc) (hKsrc_sub : Ksrc ⊆ P.V) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ u ∈ Ksrc,
        let e : NPointDomain d (m + 1) ≃L[ℝ]
            BHW.OS45FlatCommonChartReal d (m + 1) :=
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
        let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
          e (canonicalForwardConeDirection (d := d) (m + 1))
        let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
          ((1 : ℝ) * ε) • ηc
        BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc
            (e.symm (e u - a)) ∈
          BHW.ExtendedTube d (m + 1) := by
  classical
  let e : NPointDomain d (m + 1) ≃L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
  let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
    e (canonicalForwardConeDirection (d := d) (m + 1))
  let K : Set (BHW.OS45FlatCommonChartReal d (m + 1)) := e '' Ksrc
  have hK : IsCompact K := hKsrc.image e.continuous
  have hK_sub :
      K ⊆ BHW.os45FlatCommonChartEdgeSet d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1))) := by
    intro x hx
    rcases hx with ⟨u, huK, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1))) u).2 (hKsrc_sub huK)
  have hηc_cone : ηc ∈ BHW.os45FlatCommonChartCone d (m + 1) := by
    simpa [e, ηc] using
      BHW.os45CommonEdgeFlatCLE_canonicalForwardConeDirection_mem_cone
        (d := d) m
  have hKη_sub : ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1))) ⊆
      BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    rw [Set.mem_singleton_iff] at hη
    subst η
    exact hηc_cone
  obtain ⟨r, hr_pos, hside⟩ :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P) K hK hK_sub
      ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1)))
      isCompact_singleton hKη_sub
  have hsmall :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ε < r := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds hr_pos)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt u huK
  let a : BHW.OS45FlatCommonChartReal d (m + 1) := ((1 : ℝ) * ε) • ηc
  have homega :
      (fun b => (e u b : ℂ) + (ε : ℂ) * (ηc b : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) :=
    (hside (e u) ⟨u, huK, rfl⟩ ηc (by simp) ε hε_pos hε_lt).1
  have hflat_eq :
      (fun b =>
          ((e (e.symm (e u - a)) + ((1 : ℝ) * ε) • ηc) b : ℂ) +
            ((((1 : ℝ) * ε) • ηc) b : ℂ) * Complex.I) =
        fun b => (e u b : ℂ) + (ε : ℂ) * (ηc b : ℂ) * Complex.I := by
    funext b
    simp [a, sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hflat :
      (fun b =>
          ((e (e.symm (e u - a)) + ((1 : ℝ) * ε) • ηc) b : ℂ) +
            ((((1 : ℝ) * ε) • ηc) b : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) := by
    rw [hflat_eq]
    exact homega
  have hET :=
    (BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
      d (m + 1) (1 : Equiv.Perm (Fin (m + 1)))
      (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc
      (e.symm (e u - a))).1 hflat
  simpa [e, ηc, a] using hET

set_option maxHeartbeats 1200000
/-- Uniform compact-source lower ET membership for the canonical OS45
cone-height, with the adjacent branch permutation applied. -/
theorem eventually_forall_sourceSide_canonicalHeight_lower_mem_extendedTube_of_compact_source
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    {Ksrc : Set (NPointDomain d (m + 1))}
    (hKsrc : IsCompact Ksrc) (hKsrc_sub : Ksrc ⊆ P.V) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ u ∈ Ksrc,
        let e : NPointDomain d (m + 1) ≃L[ℝ]
            BHW.OS45FlatCommonChartReal d (m + 1) :=
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
        let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
          e (canonicalForwardConeDirection (d := d) (m + 1))
        let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
          ((-1 : ℝ) * ε) • ηc
        BHW.permAct (d := d)
            ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm)
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc
              (e.symm (e u - a))) ∈
          BHW.ExtendedTube d (m + 1) := by
  classical
  let e : NPointDomain d (m + 1) ≃L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
  let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
    e (canonicalForwardConeDirection (d := d) (m + 1))
  let K : Set (BHW.OS45FlatCommonChartReal d (m + 1)) := e '' Ksrc
  have hK : IsCompact K := hKsrc.image e.continuous
  have hK_sub :
      K ⊆ BHW.os45FlatCommonChartEdgeSet d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1))) := by
    intro x hx
    rcases hx with ⟨u, huK, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1))) u).2 (hKsrc_sub huK)
  have hηc_cone : ηc ∈ BHW.os45FlatCommonChartCone d (m + 1) := by
    simpa [e, ηc] using
      BHW.os45CommonEdgeFlatCLE_canonicalForwardConeDirection_mem_cone
        (d := d) m
  have hKη_sub : ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1))) ⊆
      BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    rw [Set.mem_singleton_iff] at hη
    subst η
    exact hηc_cone
  obtain ⟨r, hr_pos, hside⟩ :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P) K hK hK_sub
      ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1)))
      isCompact_singleton hKη_sub
  have hsmall :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ε < r := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds hr_pos)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt u huK
  let a : BHW.OS45FlatCommonChartReal d (m + 1) := ((-1 : ℝ) * ε) • ηc
  have homega :
      (fun b => (e u b : ℂ) - (ε : ℂ) * (ηc b : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) :=
    (hside (e u) ⟨u, huK, rfl⟩ ηc (by simp) ε hε_pos hε_lt).2
  have hflat_eq :
      (fun b =>
          ((e (e.symm (e u - a)) + ((-1 : ℝ) * ε) • ηc) b : ℂ) +
            ((((-1 : ℝ) * ε) • ηc) b : ℂ) * Complex.I) =
        fun b => (e u b : ℂ) - (ε : ℂ) * (ηc b : ℂ) * Complex.I := by
    funext b
    simp [a, sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hflat :
      (fun b =>
          ((e (e.symm (e u - a)) + ((-1 : ℝ) * ε) • ηc) b : ℂ) +
            ((((-1 : ℝ) * ε) • ηc) b : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) := by
    rw [hflat_eq]
    exact homega
  have hET :=
    (BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
      d (m + 1) (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc
      (e.symm (e u - a))).1 hflat
  simpa [e, ηc, a] using hET

set_option maxHeartbeats 1200000 in
/-- Support-form upper ET collar for the canonical OS45 cone-height.

This is the honest geometric support input produced from a compact source
window containing the topological support of the lifted reduced test. -/
theorem eventually_sourceSide_canonicalHeight_upper_mem_extendedTube_of_lift_tsupport_subset_compact
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    {Ksrc : Set (NPointDomain d (m + 1))}
    (hKsrc : IsCompact Ksrc) (hKsrc_sub : Ksrc ⊆ P.V)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) (ψ : SchwartzNPoint d m)
    (hliftK :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Ksrc) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ u : NPointDomain d (m + 1),
        ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
          NPointDomain d (m + 1) → ℂ) u ≠ 0 →
          let e : NPointDomain d (m + 1) ≃L[ℝ]
              BHW.OS45FlatCommonChartReal d (m + 1) :=
            BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1)))
          let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
            e (canonicalForwardConeDirection (d := d) (m + 1))
          let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
            ((1 : ℝ) * ε) • ηc
          BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc
              (e.symm (e u - a)) ∈
            BHW.ExtendedTube d (m + 1) := by
  let f : NPointDomain d (m + 1) → ℂ :=
    ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
      NPointDomain d (m + 1) → ℂ)
  have hmem :=
    eventually_forall_sourceSide_canonicalHeight_upper_mem_extendedTube_of_compact_source
      (d := d) P hKsrc hKsrc_sub
  filter_upwards [hmem] with ε hε u hu
  have huK : u ∈ Ksrc := by
    have hu_support : u ∈ Function.support f :=
      Function.mem_support.mpr (by simpa [f] using hu)
    exact hliftK (subset_tsupport f hu_support)
  simpa [f] using hε u huK

set_option maxHeartbeats 1200000 in
/-- Support-form lower ET collar for the canonical OS45 cone-height, after the
adjacent branch permutation. -/
theorem eventually_sourceSide_canonicalHeight_lower_mem_extendedTube_of_lift_tsupport_subset_compact
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    {Ksrc : Set (NPointDomain d (m + 1))}
    (hKsrc : IsCompact Ksrc) (hKsrc_sub : Ksrc ⊆ P.V)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) (ψ : SchwartzNPoint d m)
    (hliftK :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Ksrc) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ u : NPointDomain d (m + 1),
        ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
          NPointDomain d (m + 1) → ℂ) u ≠ 0 →
          let e : NPointDomain d (m + 1) ≃L[ℝ]
              BHW.OS45FlatCommonChartReal d (m + 1) :=
            BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1)))
          let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
            e (canonicalForwardConeDirection (d := d) (m + 1))
          let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
            ((-1 : ℝ) * ε) • ηc
          BHW.permAct (d := d)
              ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc
                (e.symm (e u - a))) ∈
            BHW.ExtendedTube d (m + 1) := by
  let f : NPointDomain d (m + 1) → ℂ :=
    ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
      NPointDomain d (m + 1) → ℂ)
  have hmem :=
    eventually_forall_sourceSide_canonicalHeight_lower_mem_extendedTube_of_compact_source
      (d := d) P hKsrc hKsrc_sub
  filter_upwards [hmem] with ε hε u hu
  have huK : u ∈ Ksrc := by
    have hu_support : u ∈ Function.support f :=
      Function.mem_support.mpr (by simpa [f] using hu)
    exact hliftK (subset_tsupport f hu_support)
  simpa [f] using hε u huK

omit [NeZero d] in
/-- The reduced-test lift has the source-collar support required after pulling
it to OS45 flat common-edge coordinates.

This is the concrete test-admissibility bridge for the active Path 2 source
transfer: a reduced collar test is first lifted to an absolute source test, and
then pulled back to the flat Figure-2-4 common chart.  The resulting flat test
is compactly supported and supported over the chosen source window. -/
theorem flatCommonChartPullback_reducedTestLift_support
    {m : ℕ}
    (ρperm : Equiv.Perm (Fin (m + 1)))
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {U : Set (NPointDomain d (m + 1))}
    (hU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ U) :
    HasCompactSupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
          (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))) :
          BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
      tsupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
          (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))) :
          BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm '' U := by
  let f : SchwartzNPoint d (m + 1) := BHW.reducedTestLift m d χ ψ
  have hf_compact : HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) := by
    simpa [f] using
      reducedTestLift_hasCompactSupport
        (d := d) χ ψ hχ_compact hψ_compact
  constructor
  · simpa [f] using
      BHW.hasCompactSupport_comp_os45CommonEdgeFlatCLE_symm
        (d := d) (n := m + 1) ρperm f hf_compact
  · simpa [f] using
      BHW.tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_image
        (d := d) (n := m + 1) ρperm f hU

/-- Source-side support package for the flat pullback of a reduced-test lift.

This is the support packet used when applying the OS45 moving-source theorem to
the lifted reduced collar test: if the absolute lift is supported in a source
window `U ⊆ P.V`, then its flat common-chart pullback is compactly supported,
lies on the Figure-2-4 flat edge, and lies over the source window image. -/
theorem flatCommonChartPullback_reducedTestLift_sourceSideSupport
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (ρperm : Equiv.Perm (Fin (m + 1)))
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {U : Set (NPointDomain d (m + 1))}
    (hU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ U)
    (hUP : U ⊆ P.V) :
    HasCompactSupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
          (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))) :
          BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
      tsupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
          (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))) :
          BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P ρperm ∧
      tsupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
          (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))) :
          BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm '' U := by
  let f : SchwartzNPoint d (m + 1) := BHW.reducedTestLift m d χ ψ
  have hsupport :=
    flatCommonChartPullback_reducedTestLift_support
      (d := d) ρperm χ ψ hχ_compact hψ_compact hU
  refine ⟨hsupport.1, ?_, hsupport.2⟩
  have hV : tsupport (f : NPointDomain d (m + 1) → ℂ) ⊆ P.V :=
    hU.trans hUP
  simpa [f] using
    BHW.tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_edgeSet
      (d := d) (n := m + 1) (P := P) ρperm f hV

/-- Reduced-test specialization of the OS45 moving-source branch comparison.

This is the fixed-test bridge needed on Path 2: the flat Figure-2-4 test is
the inverse OS45 common-edge pullback of the lifted reduced collar test, and
the support hypotheses required by the moving-source theorem are discharged
from `flatCommonChartPullback_reducedTestLift_sourceSideSupport`. -/
theorem tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_sourceCommonEdge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hUsrcP : Usrc ⊆ P.V)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηC : η ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hsource :
      ∀ u ∈ Ksrc,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc) :
    let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm)
        (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φFlat x) -
        ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φFlat x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ ψ
        hχ_compact hψ_compact hliftU hUsrcP
  simpa [φFlat] using
    BHW.OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceCommonEdge
      (d := d) OS lgc D
      hΩplus_open hΩminus_open hFplus_cont hFminus_cont
      hUsrc_open hUsrc_sub_K hKsrc η hηC h0_plus h0_minus
      hsource φFlat hsupport.1 hsupport.2.1 hsupport.2.2

/-- Reduced-test specialization of the OS45 moving-source branch comparison from
the source-side zero representation.

This is the distributional OS-I `(4.12)`--`(4.14)` form of
`tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_sourceCommonEdge`.
The fixed flat test is still the inverse OS45 common-edge pullback of the lifted
reduced collar test; the zero-height equality is supplied by the local
`RepresentsDistributionOn 0` packet on the source collar. -/
theorem tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hUsrcP : Usrc ⊆ P.V)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηC : η ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc) :
    let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm)
        (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φFlat x) -
        ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φFlat x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ ψ
        hχ_compact hψ_compact hliftU hUsrcP
  simpa [φFlat] using
    BHW.OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceRepresentsOn
      (d := d) OS lgc D
      hΩplus_open hΩminus_open hFplus_cont hFminus_cont
      hUsrc_open hUsrc_sub_K hKsrc η hηC h0_plus h0_minus
      hrep φFlat hsupport.1 hsupport.2.1 hsupport.2.2

/-- Reduced-test specialization of the fixed zero-diagonal source-side
`extendF` comparison from a source-side zero representation.

The flat test is the inverse common-edge pullback of the lifted reduced test,
so the Figure-2-4 zero-diagonal cutoff recovers exactly
`BHW.reducedTestLift`.  This is the source-side finite-height form needed
before transporting the two integrals through the reduced PET extension. -/
theorem tendsto_sourceSide_extendF_fixedZeroDiagonal_difference_zero_reducedTestLift_of_sourceRepresentsOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hUsrcP : Usrc ⊆ P.V)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η u) *
            ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u) -
        ∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η u)) *
            ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ ψ
        hχ_compact hψ_compact hliftU hUsrcP
  have hψV :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ P.V :=
    hliftU.trans hUsrcP
  have hzero_eq :
      ((D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin (m + 1))) φFlat).1 :
          SchwartzNPoint d (m + 1)) =
        (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) := by
    simpa [φFlat] using
      D.toZeroDiagonalCLM_flatPullback_eq
        (1 : Equiv.Perm (Fin (m + 1)))
        (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
        hψV
  have hlim :=
    D.tendsto_sourceSide_extendF_fixedZeroDiagonal_difference_zero_of_sourceRepresentsOn
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus hrep φFlat hsupport.1 hsupport.2.2
  simpa [φFlat, hzero_eq] using hlim

/-- Fixed zero-diagonal reduced-test source representation plus finite-height
support transport gives the reduced canonical/adjacent branch difference limit.

This is the concrete handoff after the source-side distributional theorem: the
only remaining hypotheses are the genuine finite-height OS45 transport facts on
the support of `BHW.reducedTestLift`. -/
theorem tendsto_reducedBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn_and_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hUsrcP : Usrc ⊆ P.V)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (ξplus ξminus : NPointDomain d (m + 1) → NPointDomain d m)
    (hplus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η u ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η u) =
              fun k μ =>
                (ξplus u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)
    (hminus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η u) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η u)) =
              fun k μ =>
                (ξminus u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ u : NPointDomain d (m + 1),
          canonicalReducedBranch (d := d) OS lgc m ε (ξplus u) *
            ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u) -
        ∫ u : NPointDomain d (m + 1),
          adjacentReducedPermutedBranch (d := d) OS lgc m i
              ⟨i.val + 1, hi⟩ ε (ξminus u) *
            ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let φ : NPointDomain d (m + 1) → ℂ :=
    ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
      NPointDomain d (m + 1) → ℂ)
  let zplus : ℝ → NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ := fun ε u =>
    BHW.os45FlatCommonChartSourceSide d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η u
  let zminus : ℝ → NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ := fun ε u =>
    BHW.permAct (d := d)
      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
      (BHW.os45FlatCommonChartSourceSide d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η u)
  have hsource :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (zplus ε u) * φ u) -
          ∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (zminus ε u) * φ u)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [φ, zplus, zminus] using
      tendsto_sourceSide_extendF_fixedZeroDiagonal_difference_zero_reducedTestLift_of_sourceRepresentsOn
        (d := d) OS lgc D hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hUsrcP
        η h0_plus h0_minus hrep χ ψ hχ_compact hψ_compact hliftU
  simpa [φ, zplus, zminus] using
    tendsto_canonicalSubAdjacentReducedBranch_of_sourceSide_transport
      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ Fred
      ξplus ξminus zplus zminus φ hsource
      (by simpa [φ, zplus] using hplus_transport)
      (by simpa [φ, zminus] using hminus_transport)

/-- Source-window zero representation plus finite-height transport gives the
local reduced branch-difference limit in the exact form consumed by
`ReducedLocalAdjacentBoundaryCLMInvariant`.

Compared with
`tendsto_reducedBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn_and_transport`,
this theorem fixes the reduced base of both transported source-side branches to
the actual reduced-difference map of the lifted absolute test, integrates out
the normalized basepoint cutoff, rewrites the adjacent branch as the
canonical-after-swap branch, and flips the sign.  The remaining hypotheses are
therefore precisely the source-window and finite-height transport obligations,
not pointwise reduced-normal EOW data. -/
theorem tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn_and_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 ηsrc u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηsrc u ∈ Ωminus)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc)
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hplus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)
    (hminus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            ψ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz ψ
  let Gcan : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    canonicalReducedBranch (d := d) OS lgc m ε ξ
  let Gadj : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ
  have hsource :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            Gcan ε (BHW.reducedDiffMapReal (m + 1) d u) * f u) -
          ∫ u : NPointDomain d (m + 1),
            Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u)
        l
        (nhds 0) := by
    simpa [l, f, Gcan, Gadj, j] using
      tendsto_reducedBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn_and_transport
        (d := d) OS lgc D Fred hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hUsrcP
        ηsrc h0_plus h0_minus hrep χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU
        (fun u => BHW.reducedDiffMapReal (m + 1) d u)
        (fun u => BHW.reducedDiffMapReal (m + 1) d u)
        (by simpa [f, l, j] using hplus_transport)
        (by simpa [f, l, j] using hminus_transport)
  have hadj_int :
      ∀ᶠ (ε : ℝ) in l,
        MeasureTheory.Integrable
          (fun u : NPointDomain d (m + 1) =>
            Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u)
          MeasureTheory.volume := by
    simpa [l, f, Gadj, j] using
      bvt_F_reduced_permuted_integrable_eventually
        (d := d) OS lgc m i j f
  have hcan_int :
      ∀ᶠ (ε : ℝ) in l,
        MeasureTheory.Integrable
          (fun u : NPointDomain d (m + 1) =>
            Gcan ε (BHW.reducedDiffMapReal (m + 1) d u) * f u)
          MeasureTheory.volume := by
    simpa [l, f, Gcan] using
      bvt_F_reduced_canonical_integrable_eventually
        (d := d) OS lgc m f
  have hcanonical_sub_adjacent :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m, Gcan ε ξ * ψ ξ) -
          ∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ)
        l
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hsource
    filter_upwards [hcan_int, hadj_int] with ε hcanε hadjε
    have hcan_lift :
        (∫ u : NPointDomain d (m + 1),
          Gcan ε (BHW.reducedDiffMapReal (m + 1) d u) * f u) =
          ∫ ξ : NPointDomain d m, Gcan ε ξ * ψ ξ := by
      simpa [f] using
        integral_reducedTestLift_eq_reduced
          (d := d) m χ ψ (Gcan ε) hcanε
    have hadj_lift :
        (∫ u : NPointDomain d (m + 1),
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u) =
          ∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ := by
      simpa [f] using
        integral_reducedTestLift_eq_reduced
          (d := d) m χ ψ (Gadj ε) hadjε
    rw [hcan_lift, hadj_lift]
  have hcanonical_sub_adjacent_neg :
      Filter.Tendsto
        (fun ε : ℝ =>
          -((∫ ξ : NPointDomain d m, Gcan ε ξ * ψ ξ) -
            ∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    have hneg := hcanonical_sub_adjacent.neg
    simpa [l] using hneg
  refine Filter.Tendsto.congr' ?_ hcanonical_sub_adjacent_neg
  filter_upwards with ε
  have hadj_eq :
      (∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ) =
        ∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ *
            ψ ξ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ξ
    simpa [Gadj] using
      congrArg (fun z : ℂ => z * ψ ξ)
        (adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
          (d := d) OS lgc m i j ε ξ)
  calc
    -((∫ ξ : NPointDomain d m, Gcan ε ξ * ψ ξ) -
        ∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ)
        =
      (∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ) -
        ∫ ξ : NPointDomain d m, Gcan ε ξ * ψ ξ := by
          ring
    _ =
      (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ *
            ψ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ := by
          rw [← hadj_eq]

/-- Hdiff-germ form of the integrated reduced branch-difference theorem.

The Hdiff germ supplies the zero horizontal common-edge distribution on the
source carrier; after restriction to the source window, the integrated
source-representation/transport theorem yields the exact
canonical-after-swap minus canonical reduced branch limit used by the local
boundary-CLM layer.  The finite-height transport hypotheses remain explicit. -/
theorem tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ θ : SchwartzNPoint d (m + 1),
        HasCompactSupport (θ : NPointDomain d (m + 1) → ℂ) →
        tsupport (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * θ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hKsrc_sub_U : Ksrc ⊆ U)
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 ηsrc u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηsrc u ∈ Ωminus)
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hplus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)
    (hminus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            ψ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  have hrepU :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) U := by
    exact
      BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
        (d := d) hd OS lgc (P := P) U hU_open hU_nonempty
        Ucx Hdiff hUcx_open hUcx_connected hwick_mem hcommon_mem
        hHdiff_holo hwick_pairing_zero hcommon_trace
  have hrepUsrc :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc := by
    refine
      SCV.representsDistributionOn_congr_on_subset
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        hrepU ?_ ?_
    · intro u _hu
      rfl
    · intro u hu
      exact hKsrc_sub_U (hUsrc_sub_K hu)
  exact
    tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn_and_transport
      (d := d) OS lgc D Fred hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hUsrcP
      ηsrc h0_plus h0_minus hrepUsrc χ ψ hχ_compact hψ_compact
      hliftU hplus_transport hminus_transport

/-- Hdiff-germ form of the reduced-test OS45 moving-source comparison.

This is the Lean carrier used immediately after the OS-I `(4.12)`--`(4.14)`
source-side branch transfer has been produced.  The local holomorphic
difference germ has zero Wick-side compact-test boundary value and its
horizontal common-edge trace is the adjacent-minus-ordinary source branch.  The
identity theorem first turns that into pointwise common-edge equality on the
source carrier, and the checked moving-source proof then gives the flat
side-branch limit for the lifted reduced test. -/
theorem tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_HdiffGerm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ θ : SchwartzNPoint d (m + 1),
        HasCompactSupport (θ : NPointDomain d (m + 1) → ℂ) →
        tsupport (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * θ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hKsrc_sub_U : Ksrc ⊆ U)
    (hUsrcP : Usrc ⊆ P.V)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηC : η ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 η u ∈ Ωminus)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc) :
    let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm)
        (BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1))
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φFlat x) -
        ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φFlat x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  have hrepU :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) U := by
    exact
      BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
        (d := d) hd OS lgc (P := P) U hU_open hU_nonempty
        Ucx Hdiff hUcx_open hUcx_connected hwick_mem hcommon_mem
        hHdiff_holo hwick_pairing_zero hcommon_trace
  have hrepUsrc :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc := by
    refine
      SCV.representsDistributionOn_congr_on_subset
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        hrepU ?_ ?_
    · intro u _hu
      rfl
    · intro u hu
      exact hKsrc_sub_U (hUsrc_sub_K hu)
  exact
    tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn
      (d := d) OS lgc D
      hΩplus_open hΩminus_open hFplus_cont hFminus_cont
      hUsrc_open hUsrc_sub_K hKsrc hUsrcP η hηC h0_plus h0_minus
      hrepUsrc χ ψ hχ_compact hψ_compact hliftU

set_option maxHeartbeats 1200000 in
/-- Private diagnostic endpoint reducer for an over-strong reindexed
moving-source hypothesis.

The exported theorem-2 route should use
`tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_sourceSide_shifted_transport`,
which takes the OS-I endpoint limits directly.  This private lemma is retained
only to document the stronger finite-height support condition that would imply
the plus endpoint transport; it is not a theorem-2 producer surface. -/
private theorem tendsto_flatCommonChart_branch_integral_sub_canonicalReducedBranch_reducedTestLift_of_reindexed_sourceSide_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ}
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (σ ρperm : Equiv.Perm (Fin (m + 1)))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hflat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ
              (fun j =>
                ((x + (sgn * ε) • η) j : ℂ) +
                  (((sgn * ε) • η) j : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
              (x + (sgn * ε) • η)))
    (htransport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u : NPointDomain d (m + 1),
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            let e : NPointDomain d (m + 1) ≃L[ℝ]
                BHW.OS45FlatCommonChartReal d (m + 1) :=
              BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm
            let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
              (sgn * ε) • η
            BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η (e.symm (e u - a))) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    ρperm sgn ε η (e.symm (e u - a)))) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ
            (fun a =>
              (x a : ℂ) + (((sgn * ε) • η) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let e : NPointDomain d (m + 1) ≃L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz ψ
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f
  let Target : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  have hφeq : ∀ u : NPointDomain d (m + 1), φFlat (e u) = f u := by
    intro u
    simp [φFlat, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hcan_int :
      ∀ᶠ (ε : ℝ) in l,
        MeasureTheory.Integrable
          (fun u : NPointDomain d (m + 1) =>
            canonicalReducedBranch (d := d) OS lgc m ε
              (BHW.reducedDiffMapReal (m + 1) d u) * f u)
          MeasureTheory.volume := by
    simpa [l, f] using
      bvt_F_reduced_canonical_integrable_eventually
        (d := d) OS lgc m f
  have hsource_moving :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η)))) *
              φFlat (e u)) - Target ε)
        l (nhds 0) := by
    refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) l (nhds 0))
    filter_upwards [self_mem_nhdsWithin, htransport, hcan_int] with ε hε_pos htrans hcanε
    have hpoint :
        ∀ u : NPointDomain d (m + 1),
          φFlat (e u) ≠ 0 →
            BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η))) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    ρperm sgn ε η
                    (e.symm (e u - (sgn * ε) • η)))) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I := by
      intro u hφ_ne
      have hf_ne : (f : NPointDomain d (m + 1) → ℂ) u ≠ 0 := by
        simpa [hφeq u] using hφ_ne
      simpa [e] using htrans u hf_ne
    have hbranch :=
      integral_extendF_bvt_F_eq_canonicalReducedBranch_of_support
        (d := d) OS lgc m Fred
        (fun u : NPointDomain d (m + 1) =>
          BHW.reducedDiffMapReal (m + 1) d u)
        (fun u : NPointDomain d (m + 1) =>
          BHW.permAct (d := d) σ.symm
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              ρperm sgn ε η
              (e.symm (e u - (sgn * ε) • η))))
        (fun u : NPointDomain d (m + 1) => φFlat (e u))
        hε_pos hpoint
    have hφcan :
        (∫ u : NPointDomain d (m + 1),
          canonicalReducedBranch (d := d) OS lgc m ε
              (BHW.reducedDiffMapReal (m + 1) d u) * φFlat (e u)) =
        ∫ u : NPointDomain d (m + 1),
          canonicalReducedBranch (d := d) OS lgc m ε
              (BHW.reducedDiffMapReal (m + 1) d u) * f u := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with u
      rw [hφeq u]
    have hcan_lift :
        (∫ u : NPointDomain d (m + 1),
          canonicalReducedBranch (d := d) OS lgc m ε
              (BHW.reducedDiffMapReal (m + 1) d u) * f u) =
        Target ε := by
      simpa [Target, f] using
        integral_reducedTestLift_eq_reduced
          (d := d) m χ ψ
          (canonicalReducedBranch (d := d) OS lgc m ε) hcanε
    have hzero :
        (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η)))) *
              φFlat (e u)) - Target ε = 0 := by
      calc
        (∫ u : NPointDomain d (m + 1),
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    ρperm sgn ε η
                    (e.symm (e u - (sgn * ε) • η)))) *
                φFlat (e u)) - Target ε =
            (∫ u : NPointDomain d (m + 1),
              canonicalReducedBranch (d := d) OS lgc m ε
                (BHW.reducedDiffMapReal (m + 1) d u) * φFlat (e u)) - Target ε := by
              rw [hbranch]
        _ = (∫ u : NPointDomain d (m + 1),
              canonicalReducedBranch (d := d) OS lgc m ε
                (BHW.reducedDiffMapReal (m + 1) d u) * f u) - Target ε := by
              rw [hφcan]
        _ = 0 := by
              rw [hcan_lift]
              ring
    exact hzero.symm
  have hsource_shifted :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η u)) *
              φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm u +
                (sgn * ε) • η)) -
          Target ε)
        l (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hsource_moving
    filter_upwards with ε
    have hreindex :=
      BHW.integral_sourceSide_shiftedTest_eq_movingSource_fixedTest
        (d := d) (n := m + 1) ρperm sgn ε η
        (fun x : BHW.OS45FlatCommonChartReal d (m + 1) => φFlat x)
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) σ.symm z))
    change
        ((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η)))) *
              φFlat (e u)) - Target ε) =
      ((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η u)) *
              φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm u +
                (sgn * ε) • η)) - Target ε)
    rw [hreindex]
  exact
    BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
      (d := d) (n := m + 1) OS lgc σ ρperm sgn η φFlat Target
      (by simpa [l, φFlat, e] using hflat_int)
      (by simpa [l, φFlat, e, Target] using hsource_shifted)

set_option maxHeartbeats 1200000 in
/-- Private lower endpoint companion to the diagnostic reindexed reducer above.

It records that a strong supportwise finite-height adjacent-permuted
reduced-coordinate hypothesis would imply the lower flat endpoint transport.
The active OS route keeps the genuine asymptotic source-side endpoint limit as
the remaining analytic leaf instead. -/
private theorem tendsto_flatCommonChart_branch_integral_sub_canonicalAfterReducedSwapBranch_reducedTestLift_of_reindexed_sourceSide_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ}
    (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (σ ρperm : Equiv.Perm (Fin (m + 1)))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hflat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ
              (fun j =>
                ((x + (sgn * ε) • η) j : ℂ) +
                  (((sgn * ε) • η) j : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
              (x + (sgn * ε) • η)))
    (htransport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u : NPointDomain d (m + 1),
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            let e : NPointDomain d (m + 1) ≃L[ℝ]
                BHW.OS45FlatCommonChartReal d (m + 1) :=
              BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm
            let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
              (sgn * ε) • η
            BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η (e.symm (e u - a))) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    ρperm sgn ε η (e.symm (e u - a)))) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ
            (fun a =>
              (x a : ℂ) + (((sgn * ε) • η) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ *
                ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let e : NPointDomain d (m + 1) ≃L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz ψ
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f
  let Gadj : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ
  let Target : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  have hφeq : ∀ u : NPointDomain d (m + 1), φFlat (e u) = f u := by
    intro u
    simp [φFlat, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hadj_int :
      ∀ᶠ (ε : ℝ) in l,
        MeasureTheory.Integrable
          (fun u : NPointDomain d (m + 1) =>
            Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u)
          MeasureTheory.volume := by
    simpa [l, f, Gadj] using
      bvt_F_reduced_permuted_integrable_eventually
        (d := d) OS lgc m i j f
  have hsource_moving :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η)))) *
              φFlat (e u)) - Target ε)
        l (nhds 0) := by
    refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) l (nhds 0))
    filter_upwards [self_mem_nhdsWithin, htransport, hadj_int] with ε hε_pos htrans hadjε
    have hpoint :
        ∀ u : NPointDomain d (m + 1),
          φFlat (e u) ≠ 0 →
            BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η))) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    ρperm sgn ε η
                    (e.symm (e u - (sgn * ε) • η)))) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I := by
      intro u hφ_ne
      have hf_ne : (f : NPointDomain d (m + 1) → ℂ) u ≠ 0 := by
        simpa [hφeq u] using hφ_ne
      simpa [e] using htrans u hf_ne
    have hbranch :=
      integral_extendF_bvt_F_eq_adjacentReducedPermutedBranch_of_support
        (d := d) OS lgc m i j Fred
        (fun u : NPointDomain d (m + 1) =>
          BHW.reducedDiffMapReal (m + 1) d u)
        (fun u : NPointDomain d (m + 1) =>
          BHW.permAct (d := d) σ.symm
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              ρperm sgn ε η
              (e.symm (e u - (sgn * ε) • η))))
        (fun u : NPointDomain d (m + 1) => φFlat (e u))
        hε_pos hpoint
    have hφadj :
        (∫ u : NPointDomain d (m + 1),
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * φFlat (e u)) =
        ∫ u : NPointDomain d (m + 1),
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with u
      rw [hφeq u]
    have hadj_lift :
        (∫ u : NPointDomain d (m + 1),
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u) =
        ∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ := by
      simpa [f] using
        integral_reducedTestLift_eq_reduced
          (d := d) m χ ψ (Gadj ε) hadjε
    have hadj_target :
        (∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ) = Target ε := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ξ
      simpa [Gadj, Target] using
        congrArg (fun z : ℂ => z * ψ ξ)
          (adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
            (d := d) OS lgc m i j ε ξ)
    have hzero :
        (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η)))) *
              φFlat (e u)) - Target ε = 0 := by
      calc
        (∫ u : NPointDomain d (m + 1),
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    ρperm sgn ε η
                    (e.symm (e u - (sgn * ε) • η)))) *
                φFlat (e u)) - Target ε =
            (∫ u : NPointDomain d (m + 1),
              Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) *
                φFlat (e u)) - Target ε := by
              simpa [Gadj] using
                congrArg (fun z : ℂ => z - Target ε) hbranch
        _ = (∫ u : NPointDomain d (m + 1),
              Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) * f u) -
              Target ε := by
              rw [hφadj]
        _ = (∫ ξ : NPointDomain d m, Gadj ε ξ * ψ ξ) - Target ε := by
              rw [hadj_lift]
        _ = 0 := by
              rw [hadj_target]
              ring
    exact hzero.symm
  have hsource_shifted :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η u)) *
              φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm u +
                (sgn * ε) • η)) -
          Target ε)
        l (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hsource_moving
    filter_upwards with ε
    have hreindex :=
      BHW.integral_sourceSide_shiftedTest_eq_movingSource_fixedTest
        (d := d) (n := m + 1) ρperm sgn ε η
        (fun x : BHW.OS45FlatCommonChartReal d (m + 1) => φFlat x)
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) σ.symm z))
    change
        ((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η
                  (e.symm (e u - (sgn * ε) • η)))) *
              φFlat (e u)) - Target ε) =
      ((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  ρperm sgn ε η u)) *
              φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1) ρperm u +
                (sgn * ε) • η)) - Target ε)
    rw [hreindex]
  exact
    BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
      (d := d) (n := m + 1) OS lgc σ ρperm sgn η φFlat Target
      (by simpa [l, φFlat, e] using hflat_int)
      (by simpa [l, φFlat, e, Target] using hsource_shifted)

/-- Hdiff-germ form of the integrated reduced branch-difference theorem using
the honest flat side-branch carrier.

The Hdiff/source-window theorem supplies the moving-source flat side-branch
limit.  The remaining assumptions are exactly the asymptotic endpoint
transport/reindexing facts identifying those flat side integrals with the
canonical reduced and adjacent-after-swap reduced branch integrals up to the
common-edge Jacobian.  This avoids asserting the false unshifted source-variable
PET coordinate normal form. -/
theorem tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_flat_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ θ : SchwartzNPoint d (m + 1),
        HasCompactSupport (θ : NPointDomain d (m + 1) → ℂ) →
        tsupport (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * θ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hKsrc_sub_U : Ksrc ⊆ U)
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηsrcC : ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 ηsrc u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηsrc u ∈ Ωminus)
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hplus_flat_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_flat_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                ψ ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            ψ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let J : ℂ := (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ)
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ : SchwartzNPoint d (m + 1))
  let A : ℝ → ℂ := fun ε =>
    ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
      BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (1 : Equiv.Perm (Fin (m + 1)))
        (fun a =>
          (x a : ℂ) + ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
        φFlat x
  let B : ℝ → ℂ := fun ε =>
    ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
      BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
        (fun a =>
          (x a : ℂ) + ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
        φFlat x
  let C : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let R : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  have hflat :
      Filter.Tendsto
        (fun ε : ℝ => A ε - B ε)
        l
        (nhds 0) := by
    simpa [l, φFlat, A, B] using
      tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_HdiffGerm
        (d := d) OS lgc D U hU_open hU_nonempty Ucx Hdiff
        hUcx_open hUcx_connected hwick_mem hcommon_mem hHdiff_holo
        hwick_pairing_zero hcommon_trace hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hKsrc_sub_U
        hUsrcP ηsrc hηsrcC h0_plus h0_minus χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU
  have hplusT :
      Filter.Tendsto
        (fun ε : ℝ => A ε - J * C ε)
        l
        (nhds 0) := by
    simpa [l, φFlat, J, A, C] using hplus_flat_transport
  have hminusT :
      Filter.Tendsto
        (fun ε : ℝ => B ε - J * R ε)
        l
        (nhds 0) := by
    simpa [l, φFlat, J, j, B, R] using hminus_flat_transport
  have hscaled_sub_after :
      Filter.Tendsto
        (fun ε : ℝ => J * (C ε - R ε))
        l
        (nhds 0) := by
    have hcomb :
        Filter.Tendsto
          (fun ε : ℝ =>
            ((A ε - B ε) - (A ε - J * C ε)) + (B ε - J * R ε))
          l
          (nhds 0) := by
      simpa using ((hflat.sub hplusT).add hminusT)
    refine Filter.Tendsto.congr' ?_ hcomb
    filter_upwards with ε
    ring
  have hJ_ne : J ≠ 0 := by
    dsimp [J]
    exact_mod_cast
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos (m + 1)))
  have hcanonical_sub_after :
      Filter.Tendsto
        (fun ε : ℝ => C ε - R ε)
        l
        (nhds 0) := by
    have hscaled_div :
        Filter.Tendsto
          (fun ε : ℝ => J⁻¹ * (J * (C ε - R ε)))
          l
          (nhds 0) := by
      exact
        (tendsto_const_nhds.mul hscaled_sub_after).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ hscaled_div
    filter_upwards with ε
    rw [← mul_assoc, inv_mul_cancel₀ hJ_ne, one_mul]
  have hneg :
      Filter.Tendsto
        (fun ε : ℝ => -(C ε - R ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [l] using hcanonical_sub_after.neg
  refine Filter.Tendsto.congr' ?_ hneg
  filter_upwards with ε
  simp only [j, C, R]
  ring

/-- Split upper/lower shifted source-side endpoint limits into the combined
transport hypothesis consumed by the integrated Hdiff handoff.

The analytic DCT/reindexing leaf can now land separately on the upper
source-side endpoint and the lower adjacent source-side endpoint; this theorem
only performs the final subtraction bookkeeping. -/
theorem sourceSide_shifted_reduced_transport_of_endpoint_transports
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hplus_endpoint :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (1 : Equiv.Perm (Fin (m + 1))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((1 : ℝ) * ε) • ηsrc))) -
            ∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_endpoint :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((-1 : ℝ) * ε) • ηsrc))) -
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                ψ ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (1 : Equiv.Perm (Fin (m + 1))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((1 : ℝ) * ε) • ηsrc))) -
          ∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((-1 : ℝ) * ε) • ηsrc))) -
          ((∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ) -
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                ψ ξ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ :
        SchwartzNPoint d (m + 1))
  let plusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((1 : ℝ) * ε) • ηsrc))
  let minusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((-1 : ℝ) * ε) • ηsrc))
  let canonicalTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let adjacentTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch
          (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
        ψ ξ
  have hplus :
      Filter.Tendsto
        (fun ε : ℝ => plusSource ε - canonicalTarget ε) l (nhds 0) := by
    simpa [l, plusSource, canonicalTarget, φFlat] using hplus_endpoint
  have hminus :
      Filter.Tendsto
        (fun ε : ℝ => minusSource ε - adjacentTarget ε) l (nhds 0) := by
    simpa [l, minusSource, adjacentTarget, φFlat] using hminus_endpoint
  have hsplit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (plusSource ε - canonicalTarget ε) -
            (minusSource ε - adjacentTarget ε))
        l (nhds 0) := by
    exact (hplus.sub hminus).mono_right (by simp)
  refine Filter.Tendsto.congr' ?_ hsplit
  filter_upwards with ε
  simp only [plusSource, minusSource, canonicalTarget, adjacentTarget, φFlat]
  ring

set_option maxHeartbeats 1200000 in
/-- Upper shifted source-side endpoint transport from pointwise source transfer
and a dominated-convergence packet.

This is the DCT/reindexing half of the upper endpoint leaf.  The hypotheses that
remain are the genuine analytic inputs: pointwise convergence of the moving
source-side branch to the canonical reduced branch on the reduced-test support,
plus a single integrable domination packet for that difference. -/
theorem sourceSide_shifted_upper_reduced_endpoint_of_pointwise_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ}
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (bound : NPointDomain d (m + 1) → ℝ)
    (hpointwise :
      ∀ u : NPointDomain d (m + 1),
        ((BHW.reducedTestLift m d χ.toSchwartz ψ :
            SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) u ≠ 0 →
          Filter.Tendsto
            (fun ε : ℝ =>
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (1 : Equiv.Perm (Fin (m + 1))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                    ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))).symm
                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1))) u -
                          ε • ηsrc)))) -
                canonicalReducedBranch (d := d) OS lgc m ε
                  (BHW.reducedDiffMapReal (m + 1) d u))
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
            (nhds 0))
    (hmeas :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AEStronglyMeasurable
          (fun u : NPointDomain d (m + 1) =>
            (BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (1 : Equiv.Perm (Fin (m + 1))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                    ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))).symm
                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1))) u -
                          ε • ηsrc)))) -
              canonicalReducedBranch (d := d) OS lgc m ε
                (BHW.reducedDiffMapReal (m + 1) d u)) *
              ((BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                  NPointDomain d (m + 1) → ℂ) u)
          volume)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ᵐ u : NPointDomain d (m + 1) ∂volume,
          ‖(BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (1 : Equiv.Perm (Fin (m + 1))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                    ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))).symm
                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1))) u -
                          ε • ηsrc)))) -
              canonicalReducedBranch (d := d) OS lgc m ε
                (BHW.reducedDiffMapReal (m + 1) d u)) *
              ((BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                  NPointDomain d (m + 1) → ℂ) u‖ ≤ bound u) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (1 : Equiv.Perm (Fin (m + 1))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u + ε • ηsrc)) -
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let e : NPointDomain d (m + 1) ≃L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz ψ
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f
  let sourceMoving : ℝ → NPointDomain d (m + 1) → ℂ := fun ε u =>
    BHW.extendF (bvt_F OS lgc (m + 1))
      (BHW.permAct (d := d)
        (1 : Equiv.Perm (Fin (m + 1))).symm
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
          (e.symm (e u - ε • ηsrc))))
  let canLift : ℝ → NPointDomain d (m + 1) → ℂ := fun ε u =>
    canonicalReducedBranch (d := d) OS lgc m ε
      (BHW.reducedDiffMapReal (m + 1) d u)
  let diff : ℝ → NPointDomain d (m + 1) → ℂ := fun ε u =>
    (sourceMoving ε u - canLift ε u) * (f : NPointDomain d (m + 1) → ℂ) u
  let Target : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  have hdiff_meas :
      ∀ᶠ ε : ℝ in l,
        AEStronglyMeasurable (diff ε) volume := by
    simpa [l, diff, sourceMoving, canLift, f, e] using hmeas
  have hdiff_bound :
      ∀ᶠ ε : ℝ in l,
        ∀ᵐ u : NPointDomain d (m + 1) ∂volume,
          ‖diff ε u‖ ≤ bound u := by
    simpa [l, diff, sourceMoving, canLift, f, e] using hbound
  have hdiff_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => ∫ u : NPointDomain d (m + 1), diff ε u)
        l (nhds 0) := by
    have hDCT :
        Filter.Tendsto
          (fun ε : ℝ => ∫ u : NPointDomain d (m + 1), diff ε u)
          l (nhds (∫ u : NPointDomain d (m + 1), (0 : ℂ))) := by
      exact
        MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          bound hdiff_meas hdiff_bound hbound_integrable
          (by
            refine Filter.Eventually.of_forall ?_
            intro u
            by_cases hfu :
                (f : NPointDomain d (m + 1) → ℂ) u = 0
            · simp [diff, hfu]
            · simpa [diff, sourceMoving, canLift, f, e, l] using
                (hpointwise u hfu).mul tendsto_const_nhds)
    simpa using hDCT
  have hcan_int :
      ∀ᶠ (ε : ℝ) in l,
        Integrable (fun u : NPointDomain d (m + 1) =>
          canLift ε u * (f : NPointDomain d (m + 1) → ℂ) u) volume := by
    simpa [l, canLift, f] using
      bvt_F_reduced_canonical_integrable_eventually
        (d := d) OS lgc m f
  have hdiff_int :
      ∀ᶠ (ε : ℝ) in l, Integrable (diff ε) volume := by
    filter_upwards [hdiff_meas, hdiff_bound] with ε hmeasε hboundε
    exact hbound_integrable.mono' hmeasε hboundε
  have hmoving :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) -
            Target ε)
        l (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hdiff_tendsto
    filter_upwards [hcan_int, hdiff_int] with ε hcanε hdiffε
    let sourceIntegrand : NPointDomain d (m + 1) → ℂ := fun u =>
      sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u
    let canIntegrand : NPointDomain d (m + 1) → ℂ := fun u =>
      canLift ε u * (f : NPointDomain d (m + 1) → ℂ) u
    have hsource_eq :
        sourceIntegrand = fun u =>
          diff ε u + canIntegrand u := by
      funext u
      simp [sourceIntegrand, diff]
      ring
    have hsource_int : Integrable sourceIntegrand volume := by
      rw [hsource_eq]
      exact hdiffε.add hcanε
    have hsplit :
        (∫ u : NPointDomain d (m + 1), sourceIntegrand u) -
            ∫ u : NPointDomain d (m + 1), canIntegrand u =
          ∫ u : NPointDomain d (m + 1), diff ε u := by
      rw [← MeasureTheory.integral_sub hsource_int hcanε]
      congr 1
      funext u
      simp [sourceIntegrand, diff]
      ring
    have hcan_lift :
        (∫ u : NPointDomain d (m + 1), canIntegrand u) =
          Target ε := by
      simpa [Target, canIntegrand, canLift, f] using
        integral_reducedTestLift_eq_reduced
          (d := d) m χ ψ
          (canonicalReducedBranch (d := d) OS lgc m ε) hcanε
    calc
      (∫ u : NPointDomain d (m + 1), diff ε u)
          = (∫ u : NPointDomain d (m + 1), sourceIntegrand u) -
              ∫ u : NPointDomain d (m + 1), canIntegrand u := hsplit.symm
      _ = (∫ u : NPointDomain d (m + 1),
            sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) -
            Target ε := by
              rw [hcan_lift]
  refine Filter.Tendsto.congr' ?_ hmoving
  filter_upwards with ε
  have hφeq : ∀ u : NPointDomain d (m + 1),
      φFlat (e u) = (f : NPointDomain d (m + 1) → ℂ) u := by
    intro u
    simp [φFlat, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hreindex :=
    BHW.integral_sourceSide_shiftedTest_eq_movingSource_fixedTest
      (d := d) (n := m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
      (fun x : BHW.OS45FlatCommonChartReal d (m + 1) => φFlat x)
      (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc (m + 1))
          (BHW.permAct (d := d)
            (1 : Equiv.Perm (Fin (m + 1))).symm z))
  change
      ((∫ u : NPointDomain d (m + 1),
          sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) -
        Target ε) =
      ((∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (1 : Equiv.Perm (Fin (m + 1))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u + ε • ηsrc)) -
        Target ε)
  have hmoving_eq :
      (∫ u : NPointDomain d (m + 1),
          sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) =
        ∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (1 : Equiv.Perm (Fin (m + 1))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm
                    (BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1))) u -
                      ε • ηsrc)))) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    simp [sourceMoving, e, hφeq u]
  have hshift_eq :
      (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (1 : Equiv.Perm (Fin (m + 1))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u + ε • ηsrc)) =
        (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (1 : Equiv.Perm (Fin (m + 1))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm
                    (BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1))) u -
                      ε • ηsrc)))) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    simpa [one_mul] using hreindex
  rw [hmoving_eq, hshift_eq]

set_option maxHeartbeats 1200000 in
/-- Lower shifted source-side endpoint transport from pointwise source transfer
and a dominated-convergence packet.

This is the adjacent lower companion to
`sourceSide_shifted_upper_reduced_endpoint_of_pointwise_bound`: it performs the
DCT/reindexing passage from the moving source-side branch to the
canonical-after-swap reduced endpoint, leaving the pointwise OS transfer and the
domination packet as the visible analytic inputs. -/
theorem sourceSide_shifted_lower_reduced_endpoint_of_pointwise_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (bound : NPointDomain d (m + 1) → ℝ)
    (hpointwise :
      ∀ u : NPointDomain d (m + 1),
        ((BHW.reducedTestLift m d χ.toSchwartz ψ :
            SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) u ≠ 0 →
          Filter.Tendsto
            (fun ε : ℝ =>
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                    ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))).symm
                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1))) u -
                          (((-1 : ℝ) * ε) • ηsrc))))) -
                canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε
                  (BHW.reducedDiffMapReal (m + 1) d u))
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
            (nhds 0))
    (hmeas :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AEStronglyMeasurable
          (fun u : NPointDomain d (m + 1) =>
            (BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                    ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))).symm
                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1))) u -
                          (((-1 : ℝ) * ε) • ηsrc))))) -
              canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε
                (BHW.reducedDiffMapReal (m + 1) d u)) *
              ((BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                  NPointDomain d (m + 1) → ℂ) u)
          volume)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ᵐ u : NPointDomain d (m + 1) ∂volume,
          ‖(BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                    ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))).symm
                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1))) u -
                          (((-1 : ℝ) * ε) • ηsrc))))) -
              canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε
                (BHW.reducedDiffMapReal (m + 1) d u)) *
              ((BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                  NPointDomain d (m + 1) → ℂ) u‖ ≤ bound u) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u +
                  (((-1 : ℝ) * ε) • ηsrc))) -
          ∫ ξ : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
              ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let e : NPointDomain d (m + 1) ≃L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz ψ
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f
  let sourceMoving : ℝ → NPointDomain d (m + 1) → ℂ := fun ε u =>
    BHW.extendF (bvt_F OS lgc (m + 1))
      (BHW.permAct (d := d)
        (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
          (e.symm (e u - (((-1 : ℝ) * ε) • ηsrc)))))
  let canLift : ℝ → NPointDomain d (m + 1) → ℂ := fun ε u =>
    canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε
      (BHW.reducedDiffMapReal (m + 1) d u)
  let diff : ℝ → NPointDomain d (m + 1) → ℂ := fun ε u =>
    (sourceMoving ε u - canLift ε u) * (f : NPointDomain d (m + 1) → ℂ) u
  let Target : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  have hdiff_meas :
      ∀ᶠ ε : ℝ in l,
        AEStronglyMeasurable (diff ε) volume := by
    simpa [l, diff, sourceMoving, canLift, f, e, j] using hmeas
  have hdiff_bound :
      ∀ᶠ ε : ℝ in l,
        ∀ᵐ u : NPointDomain d (m + 1) ∂volume,
          ‖diff ε u‖ ≤ bound u := by
    simpa [l, diff, sourceMoving, canLift, f, e, j] using hbound
  have hdiff_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => ∫ u : NPointDomain d (m + 1), diff ε u)
        l (nhds 0) := by
    have hDCT :
        Filter.Tendsto
          (fun ε : ℝ => ∫ u : NPointDomain d (m + 1), diff ε u)
          l (nhds (∫ u : NPointDomain d (m + 1), (0 : ℂ))) := by
      exact
        MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          bound hdiff_meas hdiff_bound hbound_integrable
          (by
            refine Filter.Eventually.of_forall ?_
            intro u
            by_cases hfu :
                (f : NPointDomain d (m + 1) → ℂ) u = 0
            · simp [diff, hfu]
            · simpa [diff, sourceMoving, canLift, f, e, j, l] using
                (hpointwise u hfu).mul tendsto_const_nhds)
    simpa using hDCT
  let Gadj : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ
  have hadj_int :
      ∀ᶠ (ε : ℝ) in l,
        Integrable (fun u : NPointDomain d (m + 1) =>
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) *
            (f : NPointDomain d (m + 1) → ℂ) u) volume := by
    simpa [l, Gadj, f] using
      bvt_F_reduced_permuted_integrable_eventually
        (d := d) OS lgc m i j f
  have hcan_int :
      ∀ᶠ (ε : ℝ) in l,
        Integrable (fun u : NPointDomain d (m + 1) =>
          canLift ε u * (f : NPointDomain d (m + 1) → ℂ) u) volume := by
    filter_upwards [hadj_int] with ε hadjε
    have heq :
        (fun u : NPointDomain d (m + 1) =>
          canLift ε u * (f : NPointDomain d (m + 1) → ℂ) u) =
        fun u : NPointDomain d (m + 1) =>
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) *
            (f : NPointDomain d (m + 1) → ℂ) u := by
      funext u
      rw [show canLift ε u =
          Gadj ε (BHW.reducedDiffMapReal (m + 1) d u) by
        simpa [canLift, Gadj, j] using
          (adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
            (d := d) OS lgc m i j ε
            (BHW.reducedDiffMapReal (m + 1) d u)).symm]
    rw [heq]
    exact hadjε
  have hdiff_int :
      ∀ᶠ (ε : ℝ) in l, Integrable (diff ε) volume := by
    filter_upwards [hdiff_meas, hdiff_bound] with ε hmeasε hboundε
    exact hbound_integrable.mono' hmeasε hboundε
  have hmoving :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d (m + 1),
            sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) -
            Target ε)
        l (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hdiff_tendsto
    filter_upwards [hcan_int, hdiff_int] with ε hcanε hdiffε
    let sourceIntegrand : NPointDomain d (m + 1) → ℂ := fun u =>
      sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u
    let canIntegrand : NPointDomain d (m + 1) → ℂ := fun u =>
      canLift ε u * (f : NPointDomain d (m + 1) → ℂ) u
    have hsource_eq :
        sourceIntegrand = fun u =>
          diff ε u + canIntegrand u := by
      funext u
      simp [sourceIntegrand, canIntegrand, diff]
      ring
    have hsource_int : Integrable sourceIntegrand volume := by
      rw [hsource_eq]
      exact hdiffε.add hcanε
    have hsplit :
        (∫ u : NPointDomain d (m + 1), sourceIntegrand u) -
            ∫ u : NPointDomain d (m + 1), canIntegrand u =
          ∫ u : NPointDomain d (m + 1), diff ε u := by
      rw [← MeasureTheory.integral_sub hsource_int hcanε]
      congr 1
      funext u
      simp [sourceIntegrand, diff]
      ring
    have hcan_lift :
        (∫ u : NPointDomain d (m + 1), canIntegrand u) =
          Target ε := by
      simpa [Target, canIntegrand, canLift, f, j] using
        integral_reducedTestLift_eq_reduced
          (d := d) m χ ψ
          (canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε) hcanε
    calc
      (∫ u : NPointDomain d (m + 1), diff ε u)
          = (∫ u : NPointDomain d (m + 1), sourceIntegrand u) -
              ∫ u : NPointDomain d (m + 1), canIntegrand u := hsplit.symm
      _ = (∫ u : NPointDomain d (m + 1),
            sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) -
            Target ε := by
              rw [hcan_lift]
  refine Filter.Tendsto.congr' ?_ hmoving
  filter_upwards with ε
  have hφeq : ∀ u : NPointDomain d (m + 1),
      φFlat (e u) = (f : NPointDomain d (m + 1) → ℂ) u := by
    intro u
    simp [φFlat, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hreindex :=
    BHW.integral_sourceSide_shiftedTest_eq_movingSource_fixedTest
      (d := d) (n := m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
      (fun x : BHW.OS45FlatCommonChartReal d (m + 1) => φFlat x)
      (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc (m + 1))
          (BHW.permAct (d := d)
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
  change
      ((∫ u : NPointDomain d (m + 1),
          sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) -
        Target ε) =
      ((∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u +
                (((-1 : ℝ) * ε) • ηsrc))) -
        Target ε)
  have hmoving_eq :
      (∫ u : NPointDomain d (m + 1),
          sourceMoving ε u * (f : NPointDomain d (m + 1) → ℂ) u) =
        (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm
                    (BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1))) u -
                      (((-1 : ℝ) * ε) • ηsrc))))) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    simp [sourceMoving, e, hφeq u]
  have hshift_eq :
      (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u +
                (((-1 : ℝ) * ε) • ηsrc))) =
        (∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm
                    (BHW.os45CommonEdgeFlatCLE d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1))) u -
                      (((-1 : ℝ) * ε) • ηsrc))))) *
            φFlat (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    exact hreindex
  rw [hmoving_eq, hshift_eq]

/-- Hdiff-germ form of the integrated reduced branch-difference theorem using
shifted source-side endpoint transport.

The coordinate/Jacobian layer is supplied by
`BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift`.
The flat integrability needed for that change of variables is discharged from
compact reduced-lift support and the Figure-2-4 local wedge; the remaining
source-side hypothesis is the single combined analytic endpoint comparison
between the shifted source difference and the reduced canonical difference. -/
theorem tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_sourceSide_shifted_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ θ : SchwartzNPoint d (m + 1),
        HasCompactSupport (θ : NPointDomain d (m + 1) → ℂ) →
        tsupport (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * θ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hKsrc_sub_U : Ksrc ⊆ U)
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηsrcC : ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 ηsrc u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηsrc u ∈ Ωminus)
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hsource_reduced_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
          (((∫ u : NPointDomain d (m + 1),
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (1 : Equiv.Perm (Fin (m + 1))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
                ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm)
                  (BHW.reducedTestLift m d χ.toSchwartz ψ :
                    SchwartzNPoint d (m + 1)) :
                  SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) u +
                      (((1 : ℝ) * ε) • ηsrc))) -
            ∫ u : NPointDomain d (m + 1),
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
                ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm)
                  (BHW.reducedTestLift m d χ.toSchwartz ψ :
                    SchwartzNPoint d (m + 1)) :
                  SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) u +
                      (((-1 : ℝ) * ε) • ηsrc))) -
            ((∫ ξ : NPointDomain d m,
                canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ) -
              ∫ ξ : NPointDomain d m,
                canonicalAfterReducedSwapBranch
                    (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                  ψ ξ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            ψ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ : SchwartzNPoint d (m + 1))
  let plusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let minusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  let plusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((1 : ℝ) * ε) • ηsrc))
  let minusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((-1 : ℝ) * ε) • ηsrc))
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU hUsrcP
  let Kη : Set (BHW.OS45FlatCommonChartReal d (m + 1)) := {ηsrc}
  have hKη : IsCompact Kη := isCompact_singleton
  have hKηC :
      Kη ⊆ BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    have hη_eq : η = ηsrc := by
      simpa [Kη] using hη
    simpa [hη_eq] using hηsrcC
  have hflat_int_both :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ∀ η ∈ Kη,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (fun j =>
                ((x + ε • η) j : ℂ) + ((ε • η) j : ℂ) * Complex.I) *
            φFlat (x + ε • η)) ∧
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (fun j =>
                ((x + (-ε : ℝ) • η) j : ℂ) +
                  (((-ε : ℝ) • η) j : ℂ) * Complex.I) *
            φFlat (x + (-ε : ℝ) • η)) := by
    simpa [Kη] using
      BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
        (d := d) (n := m + 1) OS lgc (P := P)
        Kη hKη hKηC φFlat hsupport.1 hsupport.2.1
  have hplus_flat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (fun a =>
                ((x + (((1 : ℝ) * ε) • ηsrc)) a : ℂ) +
                  (((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I)) *
              φFlat (x + (((1 : ℝ) * ε) • ηsrc))) := by
    filter_upwards [hflat_int_both] with ε hε
    simpa [Kη, one_mul] using (hε ηsrc (by simp [Kη])).1
  have hminus_flat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (fun a =>
                ((x + (((-1 : ℝ) * ε) • ηsrc)) a : ℂ) +
                  (((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I)) *
              φFlat (x + (((-1 : ℝ) * ε) • ηsrc))) := by
    filter_upwards [hflat_int_both] with ε hε
    simpa [Kη, neg_mul] using (hε ηsrc (by simp [Kη])).2
  have hplus_source_self :
      Filter.Tendsto
        (fun ε : ℝ => plusSource ε - plusSource ε)
        l
        (nhds 0) := by
    simp
  have hminus_source_self :
      Filter.Tendsto
        (fun ε : ℝ => minusSource ε - minusSource ε)
        l
        (nhds 0) := by
    simp
  have hplus_flat_source :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            φFlat x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            plusSource ε)
        l
        (nhds 0) := by
    simpa [l, φFlat, plusSource] using
      BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
        (d := d) (n := m + 1) OS lgc
        (σ := (1 : Equiv.Perm (Fin (m + 1))))
        (ρperm := (1 : Equiv.Perm (Fin (m + 1))))
        (sgn := (1 : ℝ)) (η := ηsrc) (φ := φFlat)
        (Target := plusSource) hplus_flat_int hplus_source_self
  have hminus_flat_source :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            φFlat x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            minusSource ε)
        l
        (nhds 0) := by
    simpa [l, φFlat, minusSource, j] using
      BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
        (d := d) (n := m + 1) OS lgc
        (σ := (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))))
        (ρperm := (1 : Equiv.Perm (Fin (m + 1))))
        (sgn := (-1 : ℝ)) (η := ηsrc) (φ := φFlat)
        (Target := minusSource) hminus_flat_int hminus_source_self
  have hflat_diff :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            φFlat x) -
        ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            φFlat x)
        l
        (nhds 0) := by
    simpa [l, φFlat] using
      tendsto_flatCommonChart_sideBranch_difference_zero_reducedTestLift_of_HdiffGerm
        (d := d) OS lgc D U hU_open hU_nonempty Ucx Hdiff
        hUcx_open hUcx_connected hwick_mem hcommon_mem hHdiff_holo
        hwick_pairing_zero hcommon_trace hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hKsrc_sub_U
        hUsrcP ηsrc hηsrcC h0_plus h0_minus χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU
  let J : ℂ := (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ)
  have hscaled_source :
      Filter.Tendsto
        (fun ε : ℝ => J * (plusSource ε - minusSource ε))
        l
        (nhds 0) := by
    have hcombo := (hflat_diff.sub hplus_flat_source).add hminus_flat_source
    have hscaled_raw :
        Filter.Tendsto
          (fun ε : ℝ => J * (plusSource ε - minusSource ε))
          l
          (nhds (0 - 0 + 0 : ℂ)) := by
      refine Filter.Tendsto.congr' ?_ hcombo
      filter_upwards with ε
      simp only [J]
      ring
    simpa using hscaled_raw
  have hJ_ne : J ≠ 0 := by
    dsimp [J]
    exact_mod_cast
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos (m + 1)))
  have hsource_diff_zero :
      Filter.Tendsto
        (fun ε : ℝ => plusSource ε - minusSource ε)
        l
        (nhds 0) := by
    have hscaled_div :
        Filter.Tendsto
          (fun ε : ℝ => J⁻¹ * (J * (plusSource ε - minusSource ε)))
          l
          (nhds 0) := by
      exact
        (tendsto_const_nhds.mul hscaled_source).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ hscaled_div
    filter_upwards with ε
    rw [← mul_assoc, inv_mul_cancel₀ hJ_ne, one_mul]
  have htransport :
      Filter.Tendsto
        (fun ε : ℝ =>
          (plusSource ε - minusSource ε) -
            (plusTarget ε - minusTarget ε))
        l
        (nhds 0) := by
    simpa [l, φFlat, plusSource, minusSource, plusTarget, minusTarget, j] using
      hsource_reduced_transport
  have hcanonical_sub_after :
      Filter.Tendsto
        (fun ε : ℝ => plusTarget ε - minusTarget ε)
        l
        (nhds 0) := by
    have h := hsource_diff_zero.sub htransport
    have h0 :
        Filter.Tendsto
          (fun ε : ℝ =>
            (plusSource ε - minusSource ε) -
              ((plusSource ε - minusSource ε) -
                (plusTarget ε - minusTarget ε)))
          l
          (nhds 0) := by
      simpa using h
    refine Filter.Tendsto.congr' ?_ h0
    filter_upwards with ε
    ring
  have hneg :
      Filter.Tendsto
        (fun ε : ℝ => -(plusTarget ε - minusTarget ε))
        l
        (nhds 0) := by
    simpa using hcanonical_sub_after.neg
  refine Filter.Tendsto.congr' ?_ hneg
  filter_upwards with ε
  simp only [plusTarget, minusTarget, j]
  ring

/-- The two flat endpoint transport limits imply the single combined shifted
source-side reduced endpoint comparison.

This is the algebraic/Jacobian bridge between the older flat endpoint surface
and the direct source-side endpoint leaf used by the corrected Path-2 consumer.
It uses the existing shifted-test change of variables for each side; the
remaining analytic content is still the two flat-to-reduced endpoint transports
given as hypotheses. -/
theorem tendsto_sourceSide_shifted_reduced_transport_of_flat_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {Usrc : Set (NPointDomain d (m + 1))}
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηsrcC : ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hplus_flat_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_flat_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                ψ ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (1 : Equiv.Perm (Fin (m + 1))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((1 : ℝ) * ε) • ηsrc))) -
          ∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((-1 : ℝ) * ε) • ηsrc))) -
          ((∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ) -
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                ψ ξ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let J : ℂ := (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ)
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ : SchwartzNPoint d (m + 1))
  let plusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let minusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  let plusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((1 : ℝ) * ε) • ηsrc))
  let minusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((-1 : ℝ) * ε) • ηsrc))
  let plusFlat : ℝ → ℂ := fun ε =>
    ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
      BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (1 : Equiv.Perm (Fin (m + 1)))
        (fun a =>
          (x a : ℂ) + ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
        φFlat x
  let minusFlat : ℝ → ℂ := fun ε =>
    ∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
      BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
        (fun a =>
          (x a : ℂ) + ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
        φFlat x
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU hUsrcP
  let Kη : Set (BHW.OS45FlatCommonChartReal d (m + 1)) := {ηsrc}
  have hKη : IsCompact Kη := isCompact_singleton
  have hKηC :
      Kη ⊆ BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    have hη_eq : η = ηsrc := by
      simpa [Kη] using hη
    simpa [hη_eq] using hηsrcC
  have hflat_int_both :
      ∀ᶠ ε in l, ∀ η ∈ Kη,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (fun j =>
                ((x + ε • η) j : ℂ) + ((ε • η) j : ℂ) * Complex.I) *
            φFlat (x + ε • η)) ∧
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (fun j =>
                ((x + (-ε : ℝ) • η) j : ℂ) +
                  (((-ε : ℝ) • η) j : ℂ) * Complex.I) *
            φFlat (x + (-ε : ℝ) • η)) := by
    simpa [l, Kη] using
      BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
        (d := d) (n := m + 1) OS lgc (P := P)
        Kη hKη hKηC φFlat hsupport.1 hsupport.2.1
  have hplus_flat_int :
      ∀ᶠ ε : ℝ in l,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (fun a =>
                ((x + (((1 : ℝ) * ε) • ηsrc)) a : ℂ) +
                  (((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I)) *
              φFlat (x + (((1 : ℝ) * ε) • ηsrc))) := by
    filter_upwards [hflat_int_both] with ε hε
    simpa [Kη, one_mul] using (hε ηsrc (by simp [Kη])).1
  have hminus_flat_int :
      ∀ᶠ ε : ℝ in l,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (fun a =>
                ((x + (((-1 : ℝ) * ε) • ηsrc)) a : ℂ) +
                  (((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I)) *
              φFlat (x + (((-1 : ℝ) * ε) • ηsrc))) := by
    filter_upwards [hflat_int_both] with ε hε
    simpa [Kη, neg_mul] using (hε ηsrc (by simp [Kη])).2
  have hplus_source_self :
      Filter.Tendsto
        (fun ε : ℝ => plusSource ε - plusSource ε)
        l
        (nhds 0) := by
    simp
  have hminus_source_self :
      Filter.Tendsto
        (fun ε : ℝ => minusSource ε - minusSource ε)
        l
        (nhds 0) := by
    simp
  have hplus_flat_source :
      Filter.Tendsto
        (fun ε : ℝ => plusFlat ε - J * plusSource ε)
        l
        (nhds 0) := by
    simpa [l, J, φFlat, plusFlat, plusSource] using
      BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
        (d := d) (n := m + 1) OS lgc
        (σ := (1 : Equiv.Perm (Fin (m + 1))))
        (ρperm := (1 : Equiv.Perm (Fin (m + 1))))
        (sgn := (1 : ℝ)) (η := ηsrc) (φ := φFlat)
        (Target := plusSource) hplus_flat_int hplus_source_self
  have hminus_flat_source :
      Filter.Tendsto
        (fun ε : ℝ => minusFlat ε - J * minusSource ε)
        l
        (nhds 0) := by
    simpa [l, J, φFlat, minusFlat, minusSource, j] using
      BHW.tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
        (d := d) (n := m + 1) OS lgc
        (σ := (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))))
        (ρperm := (1 : Equiv.Perm (Fin (m + 1))))
        (sgn := (-1 : ℝ)) (η := ηsrc) (φ := φFlat)
        (Target := minusSource) hminus_flat_int hminus_source_self
  have hplusT :
      Filter.Tendsto
        (fun ε : ℝ => plusFlat ε - J * plusTarget ε)
        l
        (nhds 0) := by
    simpa [l, J, φFlat, plusFlat, plusTarget] using hplus_flat_transport
  have hminusT :
      Filter.Tendsto
        (fun ε : ℝ => minusFlat ε - J * minusTarget ε)
        l
        (nhds 0) := by
    simpa [l, J, φFlat, minusFlat, minusTarget, j] using
      hminus_flat_transport
  have hJ_ne : J ≠ 0 := by
    dsimp [J]
    exact_mod_cast
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos (m + 1)))
  have hplus_scaled :
      Filter.Tendsto
        (fun ε : ℝ => J * (plusSource ε - plusTarget ε))
        l
        (nhds 0) := by
    have hcombo :
        Filter.Tendsto
          (fun ε : ℝ =>
            (plusFlat ε - J * plusTarget ε) -
              (plusFlat ε - J * plusSource ε))
          l
          (nhds 0) := by
      exact (hplusT.sub hplus_flat_source).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ hcombo
    filter_upwards with ε
    ring
  have hminus_scaled :
      Filter.Tendsto
        (fun ε : ℝ => J * (minusSource ε - minusTarget ε))
        l
        (nhds 0) := by
    have hcombo :
        Filter.Tendsto
          (fun ε : ℝ =>
            (minusFlat ε - J * minusTarget ε) -
              (minusFlat ε - J * minusSource ε))
          l
          (nhds 0) := by
      exact (hminusT.sub hminus_flat_source).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ hcombo
    filter_upwards with ε
    ring
  have hplus_source_target :
      Filter.Tendsto
        (fun ε : ℝ => plusSource ε - plusTarget ε)
        l
        (nhds 0) := by
    have hscaled_div :
        Filter.Tendsto
          (fun ε : ℝ => J⁻¹ * (J * (plusSource ε - plusTarget ε)))
          l
          (nhds 0) := by
      exact
        (tendsto_const_nhds.mul hplus_scaled).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ hscaled_div
    filter_upwards with ε
    rw [← mul_assoc, inv_mul_cancel₀ hJ_ne, one_mul]
  have hminus_source_target :
      Filter.Tendsto
        (fun ε : ℝ => minusSource ε - minusTarget ε)
        l
        (nhds 0) := by
    have hscaled_div :
        Filter.Tendsto
          (fun ε : ℝ => J⁻¹ * (J * (minusSource ε - minusTarget ε)))
          l
          (nhds 0) := by
      exact
        (tendsto_const_nhds.mul hminus_scaled).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ hscaled_div
    filter_upwards with ε
    rw [← mul_assoc, inv_mul_cancel₀ hJ_ne, one_mul]
  have hcombined :
      Filter.Tendsto
        (fun ε : ℝ =>
          (plusSource ε - minusSource ε) -
            (plusTarget ε - minusTarget ε))
        l
        (nhds 0) := by
    have h :
        Filter.Tendsto
          (fun ε : ℝ =>
            (plusSource ε - plusTarget ε) -
              (minusSource ε - minusTarget ε))
          l
          (nhds 0) := by
      exact (hplus_source_target.sub hminus_source_target).mono_right (by simp)
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with ε
    ring
  simpa [l, φFlat, plusSource, minusSource, plusTarget, minusTarget, j] using
    hcombined

/-- Figure-2-4 side-zero source endpoint transport for the reduced test lift.

This is the same finite-height source-to-reduced endpoint comparison as the
shifted flat-pullback statement, but expressed against the actual signed
side-zero source tests.  The cutoff-removal bridge below converts it to the
cutoff-free translated flat-pullback form. -/
def sourceSideSideZeroReducedEndpointTransport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m) : Prop :=
  Filter.Tendsto
    (fun ε : ℝ =>
      (((∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (1 : Equiv.Perm (Fin (m + 1))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)).1 :
                SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)) -
        ∫ u : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)).1 :
                SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)) -
        ((∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ) -
          ∫ ξ : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
              ψ ξ)))
    (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
    (nhds 0)

/-- Source-representation and finite-height reduced transport imply the
side-zero endpoint transport used by the shifted flat-pullback handoff.

The source-representation theorem supplies the zero limit for the signed
side-zero source pair itself, while the older reduced-branch transport theorem
supplies the zero limit for `canonicalAfter - canonicalReduced`.  Subtracting
the negated latter limit closes the combined endpoint Prop without hiding the
remaining finite-height transport hypotheses. -/
theorem sourceSideSideZeroReducedEndpointTransport_of_sourceRepresentsOn_and_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 ηsrc u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηsrc u ∈ Ωminus)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) Usrc)
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hplus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)
    (hminus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u,
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) :
    sourceSideSideZeroReducedEndpointTransport
      (d := d) OS lgc D ηsrc χ ψ := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ :
        SchwartzNPoint d (m + 1))
  let plusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
      ((((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc φFlat).1 :
          SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)
  let minusSource : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
      ((((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc φFlat).1 :
          SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)
  let reducedTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let afterTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU hUsrcP
  have hsource_zero :
      Filter.Tendsto
        (fun ε : ℝ => plusSource ε - minusSource ε) l
        (nhds 0) := by
    simpa [l, φFlat, plusSource, minusSource] using
      D.tendsto_sourceSide_extendF_difference_zero_of_sourceRepresentsOn
        (d := d) OS lgc hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc ηsrc
        h0_plus h0_minus hrep φFlat hsupport.1 hsupport.2.2
  have hafter_sub_reduced :
      Filter.Tendsto
        (fun ε : ℝ => afterTarget ε - reducedTarget ε) l
        (nhds 0) := by
    simpa [l, reducedTarget, afterTarget, j] using
      tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_sourceRepresentsOn_and_transport
        (d := d) OS lgc D Fred hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hUsrcP
        ηsrc h0_plus h0_minus hrep χ ψ hχ_compact hψ_compact hliftU
        hplus_transport hminus_transport
  have hreduced_sub_after :
      Filter.Tendsto
        (fun ε : ℝ => reducedTarget ε - afterTarget ε) l
        (nhds 0) := by
    have hneg :
        Filter.Tendsto
          (fun ε : ℝ => -(afterTarget ε - reducedTarget ε)) l
          (nhds 0) := by
      simpa using hafter_sub_reduced.neg
    refine Filter.Tendsto.congr' ?_ hneg
    filter_upwards with ε
    ring
  have hcombo := hsource_zero.sub hreduced_sub_after
  simpa [sourceSideSideZeroReducedEndpointTransport, l, φFlat, plusSource,
    minusSource, reducedTarget, afterTarget, j] using hcombo

/-- Cutoff-removal bridge from the Figure-2-4 side-zero endpoint transport to
the shifted flat-pullback endpoint transport consumed by the Hdiff handoff.

For sufficiently small positive side-height, the reduced-lift flat pullback is
supported in the Figure-2-4 edge and `D.toSideZeroDiagonalCLM` is pointwise the
same as evaluating the flat test at the shifted common-edge coordinate. -/
theorem sourceSide_shifted_transport_of_sideZeroReducedEndpointTransport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Usrc : Set (NPointDomain d (m + 1))}
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηsrcC : ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hsideZero :
      sourceSideSideZeroReducedEndpointTransport
        (d := d) OS lgc D ηsrc χ ψ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (((∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (1 : Equiv.Perm (Fin (m + 1))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((1 : ℝ) * ε) • ηsrc))) -
          ∫ u : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u +
                    (((-1 : ℝ) * ε) • ηsrc))) -
          ((∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ) -
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                ψ ξ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ : SchwartzNPoint d (m + 1))
  let plusRaw : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((1 : ℝ) * ε) • ηsrc))
  let minusRaw : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((-1 : ℝ) * ε) • ηsrc))
  let plusSide : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc φFlat).1 :
            SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)
  let minusSide : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc φFlat).1 :
            SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)
  let plusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let minusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU hUsrcP
  let Kη : Set (BHW.OS45FlatCommonChartReal d (m + 1)) := {ηsrc}
  have hKη : IsCompact Kη := isCompact_singleton
  have hKηC :
      Kη ⊆ BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    have hη_eq : η = ηsrc := by
      simpa [Kη] using hη
    simpa [hη_eq] using hηsrcC
  have hplain :=
    D.toSideZeroDiagonalCLM_eq_plain_eventually
      Kη hKη hKηC φFlat hsupport.1 hsupport.2.1
  have hside :
      Filter.Tendsto
        (fun ε : ℝ =>
          (plusSide ε - minusSide ε) - (plusTarget ε - minusTarget ε))
        l
        (nhds 0) := by
    simpa [sourceSideSideZeroReducedEndpointTransport, l, φFlat, plusSide,
      minusSide, plusTarget, minusTarget, j] using hsideZero
  refine Filter.Tendsto.congr' ?_ hside
  filter_upwards [hplain] with ε hε
  have hεη := hε ηsrc (by simp [Kη])
  have hplus_int : plusRaw ε = plusSide ε := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro u
    have hpoint :
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc φFlat).1 :
            SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) u) =
          φFlat
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u +
                (((1 : ℝ) * ε) • ηsrc)) := by
      simpa [one_mul] using (hεη u).1
    dsimp [plusRaw, plusSide]
    rw [← hpoint]
  have hminus_int : minusRaw ε = minusSide ε := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro u
    have hpoint :
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc φFlat).1 :
            SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) u) =
          φFlat
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u +
                (((-1 : ℝ) * ε) • ηsrc)) := by
      simpa [sub_eq_add_neg, neg_smul, neg_mul] using (hεη u).2
    dsimp [minusRaw, minusSide]
    rw [← hpoint]
  change
    (plusSide ε - minusSide ε) - (plusTarget ε - minusTarget ε) =
      (plusRaw ε - minusRaw ε) - (plusTarget ε - minusTarget ε)
  rw [← hplus_int, ← hminus_int]

/-- Shifted flat-pullback endpoint transport implies the Figure-2-4 side-zero
endpoint Prop.

This is the reverse cutoff-removal direction to
`sourceSide_shifted_transport_of_sideZeroReducedEndpointTransport`.  It lets
the local theorem-2 surface use the honest shifted source-side DCT/reindexing
comparison while still satisfying older consumers phrased with
`sourceSideSideZeroReducedEndpointTransport`. -/
theorem sourceSideSideZeroReducedEndpointTransport_of_sourceSide_shifted_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Usrc : Set (NPointDomain d (m + 1))}
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηsrcC : ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hshifted :
      Filter.Tendsto
        (fun ε : ℝ =>
          (((∫ u : NPointDomain d (m + 1),
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (1 : Equiv.Perm (Fin (m + 1))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
                ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm)
                  (BHW.reducedTestLift m d χ.toSchwartz ψ :
                    SchwartzNPoint d (m + 1)) :
                  SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) u +
                      (((1 : ℝ) * ε) • ηsrc))) -
            ∫ u : NPointDomain d (m + 1),
              BHW.extendF (bvt_F OS lgc (m + 1))
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
                ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm)
                  (BHW.reducedTestLift m d χ.toSchwartz ψ :
                    SchwartzNPoint d (m + 1)) :
                  SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) u +
                      (((-1 : ℝ) * ε) • ηsrc))) -
            ((∫ ξ : NPointDomain d m,
                canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ) -
              ∫ ξ : NPointDomain d m,
                canonicalAfterReducedSwapBranch
                    (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
                  ψ ξ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    sourceSideSideZeroReducedEndpointTransport
      (d := d) OS lgc D ηsrc χ ψ := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let φFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm)
      (BHW.reducedTestLift m d χ.toSchwartz ψ :
        SchwartzNPoint d (m + 1))
  let plusRaw : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((1 : ℝ) * ε) • ηsrc))
  let minusRaw : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        φFlat
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u +
              (((-1 : ℝ) * ε) • ηsrc))
  let plusSide : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (1 : Equiv.Perm (Fin (m + 1))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc u)) *
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc φFlat).1 :
            SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)
  let minusSide : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d (m + 1),
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc u)) *
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc φFlat).1 :
            SchwartzNPoint d (m + 1)) : NPointDomain d (m + 1) → ℂ) u)
  let plusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ
  let minusTarget : ℝ → ℂ := fun ε =>
    ∫ ξ : NPointDomain d m,
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * ψ ξ
  have hsupport :
      HasCompactSupport
          (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P
            (1 : Equiv.Perm (Fin (m + 1))) ∧
        tsupport
            (φFlat : BHW.OS45FlatCommonChartReal d (m + 1) → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' Usrc := by
    simpa [φFlat] using
      flatCommonChartPullback_reducedTestLift_sourceSideSupport
        (d := d) (m := m) (hd := hd) (i := i) (hi := hi) P
        (1 : Equiv.Perm (Fin (m + 1))) χ.toSchwartz ψ
        hχ_compact hψ_compact hliftU hUsrcP
  let Kη : Set (BHW.OS45FlatCommonChartReal d (m + 1)) := {ηsrc}
  have hKη : IsCompact Kη := isCompact_singleton
  have hKηC :
      Kη ⊆ BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    have hη_eq : η = ηsrc := by
      simpa [Kη] using hη
    simpa [hη_eq] using hηsrcC
  have hplain :=
    D.toSideZeroDiagonalCLM_eq_plain_eventually
      Kη hKη hKηC φFlat hsupport.1 hsupport.2.1
  have hraw :
      Filter.Tendsto
        (fun ε : ℝ =>
          (plusRaw ε - minusRaw ε) - (plusTarget ε - minusTarget ε))
        l
        (nhds 0) := by
    simpa [l, φFlat, plusRaw, minusRaw, plusTarget, minusTarget, j] using
      hshifted
  have hside :
      Filter.Tendsto
        (fun ε : ℝ =>
          (plusSide ε - minusSide ε) - (plusTarget ε - minusTarget ε))
        l
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hraw
    filter_upwards [hplain] with ε hε
    have hεη := hε ηsrc (by simp [Kη])
    have hplus_int : plusRaw ε = plusSide ε := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u
      have hpoint :
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc φFlat).1 :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u) =
            φFlat
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u +
                  (((1 : ℝ) * ε) • ηsrc)) := by
        simpa [one_mul] using (hεη u).1
      dsimp [plusRaw, plusSide]
      rw [← hpoint]
    have hminus_int : minusRaw ε = minusSide ε := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u
      have hpoint :
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc φFlat).1 :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u) =
            φFlat
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u +
                  (((-1 : ℝ) * ε) • ηsrc)) := by
        simpa [sub_eq_add_neg, neg_smul, neg_mul] using (hεη u).2
      dsimp [minusRaw, minusSide]
      rw [← hpoint]
    change
      (plusRaw ε - minusRaw ε) - (plusTarget ε - minusTarget ε) =
        (plusSide ε - minusSide ε) - (plusTarget ε - minusTarget ε)
    rw [hplus_int, hminus_int]
  simpa [sourceSideSideZeroReducedEndpointTransport, l, φFlat, plusSide,
    minusSide, plusTarget, minusTarget, j] using hside

set_option maxHeartbeats 1200000 in
/-- Private diagnostic Hdiff consumer for the over-strong reindexed
finite-height endpoint hypotheses.

The public Path-2 consumer is
`tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_sourceSide_shifted_transport`;
that theorem keeps the OS-I `(4.12)`--`(4.14)` source-side endpoint limits as
the real analytic/reindexing/DCT leaf.  This private theorem is intentionally
not exported as a theorem-2 route. -/
private theorem tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_reindexed_sourceSide_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {hd : 2 ≤ d} {i : Fin (m + 1)}
    {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ θ : SchwartzNPoint d (m + 1),
        HasCompactSupport (θ : NPointDomain d (m + 1) → ℂ) →
        tsupport (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * θ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    {Ωplus Ωminus : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1)) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm z))
        Ωminus)
    {Usrc Ksrc : Set (NPointDomain d (m + 1))}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hKsrc_sub_U : Ksrc ⊆ U)
    (hUsrcP : Usrc ⊆ P.V)
    (ηsrc : BHW.OS45FlatCommonChartReal d (m + 1))
    (hηsrcC : ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1))
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0 ηsrc u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) 0 ηsrc u ∈ Ωminus)
    (χ : BHW.NormalizedBasepointCutoff d)
    (ψ : SchwartzNPoint d m)
    (hχ_compact : HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hliftU :
      tsupport
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc)
    (hplus_flat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (fun a =>
                ((x + (((1 : ℝ) * ε) • ηsrc)) a : ℂ) +
                  (((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (x + (((1 : ℝ) * ε) • ηsrc))))
    (hplus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u : NPointDomain d (m + 1),
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            let e : NPointDomain d (m + 1) ≃L[ℝ]
                BHW.OS45FlatCommonChartReal d (m + 1) :=
              BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))
            let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
              ((1 : ℝ) * ε) • ηsrc
            BHW.permAct (d := d)
                (1 : Equiv.Perm (Fin (m + 1))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                  (e.symm (e u - a))) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d)
                  (1 : Equiv.Perm (Fin (m + 1))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηsrc
                    (e.symm (e u - a)))) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)
    (hminus_flat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d (m + 1) =>
            BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (fun a =>
                ((x + (((-1 : ℝ) * ε) • ηsrc)) a : ℂ) +
                  (((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I)) *
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm)
                (BHW.reducedTestLift m d χ.toSchwartz ψ :
                  SchwartzNPoint d (m + 1)) :
                SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ)
                (x + (((-1 : ℝ) * ε) • ηsrc))))
    (hminus_transport :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ u : NPointDomain d (m + 1),
          ((BHW.reducedTestLift m d χ.toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ) u ≠ 0 →
            let e : NPointDomain d (m + 1) ≃L[ℝ]
                BHW.OS45FlatCommonChartReal d (m + 1) :=
              BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))
            let a : BHW.OS45FlatCommonChartReal d (m + 1) :=
              ((-1 : ℝ) * ε) • ηsrc
            BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                  (e.symm (e u - a))) ∈
              BHW.ExtendedTube d (m + 1) ∧
            BHW.reducedDiffMap (m + 1) d
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηsrc
                    (e.symm (e u - a)))) =
              fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d u k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            ψ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  have hplus_flat_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
        l
        (nhds 0) := by
    simpa [l] using
      tendsto_flatCommonChart_branch_integral_sub_canonicalReducedBranch_reducedTestLift_of_reindexed_sourceSide_transport
        (d := d) OS lgc Fred
        (σ := (1 : Equiv.Perm (Fin (m + 1))))
        (ρperm := (1 : Equiv.Perm (Fin (m + 1))))
        (sgn := (1 : ℝ)) (η := ηsrc) χ ψ
        hplus_flat_int hplus_transport
  have hminus_flat_transport :
      Filter.Tendsto
        (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) * Complex.I) *
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1)))).symm)
              (BHW.reducedTestLift m d χ.toSchwartz ψ :
                SchwartzNPoint d (m + 1)) :
              SchwartzMap (BHW.OS45FlatCommonChartReal d (m + 1)) ℂ) x) -
          (BHW.os45CommonEdgeFlatJacobianAbs (m + 1) : ℂ) *
            ∫ ξ : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i j ε ξ *
                ψ ξ)
        l
        (nhds 0) := by
    simpa [l, j] using
      tendsto_flatCommonChart_branch_integral_sub_canonicalAfterReducedSwapBranch_reducedTestLift_of_reindexed_sourceSide_transport
        (d := d) OS lgc i j Fred
        (σ := (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))))
        (ρperm := (1 : Equiv.Perm (Fin (m + 1))))
        (sgn := (-1 : ℝ)) (η := ηsrc) χ ψ
        hminus_flat_int hminus_transport
  exact
    tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_flat_transport
      (d := d) OS lgc D U hU_open hU_nonempty Ucx Hdiff
      hUcx_open hUcx_connected hwick_mem hcommon_mem hHdiff_holo
      hwick_pairing_zero hcommon_trace hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hKsrc_sub_U
      hUsrcP ηsrc hηsrcC h0_plus h0_minus χ ψ
      hχ_compact hψ_compact hliftU hplus_flat_transport
      hminus_flat_transport

namespace AdjacentNormal

omit [NeZero d] in
/-- Insert the discarded pair center as zero. -/
noncomputable def reducedNormalZeroCenterCLM
    {m : ℕ} (i j : Fin (m + 1)) :
    ReducedSpace d m i j →L[ℝ] Space d (m + 1) i j :=
  (0 : ReducedSpace d m i j →L[ℝ] SpacetimeDim d).prod
    (ContinuousLinearMap.id ℝ (ReducedSpace d m i j))

omit [NeZero d] in
@[simp]
theorem reducedNormalZeroCenterCLM_apply
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j) :
    reducedNormalZeroCenterCLM (d := d) i j p =
      ((0 : SpacetimeDim d), p) := by
  rfl

omit [NeZero d] in
/-- Reconstruct the absolute source representative of a flattened reduced
normal point, with the selected pair center fixed at zero. -/
noncomputable def reducedNormalAbsoluteSectionCLM
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) →L[ℝ] NPointDomain d (m + 1) :=
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := reducedAdjacent_succ_ne i hi
  ((coordCLE (d := d) i j hij).symm.toContinuousLinearMap).comp
    ((reducedNormalZeroCenterCLM (d := d) i j).comp
      ((reducedNormalFlattenCLE (d := d) i j).symm.toContinuousLinearMap))

omit [NeZero d] in
@[simp]
theorem reducedNormalAbsoluteSectionCLM_apply
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalAbsoluteSectionCLM (d := d) i hi u =
      coordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        ((0 : SpacetimeDim d),
          (reducedNormalFlattenCLE
            (d := d) i ⟨i.val + 1, hi⟩).symm u) := by
  rfl

omit [NeZero d] in
@[simp]
theorem reducedNormalAbsoluteSectionCLM_apply_flatten
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedNormalAbsoluteSectionCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p) =
      coordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        ((0 : SpacetimeDim d), p) := by
  simp

omit [NeZero d] in
/-- The zero-center reduced-normal representative has the same successive
reduced differences as the absolute source configuration it represents.

This is the algebraic bridge needed before applying the Figure-2-4
cone-height packet to a lifted reduced test: an arbitrary source point is first
collapsed to its reduced differences, converted to adjacent normal coordinates,
and reconstructed with pair center zero; reduced differences are unchanged. -/
theorem reducedNormalAbsoluteSectionCLM_reducedDiffMapReal_eq
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (u : NPointDomain d (m + 1)) :
    BHW.reducedDiffMapReal (m + 1) d
        (reducedNormalAbsoluteSectionCLM (d := d) i hi
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩
            ((reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi))
              (BHW.reducedDiffMapReal (m + 1) d u)))) =
      BHW.reducedDiffMapReal (m + 1) d u := by
  simpa [reducedNormalAbsoluteSectionCLM_apply_flatten] using
    reducedCoordInv_left (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      (BHW.reducedDiffMapReal (m + 1) d u)

omit [NeZero d] in
/-- Equality of reduced real differences determines every pairwise real
difference.  This is the uniform-translation fact needed when the OS45 common
edge later permutes source labels before taking adjacent differences. -/
theorem reducedDiffMapReal_eq_pair_sub_eq
    {m : ℕ} {x y : NPointDomain d (m + 1)}
    (hxy : BHW.reducedDiffMapReal (m + 1) d x =
      BHW.reducedDiffMapReal (m + 1) d y)
    (a b : Fin (m + 1)) (μ : Fin (d + 1)) :
    x a μ - x b μ = y a μ - y b μ := by
  have hx := reducedSection_reducedDiffMapReal_eq_sub_basepoint (d := d) m x
  have hy := reducedSection_reducedDiffMapReal_eq_sub_basepoint (d := d) m y
  have hsec : (fun k μ => x k μ - x 0 μ) =
      (fun k μ => y k μ - y 0 μ) := by
    rw [← hx, ← hy, hxy]
  have ha := congrFun (congrFun hsec a) μ
  have hb := congrFun (congrFun hsec b) μ
  linarith

omit [NeZero d] in
/-- The OS45 common-edge real projection depends only on reduced real
differences, even after a source-label permutation and the half-time
normalization. -/
theorem reducedDiffMapReal_os45CommonEdgeRealPoint_eq_of_reducedDiffMapReal_eq
    {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    {x y : NPointDomain d (m + 1)}
    (hxy : BHW.reducedDiffMapReal (m + 1) d x =
      BHW.reducedDiffMapReal (m + 1) d y) :
    BHW.reducedDiffMapReal (m + 1) d
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ x) =
      BHW.reducedDiffMapReal (m + 1) d
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ y) := by
  ext k μ
  rw [BHW.reducedDiffMapReal_apply, BHW.reducedDiffMapReal_apply]
  let a : Fin (m + 1) := σ ⟨k.val + 1, by omega⟩
  let b : Fin (m + 1) := σ ⟨k.val, by omega⟩
  have hpair : x a μ - x b μ = y a μ - y b μ :=
    reducedDiffMapReal_eq_pair_sub_eq (d := d) hxy a b μ
  by_cases hμ : μ = (0 : Fin (d + 1))
  · subst μ
    simp [BHW.os45CommonEdgeRealPoint]
    linarith
  · simpa [BHW.os45CommonEdgeRealPoint, hμ, a, b] using hpair

omit [NeZero d] in
/-- Chart-native form of
`reducedDiffMapReal_os45CommonEdgeRealPoint_eq_of_reducedDiffMapReal_eq`: after
passing through the flattened OS45 common-edge equivalence and unflattening by
the real chart equivalence, only reduced real differences remain visible. -/
theorem reducedDiffMapReal_flattenCLEquivReal_symm_os45CommonEdgeFlatCLE_eq_of_reducedDiffMapReal_eq
    {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    {x y : NPointDomain d (m + 1)}
    (hxy : BHW.reducedDiffMapReal (m + 1) d x =
      BHW.reducedDiffMapReal (m + 1) d y) :
    BHW.reducedDiffMapReal (m + 1) d
        ((flattenCLEquivReal (m + 1) (d + 1)).symm
          ((BHW.os45CommonEdgeFlatCLE d (m + 1) σ) x)) =
      BHW.reducedDiffMapReal (m + 1) d
        ((flattenCLEquivReal (m + 1) (d + 1)).symm
          ((BHW.os45CommonEdgeFlatCLE d (m + 1) σ) y)) := by
  simpa [BHW.os45CommonEdgeFlatCLE] using
    reducedDiffMapReal_os45CommonEdgeRealPoint_eq_of_reducedDiffMapReal_eq
      (d := d) σ hxy

omit [NeZero d] in
/-- Specializing the common-edge invariance to the reduced-normal zero-center
section: replacing a source point by its reduced-normal representative leaves
all OS45 common-edge reduced real differences unchanged. -/
theorem reducedNormalAbsoluteSectionCLM_os45CommonEdgeRealPoint_reducedDiffMapReal_eq
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1))) (u : NPointDomain d (m + 1)) :
    BHW.reducedDiffMapReal (m + 1) d
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ
          (reducedNormalAbsoluteSectionCLM (d := d) i hi
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩
              ((reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi))
                (BHW.reducedDiffMapReal (m + 1) d u))))) =
      BHW.reducedDiffMapReal (m + 1) d
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ u) := by
  exact
    reducedDiffMapReal_os45CommonEdgeRealPoint_eq_of_reducedDiffMapReal_eq
      (d := d) σ
      (reducedNormalAbsoluteSectionCLM_reducedDiffMapReal_eq
        (d := d) (i := i) (hi := hi) u)

omit [NeZero d] in
/-- Flattened-chart specialization of the reduced-normal section invariance:
the source point and its zero-center reduced-normal representative have the same
reduced real differences after the OS45 flat common-edge chart is inverted. -/
theorem reducedNormalAbsoluteSectionCLM_flattenCLEquivReal_symm_os45CommonEdgeFlatCLE_reducedDiffMapReal_eq
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1))) (u : NPointDomain d (m + 1)) :
    BHW.reducedDiffMapReal (m + 1) d
        ((flattenCLEquivReal (m + 1) (d + 1)).symm
          ((BHW.os45CommonEdgeFlatCLE d (m + 1) σ)
            (reducedNormalAbsoluteSectionCLM (d := d) i hi
              (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩
                ((reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (BHW.reducedDiffMapReal (m + 1) d u)))))) =
      BHW.reducedDiffMapReal (m + 1) d
        ((flattenCLEquivReal (m + 1) (d + 1)).symm
          ((BHW.os45CommonEdgeFlatCLE d (m + 1) σ) u)) := by
  exact
    reducedDiffMapReal_flattenCLEquivReal_symm_os45CommonEdgeFlatCLE_eq_of_reducedDiffMapReal_eq
      (d := d) σ
      (reducedNormalAbsoluteSectionCLM_reducedDiffMapReal_eq
        (d := d) (i := i) (hi := hi) u)

omit [NeZero d] in
/-- The OS45 flat common-edge coordinates associated to a flattened reduced
normal point. -/
noncomputable def reducedNormalToOS45CommonEdgeFlatCLM
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) →L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
  ((BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))).toContinuousLinearMap).comp
    (reducedNormalAbsoluteSectionCLM (d := d) i hi)

omit [NeZero d] in
/-- Complex-linear extension of the reduced-normal to OS45 flat common-edge
coordinate map. -/
noncomputable def reducedNormalToOS45CommonEdgeComplexCLM
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
  SCV.realCLMComplexification
    (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi)

omit [NeZero d] in
@[simp]
theorem reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
        (SCV.realEmbed u) =
      SCV.realEmbed
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u) := by
  exact
    SCV.realCLMComplexification_realEmbed
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi) u

omit [NeZero d] in
theorem reducedNormalToOS45CommonEdgeComplexCLM_upperRay
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
        (reducedNormalUpperCanonicalRay (d := d) i hi p ε) =
      fun a =>
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
            (reducedNormalFlattenCLE
              (d := d) i ⟨i.val + 1, hi⟩ p) a : ℂ) +
          (ε : ℂ) *
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi) a : ℂ) *
            Complex.I := by
  simpa [reducedNormalToOS45CommonEdgeComplexCLM,
    reducedNormalUpperCanonicalRay] using
    SCV.realCLMComplexification_real_add_imag
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi)
      (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      (reducedNormalFlatCanonicalDirection (d := d) i hi) ε

omit [NeZero d] in
theorem reducedNormalToOS45CommonEdgeComplexCLM_lowerRay
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
        (reducedNormalLowerCanonicalRay (d := d) i hi p ε) =
      fun a =>
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
            (reducedNormalFlattenCLE
              (d := d) i ⟨i.val + 1, hi⟩ p) a : ℂ) -
          (ε : ℂ) *
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi) a : ℂ) *
            Complex.I := by
  simpa [reducedNormalToOS45CommonEdgeComplexCLM,
    reducedNormalLowerCanonicalRay] using
    SCV.realCLMComplexification_real_sub_imag
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi)
      (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      (reducedNormalFlatCanonicalDirection (d := d) i hi) ε

set_option maxHeartbeats 1200000 in
omit [NeZero d] in
/-- The signed OS45 source-side direction induced by the reduced-normal
canonical flat direction descends to the signed canonical reduced imaginary
direction. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSideDirection_reducedNormalCanonical_eq
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (sgn : ℝ) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) sgn η) =
      fun k μ =>
        (sgn : ℂ) * canonicalReducedDirectionC (d := d) m k μ *
          Complex.I := by
  intro η
  ext k μ
  have hdiv_succ :
      (finProdFinEquiv
        ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).divNat =
        (⟨k.val + 1, by omega⟩ : Fin (m + 1)) := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).1 =
        (⟨k.val + 1, by omega⟩ : Fin (m + 1))
    simp
  have hmod_succ :
      (finProdFinEquiv
        ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).2 = μ
    simp
  have hdiv_curr :
      (finProdFinEquiv
        ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).divNat =
        (⟨k.val, by omega⟩ : Fin (m + 1)) := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).1 =
        (⟨k.val, by omega⟩ : Fin (m + 1))
    simp
  have hmod_curr :
      (finProdFinEquiv
        ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).2 = μ
    simp
  have hdir :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            ((0 : SpacetimeDim d),
              (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi))
                (canonicalReducedDirection (d := d) m))
            ⟨k.val + 1, by omega⟩ μ -
          coordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            ((0 : SpacetimeDim d),
              (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi))
                (canonicalReducedDirection (d := d) m))
            ⟨k.val, by omega⟩ μ =
        canonicalReducedDirection (d := d) m k μ := by
    have hleft :=
      reducedCoordInv_left (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        (canonicalReducedDirection (d := d) m)
    have h :=
      congrFun (congrFun hleft k) μ
    simpa [reducedCoordInv, reducedCoordCLE, BHW.reducedDiffMapReal_apply]
      using h
  have hdirC :
      ((coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val + 1, by omega⟩ μ : ℂ) -
            (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val, by omega⟩ μ : ℂ)) =
        (canonicalReducedDirection (d := d) m k μ : ℂ) := by
    exact_mod_cast hdir
  simp only [BHW.reducedDiffMap_eq_successive_differences]
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45FlatCommonChartSourceSideDirection, η,
      reducedNormalToOS45CommonEdgeFlatCLM,
      reducedNormalFlatCanonicalDirection,
      BHW.os45CommonEdgeFlatCLE,
      BHW.os45CommonEdgeRealPoint,
      BHW.os45QuarterTurnCLE_symm_apply,
      BHW.unflattenCfg, flattenCLEquivReal_apply,
      Pi.smul_apply, canonicalReducedDirectionC,
      hdiv_succ, hmod_succ, hdiv_curr, hmod_curr]
    rw [← hdirC]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  · simp [BHW.os45FlatCommonChartSourceSideDirection, η,
      reducedNormalToOS45CommonEdgeFlatCLM,
      reducedNormalFlatCanonicalDirection,
      BHW.os45CommonEdgeFlatCLE,
      BHW.os45CommonEdgeRealPoint,
      BHW.os45QuarterTurnCLE_symm_apply,
      BHW.unflattenCfg, flattenCLEquivReal_apply,
      Pi.smul_apply, canonicalReducedDirectionC,
      hμ, hdiv_succ, hmod_succ, hdiv_curr, hmod_curr]
    have hsucc_eq :
        (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val + 1, by omega⟩ μ : ℂ) =
          (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val, by omega⟩ μ : ℂ) := by
      apply sub_eq_zero.mp
      simpa [canonicalReducedDirection, BHW.safeBasepointVec, hμ]
        using hdirC
    rw [hsucc_eq]
    simp [canonicalReducedDirection, BHW.safeBasepointVec, hμ]

/-- With the reduced-normal canonical flat direction, the signed OS45 source-side
path is an affine reduced ray in the signed canonical reduced imaginary
direction. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_reducedNormalCanonical_affine
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (sgn ε : ℝ) (u : NPointDomain d (m + 1)) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) sgn ε η u) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) sgn 0 η u) +
        (ε : ℂ) •
          (fun k μ =>
            (sgn : ℂ) * canonicalReducedDirectionC (d := d) m k μ *
              Complex.I) := by
  intro η
  rw [BHW.reducedDiffMap_os45FlatCommonChartSourceSide_affine]
  rw [reducedDiffMap_os45FlatCommonChartSourceSideDirection_reducedNormalCanonical_eq
    (d := d) (i := i) (hi := hi) sgn]

/-- The upper reduced-normal canonical ray is the OS45 source-side branch
evaluation with the flat source point translated by `-εη`.

This is only a coordinate normal form for the OS-I `(4.14)` moving-source
transfer: the analytic comparison with the canonical reduced boundary branch is
still the remaining proof leaf. -/
theorem reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
    let uε : NPointDomain d (m + 1) :=
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalToOS45CommonEdgeComplexCLM
          (d := d) i hi
          (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) := by
  intro η x0 uε
  rw [reducedNormalToOS45CommonEdgeComplexCLM_upperRay]
  change BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
      (1 : Equiv.Perm (Fin (m + 1)))
      (fun a => (x0 a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) = _
  rw [show (fun a => (x0 a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) =
      (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) uε + ((1 : ℝ) * ε) • η) a : ℂ) +
          ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) by
    ext a
    simp [uε, sub_eq_add_neg, Pi.smul_apply]]
  simpa using
    BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF
      d (m + 1) OS lgc
      (1 : Equiv.Perm (Fin (m + 1)))
      (1 : Equiv.Perm (Fin (m + 1)))
      (1 : ℝ) ε η uε

/-- The lower reduced-normal canonical ray is the adjacent OS45 source-side
branch evaluation with the flat source point translated by `+εη`.

This is the signed companion to
`reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving`; the analytic
adjacent `(4.12)`/`(4.14)` source-side transfer remains explicit. -/
theorem reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
    let uε : NPointDomain d (m + 1) :=
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
        (reducedNormalToOS45CommonEdgeComplexCLM
          (d := d) i hi
          (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) := by
  intro η x0 uε
  rw [reducedNormalToOS45CommonEdgeComplexCLM_lowerRay]
  change BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
      (fun a => (x0 a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) = _
  rw [show (fun a => (x0 a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) =
      (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) uε + ((-1 : ℝ) * ε) • η) a : ℂ) +
          ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) by
    ext a
    simp [uε, sub_eq_add_neg, Pi.smul_apply]]
  simpa using
    BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF
      d (m + 1) OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
      (1 : Equiv.Perm (Fin (m + 1)))
      (-1 : ℝ) ε η uε

omit [NeZero d] in
@[simp]
theorem reducedNormalToOS45CommonEdgeFlatCLM_apply
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u =
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalAbsoluteSectionCLM (d := d) i hi u) := by
  rfl

/-- The reduced-normal preimage of a Figure-2-4 source patch.  This is the
local real collar used by the support-local Ruelle construction. -/
def reducedNormalOS45SourcePatchPreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi) :
    Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :=
  {u | reducedNormalAbsoluteSectionCLM (d := d) i hi u ∈ P.V}

theorem isOpen_reducedNormalOS45SourcePatchPreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi) :
    IsOpen (reducedNormalOS45SourcePatchPreimage
      (d := d) i hi P) := by
  exact P.V_open.preimage
    (reducedNormalAbsoluteSectionCLM (d := d) i hi).continuous

theorem reducedNormalFlatten_mem_reducedNormalOS45SourcePatchPreimage_iff
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈
        reducedNormalOS45SourcePatchPreimage (d := d) i hi P ↔
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V := by
  simp [reducedNormalOS45SourcePatchPreimage]

/-- If a reduced test is supported in the reduced-normal preimage of the OS45
source patch, then every nonzero point of its absolute reduced lift has a
zero-center reduced-normal representative in that source patch.

This is the support-routing form needed by the cone-height packet: it uses a
condition on reduced variables, not an invalid claim that the arbitrary
absolute lift and its zero-center representative share source-patch
membership. -/
theorem reducedTestLift_support_zeroCenterSection_mem_sourcePatch
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (ψ : SchwartzNPoint d m)
    (hψ_patch :
      tsupport (ψ : NPointDomain d m → ℂ) ⊆
        {ξ : NPointDomain d m |
          reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩
            ((reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)) ξ) ∈
            reducedNormalOS45SourcePatchPreimage (d := d) i hi P})
    {u : NPointDomain d (m + 1)}
    (hu : ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
        NPointDomain d (m + 1) → ℂ) u ≠ 0) :
    reducedNormalAbsoluteSectionCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩
          ((reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi))
            (BHW.reducedDiffMapReal (m + 1) d u))) ∈ P.V := by
  let f : NPointDomain d (m + 1) → ℂ :=
    ((BHW.reducedTestLift m d χ ψ : SchwartzNPoint d (m + 1)) :
      NPointDomain d (m + 1) → ℂ)
  have hu_support : u ∈ Function.support f := by
    exact Function.mem_support.mpr (by simpa [f] using hu)
  have hu_tsupport : u ∈ tsupport f :=
    subset_tsupport f hu_support
  have hred :
      BHW.reducedDiffMapReal (m + 1) d u ∈
        tsupport (ψ : NPointDomain d m → ℂ) := by
    have hsubset :=
      reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
        (d := d) (m := m) χ ψ
    simpa [f, BHW.reducedDiffMapRealCLM] using hsubset hu_tsupport
  have hξ := hψ_patch hred
  simpa [reducedNormalOS45SourcePatchPreimage,
    reducedNormalAbsoluteSectionCLM_apply_flatten] using hξ

/-- The reduced-normal preimage of an arbitrary source window.  This is the
local form used after a selected Jost seed has narrowed the Figure-2-4 patch to
a smaller source collar. -/
def reducedNormalOS45SourcePreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (U : Set (NPointDomain d (m + 1))) :
    Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :=
  {u | reducedNormalAbsoluteSectionCLM (d := d) i hi u ∈ U}

omit [NeZero d] in
theorem isOpen_reducedNormalOS45SourcePreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {U : Set (NPointDomain d (m + 1))}
    (hU_open : IsOpen U) :
    IsOpen (reducedNormalOS45SourcePreimage
      (d := d) i hi U) := by
  exact hU_open.preimage
    (reducedNormalAbsoluteSectionCLM (d := d) i hi).continuous

omit [NeZero d] in
theorem reducedNormalFlatten_mem_reducedNormalOS45SourcePreimage_iff
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (U : Set (NPointDomain d (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈
        reducedNormalOS45SourcePreimage (d := d) i hi U ↔
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U := by
  simp [reducedNormalOS45SourcePreimage]

theorem reducedNormalOS45SourcePreimage_subset_patchPreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {U : Set (NPointDomain d (m + 1))}
    (hU_sub : U ⊆ P.V) :
    reducedNormalOS45SourcePreimage (d := d) i hi U ⊆
      reducedNormalOS45SourcePatchPreimage (d := d) i hi P := by
  intro u hu
  exact hU_sub hu

omit [NeZero d] in
theorem reducedNormalToOS45CommonEdgeFlatCLM_mem_sourceImage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {U : Set (NPointDomain d (m + 1))}
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePreimage (d := d) i hi U) :
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1))) '' U := by
  exact
    ⟨reducedNormalAbsoluteSectionCLM (d := d) i hi u, hu, rfl⟩

theorem reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) ↔
      u ∈ reducedNormalOS45SourcePatchPreimage (d := d) i hi P := by
  simpa [reducedNormalOS45SourcePatchPreimage]
    using
      BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalAbsoluteSectionCLM (d := d) i hi u)

theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePatchPreimage (d := d) i hi P) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) := by
  have hedge :
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) :=
    (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
      (d := d) i hi P u).2 hu
  exact
    BHW.os45FlatCommonChart_real_mem_omega_id
      (d := d) hd (P := P)
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u) hedge

theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePatchPreimage (d := d) i hi P) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) := by
  have hedge :
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) :=
    (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
      (d := d) i hi P u).2 hu
  exact
    BHW.os45FlatCommonChart_real_mem_omega_adjacent
      (d := d) hd (P := P)
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u) hedge

/-- Local source-window version of
`reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id`. -/
theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id_of_sourcePreimage
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {U : Set (NPointDomain d (m + 1))}
    (hU_sub : U ⊆ P.V)
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePreimage (d := d) i hi U) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) := by
  exact
    reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id
      (d := d) hd (P := P) (u := u)
      (reducedNormalOS45SourcePreimage_subset_patchPreimage
        (d := d) i hi (P := P) hU_sub hu)

/-- Local source-window version of
`reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent`. -/
theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent_of_sourcePreimage
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {U : Set (NPointDomain d (m + 1))}
    (hU_sub : U ⊆ P.V)
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePreimage (d := d) i hi U) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) := by
  exact
    reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent
      (d := d) hd (P := P) (u := u)
      (reducedNormalOS45SourcePreimage_subset_patchPreimage
        (d := d) i hi (P := P) hU_sub hu)

/-- Pull an OS45 Figure-2-4 branch packet back to a local reduced-normal
collar over a source window `U ⊆ P.V`.

This is the local form needed after the Ruelle/Jost seed has been restricted to
a neighborhood of the support point.  The assumptions left visible are the
remaining analytic payload on that local source window: source common-edge
equality. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatchOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  let q : ℕ :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let σadj : Equiv.Perm (Fin (m + 1)) := P.τ.symm * σ0
  let L : SCV.ComplexChartSpace q →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let E : Set (Fin q → ℝ) :=
    reducedNormalOS45SourcePreimage (d := d) i hi U
  let Ωplus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σ0
  let Ωminus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σadj
  let Fplus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ0 (L z)
  let Fminus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σadj (L z)
  let bv : (Fin q → ℝ) → ℂ := fun x => Fplus (SCV.realEmbed x)
  have hE_open : IsOpen E := by
    simpa [E] using
      isOpen_reducedNormalOS45SourcePreimage (d := d) i hi hU_open
  have hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E := by
    simpa [E] using
      (reducedNormalFlatten_mem_reducedNormalOS45SourcePreimage_iff
        (d := d) i hi U p).2 hpU
  have hΩplus_open : IsOpen Ωplus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σ0).preimage
        L.continuous
  have hΩminus_open : IsOpen Ωminus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σadj).preimage
        L.continuous
  have hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σ0 := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωplus] using hxΩ
  have hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σadj := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σadj, σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωminus] using hxΩ
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σ0).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σadj).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    have hreal :
        Continuous (fun x : Fin q → ℝ => SCV.realEmbed x) := by
      simpa [SCV.realEmbed] using
        (continuous_pi fun a =>
          Complex.continuous_ofReal.comp (continuous_apply a))
    exact hFplus_diff.continuousOn.comp hreal.continuousOn hplus0
  have htrace :
      ∀ x ∈ E, Fminus (SCV.realEmbed x) = Fplus (SCV.realEmbed x) := by
    intro x hx
    have himage :
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x ∈
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' U := by
      exact
        reducedNormalToOS45CommonEdgeFlatCLM_mem_sourceImage
          (d := d) i hi (U := U) (u := x) (by simpa [E] using hx)
    have hflat :=
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
        (d := d) hd OS lgc (P := P) (U := U) hsource
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) himage
    have hL :
        L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) := by
      simpa [L, q] using
        reducedNormalToOS45CommonEdgeComplexCLM_realEmbed (d := d) i hi x
    simpa [Fplus, Fminus, σadj, σ0, hL] using hflat
  have hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    simpa [bv] using
      (hFplus_diff.continuousOn.continuousWithinAt
        (hplus0 x hx)).tendsto
  have hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hlim :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) :=
      (hFminus_diff.continuousOn.continuousWithinAt
        (hminus0 x hx)).tendsto
    simpa [bv, htrace x hx] using hlim
  have hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  refine
    ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem
      (d := d) (OS := OS) (lgc := lgc) (p := p)
      E hE_open hpE Ωplus Ωminus Set.univ
      hΩplus_open hΩminus_open isOpen_univ convex_univ Set.univ_nonempty
      hplus0 hminus0 Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv hplus_nhds hminus_nhds ?_ ?_
  · simpa [Fplus, L, σ0, q] using hplus_rep
  · simpa [Fminus, L, σadj, σ0, q] using hminus_rep

/-- Pull an OS45 Figure-2-4 branch packet back to a local reduced-normal
sign-flip comparison with asymptotic branch transfer.

This is the OS-I `(4.14)` form of
`reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatchOn`: the two
canonical reduced branches are only required to be asymptotic to the OS45 side
branches along the pulled-back canonical rays. -/
theorem reducedNormalSignFlip_pointwise_of_OS45SourcePatchOn_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let q : ℕ :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let σadj : Equiv.Perm (Fin (m + 1)) := P.τ.symm * σ0
  let L : SCV.ComplexChartSpace q →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let E : Set (Fin q → ℝ) :=
    reducedNormalOS45SourcePreimage (d := d) i hi U
  let Ωplus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σ0
  let Ωminus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σadj
  let Fplus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ0 (L z)
  let Fminus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σadj (L z)
  let bv : (Fin q → ℝ) → ℂ := fun x => Fplus (SCV.realEmbed x)
  have hE_open : IsOpen E := by
    simpa [E] using
      isOpen_reducedNormalOS45SourcePreimage (d := d) i hi hU_open
  have hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E := by
    simpa [E] using
      (reducedNormalFlatten_mem_reducedNormalOS45SourcePreimage_iff
        (d := d) i hi U p).2 hpU
  have hΩplus_open : IsOpen Ωplus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σ0).preimage
        L.continuous
  have hΩminus_open : IsOpen Ωminus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σadj).preimage
        L.continuous
  have hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σ0 := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωplus] using hxΩ
  have hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σadj := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σadj, σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωminus] using hxΩ
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σ0).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σadj).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    have hreal :
        Continuous (fun x : Fin q → ℝ => SCV.realEmbed x) := by
      simpa [SCV.realEmbed] using
        (continuous_pi fun a =>
          Complex.continuous_ofReal.comp (continuous_apply a))
    exact hFplus_diff.continuousOn.comp hreal.continuousOn hplus0
  have htrace :
      ∀ x ∈ E, Fminus (SCV.realEmbed x) = Fplus (SCV.realEmbed x) := by
    intro x hx
    have himage :
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x ∈
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' U := by
      exact
        reducedNormalToOS45CommonEdgeFlatCLM_mem_sourceImage
          (d := d) i hi (U := U) (u := x) (by simpa [E] using hx)
    have hflat :=
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
        (d := d) hd OS lgc (P := P) (U := U) hsource
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) himage
    have hL :
        L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) := by
      simpa [L, q] using
        reducedNormalToOS45CommonEdgeComplexCLM_realEmbed (d := d) i hi x
    simpa [Fplus, Fminus, σadj, σ0, hL] using hflat
  have hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    simpa [bv] using
      (hFplus_diff.continuousOn.continuousWithinAt
        (hplus0 x hx)).tendsto
  have hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hlim :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) :=
      (hFminus_diff.continuousOn.continuousWithinAt
        (hminus0 x hx)).tendsto
    simpa [bv, htrace x hx] using hlim
  have hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  exact
    reducedNormalSignFlip_pointwise_of_localEOW_asymptoticBranchDataOn
      (d := d) OS lgc i hi p E hE_open hpE Ωplus Ωminus Set.univ
      hΩplus_open hΩminus_open isOpen_univ convex_univ Set.univ_nonempty
      (reducedNormalFlattened_localWedge_of_openEdge_mem
        (d := d) i hi E Ωplus Ωminus Set.univ
        hΩplus_open hΩminus_open hplus0 hminus0)
      Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
      hFplus_bv hFminus_bv hplus_nhds hminus_nhds
      (by simpa [Fplus, L, σ0, q] using hplus_transfer)
      (by simpa [Fminus, L, σadj, σ0, q] using hminus_transfer)

/-- Pull a Ruelle-overlap equality seed back to the asymptotic reduced-normal
sign-flip comparison.

This is the overlap-seed version of the OS-I `(4.14)` handoff: the seed supplies
common-edge equality on a local source window, while the two side-to-canonical
ray transfers remain asymptotic hypotheses. -/
theorem reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    {W : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d), p)))) ∈ W)
    (heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let zc : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ := fun u =>
    (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ0 u))
  let U : Set (NPointDomain d (m + 1)) := P.V ∩ zc ⁻¹' W
  have hzc_cont : Continuous zc := by
    exact
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm.continuous.comp
        (by
          simpa [σ0] using
            BHW.continuous_realEmbed_os45CommonEdgeRealPoint
              (d := d) (n := m + 1) σ0)
  have hU_open : IsOpen U := by
    exact P.V_open.inter (hW_open.preimage hzc_cont)
  have hU_sub : U ⊆ P.V := by
    intro u hu
    exact hu.1
  have hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U := by
    exact ⟨hpP, by simpa [U, zc, σ0] using hzW⟩
  have hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    exact
      BHW.os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
        (d := d) hd OS lgc (P := P) (U := U) (Ucx := W)
        (by
          intro u hu
          simpa [zc, σ0, U] using hu.2)
        heq
  exact
    reducedNormalSignFlip_pointwise_of_OS45SourcePatchOn_asymptotic
      (d := d) OS lgc P U hU_open hU_sub p hpU hsource
      hplus_transfer hminus_transfer

/-- A local source representation of the zero horizontal common-edge
difference supplies the asymptotic reduced-normal sign-flip comparison.

This is the Hdiff-facing version of the reduced-normal OS45 bridge: the
proof-local Figure-2-4 germ first gives `RepresentsDistributionOn 0` on a source
window, the checked local flat EOW bridge turns that representation into the
ambient overlap seed, and the canonical-ray transfer hypotheses identify the
two OS45 side rays with the reduced canonical rays. -/
theorem reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) U)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  let hSeed :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
      (d := d) hd OS lgc (P := P)
      hU_open hU_sub hrep
      ys hys_mem hys_li u0 (by simpa [u0] using hpU)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
      (d := d) OS lgc P p (hU_sub (by simpa [u0] using hpU))
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_transfer hminus_transfer

/-- A proof-local Figure-2-4 horizontal difference germ supplies the
asymptotic reduced-normal sign-flip comparison.

This is the Hdiff-facing version of
`reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic`: the
holomorphic germ with zero Wick trace first gives the local source
representation of the horizontal common-edge difference, and the existing
reduced-normal bridge then applies the two explicit side-to-canonical ray
transfers. -/
theorem reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hU_nonempty : U.Nonempty)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  have hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) U := by
    exact
      BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
        (d := d) hd OS lgc (P := P) U hU_open hU_nonempty
        Ucx Hdiff hUcx_open hUcx_connected hwick_mem hcommon_mem
        hHdiff_holo hwick_pairing_zero hcommon_trace
  exact
    reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic
      (d := d) OS lgc P U hU_open hU_sub p hpU hrep
      hplus_transfer hminus_transfer

/-- A proof-local Figure-2-4 horizontal difference germ supplies the
asymptotic reduced-normal sign-flip comparison from source-side moving
transfers.

This is the Hdiff-carrier form of
`reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_asymptotic`: once the OS-I
`(4.12)`--`(4.14)` source-side branch transfer has supplied the moving
source-side `extendF` comparison, the checked coordinate identities convert
those branches to the flat OS45 branch values along the reduced-normal
canonical rays. -/
theorem reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_sourceSide_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hU_nonempty : U.Nonempty)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_source_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
            reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi)
          let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
            reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
          let uε : NPointDomain d (m + 1) :=
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
          BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_source_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
            reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi)
          let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
            reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
          let uε : NPointDomain d (m + 1) :=
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
          BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                (BHW.os45FlatCommonChartSourceSide d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  have hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i j
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hplus_source_transfer
    filter_upwards with ε
    have hcoord :=
      reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i j
                (reducedAdjacent_succ_ne i hi) p))
        hcoord
    simpa [j] using hsub.symm
  have hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i j
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i j p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hminus_source_transfer
    filter_upwards with ε
    have hcoord :=
      reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc P p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i j
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i j p)))
        hcoord
    simpa [j] using hsub.symm
  simpa [j] using
    reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_asymptotic
      (d := d) OS lgc P U hU_open hU_sub hU_nonempty p hpU
      Ucx Hdiff hUcx_open hUcx_connected hwick_mem hcommon_mem
      hHdiff_holo hwick_pairing_zero hcommon_trace
      hplus_transfer hminus_transfer

/-- Local source-representation packets on adjacent spacelike collars supply the
reduced local boundary-CLM invariant.

This is the paper-facing Path-2 handoff.  The remaining analytic leaf is local
OS45 source data on each reduced-normal collar: a Figure-2-4 source window
carrying the zero horizontal common-edge representation, together with the two
OS-I `(4.12)`--`(4.14)` side-to-canonical ray transfers. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45SourceRepresentsOn_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ η, ψ η ≠ 0 →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ U : Set (NPointDomain d (m + 1)),
                    IsOpen U ∧ U ⊆ P.V ∧
                    coordInv (d := d) i ⟨i.val + 1, hi⟩
                        (reducedAdjacent_succ_ne i hi)
                        ((0 : SpacetimeDim d),
                          reducedCoord
                            (d := d) i ⟨i.val + 1, hi⟩ η) ∈ U ∧
                    SCV.RepresentsDistributionOn
                      (0 : SchwartzMap
                        (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
                      (fun u : NPointDomain d (m + 1) =>
                        BHW.os45PulledRealBranch
                            (d := d) (n := m + 1) OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u)) -
                          BHW.os45PulledRealBranch
                            (d := d) (n := m + 1) OS lgc
                            (1 : Equiv.Perm (Fin (m + 1)))
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u))) U ∧
                    Filter.Tendsto
                      (fun ε : ℝ =>
                        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                            (1 : Equiv.Perm (Fin (m + 1)))
                            (reducedNormalToOS45CommonEdgeComplexCLM
                              (d := d) i hi
                              (reducedNormalUpperCanonicalRay (d := d) i hi
                                (reducedCoord
                                  (d := d) i ⟨i.val + 1, hi⟩ η) ε)) -
                          canonicalReducedBranch (d := d) OS lgc m ε
                            (reducedCoordInv (d := d)
                              i ⟨i.val + 1, hi⟩
                              (reducedAdjacent_succ_ne i hi)
                              (reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η)))
                      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                      (nhds 0) ∧
                    Filter.Tendsto
                      (fun ε : ℝ =>
                        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                            (reducedNormalToOS45CommonEdgeComplexCLM
                              (d := d) i hi
                              (reducedNormalLowerCanonicalRay (d := d) i hi
                                (reducedCoord
                                  (d := d) i ⟨i.val + 1, hi⟩ η) ε)) -
                          canonicalReducedBranch (d := d) OS lgc m ε
                            (reducedCoordInv (d := d)
                              i ⟨i.val + 1, hi⟩
                              (reducedAdjacent_succ_ne i hi)
                              (reducedSignFlip
                                (d := d) i ⟨i.val + 1, hi⟩
                                (reducedCoord
                                  (d := d) i ⟨i.val + 1, hi⟩ η))))
                      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                      (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  exact
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ (by
        intro m i hi φ hφ_compact hφ_tsupport ξ hξ
        rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
          ⟨V, hV_open, hξV, hVlocal⟩
        refine ⟨V, hV_open, hξV, ?_⟩
        intro ψ hψ_compact hψ_tsupport η hη
        rcases hVlocal ψ hψ_compact hψ_tsupport η hη with
          ⟨P, U, hU_open, hU_sub, hpU, hrep, hplus_transfer,
            hminus_transfer⟩
        let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
        let p : ReducedSpace d m i j :=
          reducedCoord (d := d) i j η
        have hpU' :
            coordInv (d := d) i j (reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ U := by
          simpa [p, j] using hpU
        have hplus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (1 : Equiv.Perm (Fin (m + 1)))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi) p))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hplus_transfer
        have hminus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi)
                      (reducedSignFlip (d := d) i j p)))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hminus_transfer
        simpa [p, j] using
          reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic
            (d := d) OS lgc P U hU_open hU_sub p hpU'
            hrep hplus_transfer' hminus_transfer')

/-- Pointwise OS-I source-window packets supply the reduced local boundary-CLM
invariant.

Route guard: this is a correct Jost-local handoff once a Figure-2-4 source
patch with hull/cutoff data already contains the zero-center representative.
It is not, by itself, the arbitrary theorem-2 producer: membership in `P.V`
forces the representative into a full Jost patch, while theorem 2 only assumes
the selected adjacent difference is spacelike.  The arbitrary-support producer
therefore has to be direct reduced-normal EOW branch data, not this stronger
OS45 packet.

The proof uses the checked pointed OS412 source-window theorem to remove all
support-local window-selection bookkeeping before applying
`reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45SourceRepresentsOn_asymptotic`.
-/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_pointwise_OS412_sourceWindow_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hpoint :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ reducedSelectedSpacelike
            (d := d) i ⟨i.val + 1, hi⟩ →
          ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
              (d := d) hd (m + 1) i hi,
            ∃ _H : BHW.OS45BHWJostHullData (d := d) hd (m + 1) i hi P,
              ∃ _D : BHW.OS45Figure24SourceCutoffData P,
                coordInv (d := d) i ⟨i.val + 1, hi⟩
                    (reducedAdjacent_succ_ne i hi)
                    ((0 : SpacetimeDim d), p) ∈ P.V ∧
                Filter.Tendsto
                  (fun ε : ℝ =>
                    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                        (1 : Equiv.Perm (Fin (m + 1)))
                        (reducedNormalToOS45CommonEdgeComplexCLM
                          (d := d) i hi
                          (reducedNormalUpperCanonicalRay
                            (d := d) i hi p ε)) -
                      canonicalReducedBranch (d := d) OS lgc m ε
                        (reducedCoordInv (d := d)
                          i ⟨i.val + 1, hi⟩
                          (reducedAdjacent_succ_ne i hi) p))
                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                  (nhds 0) ∧
                Filter.Tendsto
                  (fun ε : ℝ =>
                    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                        (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                        (reducedNormalToOS45CommonEdgeComplexCLM
                          (d := d) i hi
                          (reducedNormalLowerCanonicalRay
                            (d := d) i hi p ε)) -
                      canonicalReducedBranch (d := d) OS lgc m ε
                        (reducedCoordInv (d := d)
                          i ⟨i.val + 1, hi⟩
                          (reducedAdjacent_succ_ne i hi)
                          (reducedSignFlip
                            (d := d) i ⟨i.val + 1, hi⟩ p)))
                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                  (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  refine
    reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45SourceRepresentsOn_asymptotic
      (d := d) hd OS lgc χ ?_
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let V : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i j
  refine
    ⟨V, by simpa [V] using isOpen_reducedSpacelikeSwapEdge (d := d) m i j,
      hφ_tsupport hξ, ?_⟩
  intro ψ hψ_compact hψ_tsupport η hη
  let p : ReducedSpace d m i j :=
    reducedCoord (d := d) i j η
  have hη_ts :
      η ∈ tsupport (ψ : NPointDomain d m → ℂ) :=
    subset_tsupport (ψ : NPointDomain d m → ℂ)
      (Function.mem_support.mpr hη)
  have hη_edge :
      η ∈ reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [V] using hψ_tsupport hη_ts
  have hp :
      p ∈ reducedSelectedSpacelike (d := d) i j := by
    exact
      (reducedCoord_mem_reducedSelectedSpacelike_iff
        (d := d) i j η).2 hη_edge
  rcases hpoint m i hi p (by simpa [p, j] using hp) with
    ⟨P, H, D, hpP, hplus_transfer, hminus_transfer⟩
  rcases
      H.exists_sourceWindow_sourceRepresentsZero_of_OS412_sourceSide
        OS lgc D hpP with
    ⟨U, hU_open, hU_sub, hpU, hrep⟩
  refine ⟨P, U, hU_open, hU_sub, ?_, hrep, ?_, ?_⟩
  · simpa [p, j] using hpU
  · simpa [p, j] using hplus_transfer
  · simpa [p, j] using hminus_transfer

/-- Pointwise OS-I source-window packets with moving source-side transfers supply
the reduced local boundary-CLM invariant.

This is the source-side version of
`reducedLocalAdjacentBoundaryCLMInvariant_of_pointwise_OS412_sourceWindow_asymptotic`:
the checked coordinate identities first turn the genuine OS45 moving-source
`extendF` transfers into the flat reduced-normal branch-transfer hypotheses, and
the existing source-window theorem then supplies the local CLM invariant. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_pointwise_OS412_sourceWindow_sourceSide_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hpoint :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ reducedSelectedSpacelike
            (d := d) i ⟨i.val + 1, hi⟩ →
          ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
              (d := d) hd (m + 1) i hi,
            ∃ _H : BHW.OS45BHWJostHullData (d := d) hd (m + 1) i hi P,
              ∃ _D : BHW.OS45Figure24SourceCutoffData P,
                coordInv (d := d) i ⟨i.val + 1, hi⟩
                    (reducedAdjacent_succ_ne i hi)
                    ((0 : SpacetimeDim d), p) ∈ P.V ∧
                Filter.Tendsto
                  (fun ε : ℝ =>
                    let ηsrc : BHW.OS45FlatCommonChartReal d (m + 1) :=
                      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                        (reducedNormalFlatCanonicalDirection (d := d) i hi)
                    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                        (reducedNormalFlattenCLE
                          (d := d) i ⟨i.val + 1, hi⟩ p)
                    let uε : NPointDomain d (m + 1) :=
                      (BHW.os45CommonEdgeFlatCLE d (m + 1)
                        (1 : Equiv.Perm (Fin (m + 1)))).symm
                          (x0 - ε • ηsrc)
                    BHW.extendF (bvt_F OS lgc (m + 1))
                        (BHW.os45FlatCommonChartSourceSide d (m + 1)
                          (1 : Equiv.Perm (Fin (m + 1)))
                          (1 : ℝ) ε ηsrc uε) -
                      canonicalReducedBranch (d := d) OS lgc m ε
                        (reducedCoordInv (d := d)
                          i ⟨i.val + 1, hi⟩
                          (reducedAdjacent_succ_ne i hi) p))
                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                  (nhds 0) ∧
                Filter.Tendsto
                  (fun ε : ℝ =>
                    let ηsrc : BHW.OS45FlatCommonChartReal d (m + 1) :=
                      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                        (reducedNormalFlatCanonicalDirection (d := d) i hi)
                    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                        (reducedNormalFlattenCLE
                          (d := d) i ⟨i.val + 1, hi⟩ p)
                    let uε : NPointDomain d (m + 1) :=
                      (BHW.os45CommonEdgeFlatCLE d (m + 1)
                        (1 : Equiv.Perm (Fin (m + 1)))).symm
                          (x0 + ε • ηsrc)
                    BHW.extendF (bvt_F OS lgc (m + 1))
                        (BHW.permAct (d := d)
                          (P.τ.symm *
                            (1 : Equiv.Perm (Fin (m + 1)))).symm
                          (BHW.os45FlatCommonChartSourceSide d (m + 1)
                            (1 : Equiv.Perm (Fin (m + 1)))
                            (-1 : ℝ) ε ηsrc uε)) -
                      canonicalReducedBranch (d := d) OS lgc m ε
                        (reducedCoordInv (d := d)
                          i ⟨i.val + 1, hi⟩
                          (reducedAdjacent_succ_ne i hi)
                          (reducedSignFlip
                            (d := d) i ⟨i.val + 1, hi⟩ p)))
                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                  (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  refine
    reducedLocalAdjacentBoundaryCLMInvariant_of_pointwise_OS412_sourceWindow_asymptotic
      (d := d) hd OS lgc χ ?_
  intro m i hi p hp
  rcases hpoint m i hi p hp with
    ⟨P, H, D, hpP, hplus_source_transfer, hminus_source_transfer⟩
  refine ⟨P, H, D, hpP, ?_, ?_⟩
  · refine Filter.Tendsto.congr' ?_ hplus_source_transfer
    filter_upwards with ε
    have hcoord :=
      reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        hcoord
    simpa using hsub.symm
  · refine Filter.Tendsto.congr' ?_ hminus_source_transfer
    filter_upwards with ε
    have hcoord :=
      reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc P p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        hcoord
    simpa using hsub.symm

/-- Local proof-local Hdiff germs on adjacent spacelike collars supply the
reduced local boundary-CLM invariant.

This is the Hdiff-carrier compatibility handoff.  It is useful once the
source-side branch transfer has already produced a local horizontal difference
germ, but it is not the OS-paper-facing input shape. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ η, ψ η ≠ 0 →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ U : Set (NPointDomain d (m + 1)),
                    ∃ Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ),
                      ∃ Hdiff :
                          (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
                        IsOpen U ∧ U ⊆ P.V ∧
                        coordInv (d := d) i ⟨i.val + 1, hi⟩
                            (reducedAdjacent_succ_ne i hi)
                            ((0 : SpacetimeDim d),
                              reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η) ∈ U ∧
                        IsOpen Ucx ∧ IsConnected Ucx ∧
                        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
                        (∀ u ∈ U,
                          (BHW.os45QuarterTurnCLE
                              (d := d) (n := m + 1)).symm
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx) ∧
                        DifferentiableOn ℂ Hdiff Ucx ∧
                        (∀ θ : SchwartzNPoint d (m + 1),
                          HasCompactSupport
                            (θ : NPointDomain d (m + 1) → ℂ) →
                          tsupport
                              (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
                          ∫ u : NPointDomain d (m + 1),
                            Hdiff (fun k => wickRotatePoint (u k)) *
                              θ u = 0) ∧
                        (∀ u ∈ U,
                          Hdiff
                            ((BHW.os45QuarterTurnCLE
                                (d := d) (n := m + 1)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := m + 1)
                                  (1 : Equiv.Perm (Fin (m + 1))) u))) =
                            BHW.os45PulledRealBranch
                                (d := d) (n := m + 1) OS lgc
                                (P.τ.symm *
                                  (1 : Equiv.Perm (Fin (m + 1))))
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1))) u)) -
                              BHW.os45PulledRealBranch
                                (d := d) (n := m + 1) OS lgc
                                (1 : Equiv.Perm (Fin (m + 1)))
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1))) u))) ∧
                        Filter.Tendsto
                          (fun ε : ℝ =>
                            BHW.os45FlatCommonChartBranch
                                d (m + 1) OS lgc
                                (1 : Equiv.Perm (Fin (m + 1)))
                                (reducedNormalToOS45CommonEdgeComplexCLM
                                  (d := d) i hi
                                  (reducedNormalUpperCanonicalRay
                                    (d := d) i hi
                                    (reducedCoord
                                      (d := d) i ⟨i.val + 1, hi⟩ η)
                                    ε)) -
                              canonicalReducedBranch
                                  (d := d) OS lgc m ε
                                  (reducedCoordInv (d := d)
                                    i ⟨i.val + 1, hi⟩
                                    (reducedAdjacent_succ_ne i hi)
                                    (reducedCoord
                                      (d := d) i ⟨i.val + 1, hi⟩ η)))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                            Filter ℝ)
                          (nhds 0) ∧
                        Filter.Tendsto
                          (fun ε : ℝ =>
                            BHW.os45FlatCommonChartBranch
                                d (m + 1) OS lgc
                                (P.τ.symm *
                                  (1 : Equiv.Perm (Fin (m + 1))))
                                (reducedNormalToOS45CommonEdgeComplexCLM
                                  (d := d) i hi
                                  (reducedNormalLowerCanonicalRay
                                    (d := d) i hi
                                    (reducedCoord
                                      (d := d) i ⟨i.val + 1, hi⟩ η)
                                    ε)) -
                              canonicalReducedBranch
                                  (d := d) OS lgc m ε
                                  (reducedCoordInv (d := d)
                                    i ⟨i.val + 1, hi⟩
                                    (reducedAdjacent_succ_ne i hi)
                                    (reducedSignFlip
                                      (d := d) i ⟨i.val + 1, hi⟩
                                      (reducedCoord
                                        (d := d) i ⟨i.val + 1, hi⟩ η))))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                            Filter ℝ)
                          (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  exact
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ (by
        intro m i hi φ hφ_compact hφ_tsupport ξ hξ
        rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
          ⟨V, hV_open, hξV, hVlocal⟩
        refine ⟨V, hV_open, hξV, ?_⟩
        intro ψ hψ_compact hψ_tsupport η hη
        rcases hVlocal ψ hψ_compact hψ_tsupport η hη with
          ⟨P, U, Ucx, Hdiff, hU_open, hU_sub, hpU, hUcx_open,
            hUcx_connected, hwick_mem, hcommon_mem, hHdiff_holo,
            hwick_pairing_zero, hcommon_trace, hplus_transfer,
            hminus_transfer⟩
        let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
        let p : ReducedSpace d m i j :=
          reducedCoord (d := d) i j η
        have hpU' :
            coordInv (d := d) i j (reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ U := by
          simpa [p, j] using hpU
        have hU_nonempty : U.Nonempty := ⟨_, hpU'⟩
        have hplus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (1 : Equiv.Perm (Fin (m + 1)))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi) p))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hplus_transfer
        have hminus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi)
                      (reducedSignFlip (d := d) i j p)))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hminus_transfer
        simpa [p, j] using
          reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_asymptotic
            (d := d) OS lgc P U hU_open hU_sub hU_nonempty
            p hpU' Ucx Hdiff hUcx_open hUcx_connected
            hwick_mem hcommon_mem hHdiff_holo hwick_pairing_zero
            hcommon_trace hplus_transfer' hminus_transfer')

/-- Local proof-local Hdiff germs with source-side moving transfers supply the
reduced local boundary-CLM invariant.

This is the Path-2 consumer for the Hdiff carrier: after the paper-facing
source-side branch transfer has been packaged as a local moving-source
horizontal difference germ, the checked reduced-normal coordinate bridge
converts it to the branch-difference/sign-flip handoff used by the reduced CLM
machinery. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_sourceSide_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ η, ψ η ≠ 0 →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ U : Set (NPointDomain d (m + 1)),
                    ∃ Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ),
                      ∃ Hdiff :
                          (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
                        IsOpen U ∧ U ⊆ P.V ∧
                        coordInv (d := d) i ⟨i.val + 1, hi⟩
                            (reducedAdjacent_succ_ne i hi)
                            ((0 : SpacetimeDim d),
                              reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η) ∈ U ∧
                        IsOpen Ucx ∧ IsConnected Ucx ∧
                        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
                        (∀ u ∈ U,
                          (BHW.os45QuarterTurnCLE
                              (d := d) (n := m + 1)).symm
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx) ∧
                        DifferentiableOn ℂ Hdiff Ucx ∧
                        (∀ θ : SchwartzNPoint d (m + 1),
                          HasCompactSupport
                            (θ : NPointDomain d (m + 1) → ℂ) →
                          tsupport
                              (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
                          ∫ u : NPointDomain d (m + 1),
                            Hdiff (fun k => wickRotatePoint (u k)) *
                              θ u = 0) ∧
                        (∀ u ∈ U,
                          Hdiff
                            ((BHW.os45QuarterTurnCLE
                                (d := d) (n := m + 1)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := m + 1)
                                  (1 : Equiv.Perm (Fin (m + 1))) u))) =
                            BHW.os45PulledRealBranch
                                (d := d) (n := m + 1) OS lgc
                                (P.τ.symm *
                                  (1 : Equiv.Perm (Fin (m + 1))))
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1))) u)) -
                              BHW.os45PulledRealBranch
                                (d := d) (n := m + 1) OS lgc
                                (1 : Equiv.Perm (Fin (m + 1)))
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1))) u))) ∧
                        Filter.Tendsto
                          (fun ε : ℝ =>
                            let p : ReducedSpace d m i ⟨i.val + 1, hi⟩ :=
                              reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η
                            let ηsrc : BHW.OS45FlatCommonChartReal d (m + 1) :=
                              reducedNormalToOS45CommonEdgeFlatCLM
                                (d := d) i hi
                                (reducedNormalFlatCanonicalDirection
                                  (d := d) i hi)
                            let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                              reducedNormalToOS45CommonEdgeFlatCLM
                                (d := d) i hi
                                (reducedNormalFlattenCLE
                                  (d := d) i ⟨i.val + 1, hi⟩ p)
                            let uε : NPointDomain d (m + 1) :=
                              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                (1 : Equiv.Perm (Fin (m + 1)))).symm
                                  (x0 - ε • ηsrc)
                            BHW.extendF (bvt_F OS lgc (m + 1))
                                (BHW.os45FlatCommonChartSourceSide
                                  d (m + 1)
                                  (1 : Equiv.Perm (Fin (m + 1)))
                                  (1 : ℝ) ε ηsrc uε) -
                              canonicalReducedBranch
                                  (d := d) OS lgc m ε
                                  (reducedCoordInv (d := d)
                                    i ⟨i.val + 1, hi⟩
                                    (reducedAdjacent_succ_ne i hi) p))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                            Filter ℝ)
                          (nhds 0) ∧
                        Filter.Tendsto
                          (fun ε : ℝ =>
                            let p : ReducedSpace d m i ⟨i.val + 1, hi⟩ :=
                              reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η
                            let ηsrc : BHW.OS45FlatCommonChartReal d (m + 1) :=
                              reducedNormalToOS45CommonEdgeFlatCLM
                                (d := d) i hi
                                (reducedNormalFlatCanonicalDirection
                                  (d := d) i hi)
                            let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                              reducedNormalToOS45CommonEdgeFlatCLM
                                (d := d) i hi
                                (reducedNormalFlattenCLE
                                  (d := d) i ⟨i.val + 1, hi⟩ p)
                            let uε : NPointDomain d (m + 1) :=
                              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                (1 : Equiv.Perm (Fin (m + 1)))).symm
                                  (x0 + ε • ηsrc)
                            BHW.extendF (bvt_F OS lgc (m + 1))
                                (BHW.permAct (d := d)
                                  (P.τ.symm *
                                    (1 : Equiv.Perm (Fin (m + 1)))).symm
                                  (BHW.os45FlatCommonChartSourceSide
                                    d (m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1)))
                                    (-1 : ℝ) ε ηsrc uε)) -
                              canonicalReducedBranch
                                  (d := d) OS lgc m ε
                                  (reducedCoordInv (d := d)
                                    i ⟨i.val + 1, hi⟩
                                    (reducedAdjacent_succ_ne i hi)
                                    (reducedSignFlip
                                      (d := d) i ⟨i.val + 1, hi⟩ p)))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                            Filter ℝ)
                          (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  exact
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ (by
        intro m i hi φ hφ_compact hφ_tsupport ξ hξ
        rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
          ⟨V, hV_open, hξV, hVlocal⟩
        refine ⟨V, hV_open, hξV, ?_⟩
        intro ψ hψ_compact hψ_tsupport η hη
        rcases hVlocal ψ hψ_compact hψ_tsupport η hη with
          ⟨P, U, Ucx, Hdiff, hU_open, hU_sub, hpU, hUcx_open,
            hUcx_connected, hwick_mem, hcommon_mem, hHdiff_holo,
            hwick_pairing_zero, hcommon_trace, hplus_source_transfer,
            hminus_source_transfer⟩
        let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
        let p : ReducedSpace d m i j :=
          reducedCoord (d := d) i j η
        have hpU' :
            coordInv (d := d) i j (reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ U := by
          simpa [p, j] using hpU
        have hU_nonempty : U.Nonempty := ⟨_, hpU'⟩
        have hplus_source_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                let ηsrc : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlatCanonicalDirection (d := d) i hi)
                let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlattenCLE (d := d) i j p)
                let uε : NPointDomain d (m + 1) :=
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm
                      (x0 - ε • ηsrc)
                BHW.extendF (bvt_F OS lgc (m + 1))
                    (BHW.os45FlatCommonChartSourceSide d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1)))
                      (1 : ℝ) ε ηsrc uε) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi) p))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hplus_source_transfer
        have hminus_source_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                let ηsrc : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlatCanonicalDirection (d := d) i hi)
                let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlattenCLE (d := d) i j p)
                let uε : NPointDomain d (m + 1) :=
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm
                      (x0 + ε • ηsrc)
                BHW.extendF (bvt_F OS lgc (m + 1))
                    (BHW.permAct (d := d)
                      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                      (BHW.os45FlatCommonChartSourceSide d (m + 1)
                        (1 : Equiv.Perm (Fin (m + 1)))
                        (-1 : ℝ) ε ηsrc uε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi)
                      (reducedSignFlip (d := d) i j p)))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hminus_source_transfer
        simpa [p, j] using
          reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_sourceSide_asymptotic
            (d := d) OS lgc P U hU_open hU_sub hU_nonempty
            p hpU' Ucx Hdiff hUcx_open hUcx_connected
            hwick_mem hcommon_mem hHdiff_holo hwick_pairing_zero
            hcommon_trace hplus_source_transfer' hminus_source_transfer')

/-- Local Hdiff germs with finite-height source transport supply the reduced
local boundary-CLM invariant directly at the integrated level.

This is the distributional Path-2 consumer: instead of asking for pointwise
reduced-normal sign-flip convergence at every point of a reduced test, it asks
for the local Hdiff/source-window data, support inclusion for the lifted
compact reduced test, and the two finite-height reduced-difference transport
facts for that lifted test.  The checked integrated Hdiff theorem then supplies
the exact branch-difference limit consumed by the local CLM layer. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_integrated_transport
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ _D : BHW.OS45Figure24SourceCutoffData P,
                    ∃ _Fred : BHW.ReducedBHWExtensionData
                        (d := d) (n := m + 1)
                        (bvt_F_reduced (d := d) OS lgc m),
                      ∃ U : Set (NPointDomain d (m + 1)),
                        ∃ Ucx : Set
                            (Fin (m + 1) → Fin (d + 1) → ℂ),
                          ∃ Hdiff :
                              (Fin (m + 1) →
                                Fin (d + 1) → ℂ) → ℂ,
                            ∃ Ωplus Ωminus :
                                Set (Fin (m + 1) →
                                  Fin (d + 1) → ℂ),
                              ∃ Usrc Ksrc :
                                  Set (NPointDomain d (m + 1)),
                                ∃ ηsrc :
                                    BHW.OS45FlatCommonChartReal d (m + 1),
                                  IsOpen U ∧ U.Nonempty ∧
                                  IsOpen Ucx ∧ IsConnected Ucx ∧
                                  (∀ u ∈ U,
                                    (fun k => wickRotatePoint (u k)) ∈
                                      Ucx) ∧
                                  (∀ u ∈ U,
                                    (BHW.os45QuarterTurnCLE
                                        (d := d) (n := m + 1)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := m + 1)
                                          (1 : Equiv.Perm (Fin (m + 1)))
                                          u)) ∈ Ucx) ∧
                                  DifferentiableOn ℂ Hdiff Ucx ∧
                                  (∀ θ : SchwartzNPoint d (m + 1),
                                    HasCompactSupport
                                      (θ : NPointDomain d (m + 1) → ℂ) →
                                    tsupport
                                        (θ :
                                          NPointDomain d (m + 1) → ℂ) ⊆ U →
                                    ∫ u : NPointDomain d (m + 1),
                                      Hdiff (fun k => wickRotatePoint (u k)) *
                                        θ u = 0) ∧
                                  (∀ u ∈ U,
                                    Hdiff
                                      ((BHW.os45QuarterTurnCLE
                                          (d := d) (n := m + 1)).symm
                                        (BHW.realEmbed
                                          (BHW.os45CommonEdgeRealPoint
                                            (d := d) (n := m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            u))) =
                                      BHW.os45PulledRealBranch
                                          (d := d) (n := m + 1) OS lgc
                                          (P.τ.symm *
                                            (1 : Equiv.Perm (Fin (m + 1))))
                                          (BHW.realEmbed
                                            (BHW.os45CommonEdgeRealPoint
                                              (d := d) (n := m + 1)
                                              (1 : Equiv.Perm (Fin (m + 1)))
                                              u)) -
                                        BHW.os45PulledRealBranch
                                          (d := d) (n := m + 1) OS lgc
                                          (1 : Equiv.Perm (Fin (m + 1)))
                                          (BHW.realEmbed
                                            (BHW.os45CommonEdgeRealPoint
                                              (d := d) (n := m + 1)
                                              (1 : Equiv.Perm (Fin (m + 1)))
                                              u))) ∧
                                  IsOpen Ωplus ∧ IsOpen Ωminus ∧
                                  ContinuousOn
                                    (fun z : Fin (m + 1) →
                                        Fin (d + 1) → ℂ =>
                                      BHW.extendF (bvt_F OS lgc (m + 1)) z)
                                    Ωplus ∧
                                  ContinuousOn
                                    (fun z : Fin (m + 1) →
                                        Fin (d + 1) → ℂ =>
                                      BHW.extendF (bvt_F OS lgc (m + 1))
                                        (BHW.permAct (d := d)
                                          (P.τ.symm *
                                            (1 : Equiv.Perm (Fin (m + 1)))).symm
                                          z))
                                    Ωminus ∧
                                  IsOpen Usrc ∧ Usrc ⊆ Ksrc ∧
                                  IsCompact Ksrc ∧ Ksrc ⊆ U ∧
                                  Usrc ⊆ P.V ∧
                                  (∀ u ∈ Ksrc,
                                    BHW.os45FlatCommonChartSourceSide
                                      d (m + 1)
                                      (1 : Equiv.Perm (Fin (m + 1)))
                                      (1 : ℝ) 0 ηsrc u ∈ Ωplus) ∧
                                  (∀ u ∈ Ksrc,
                                    BHW.os45FlatCommonChartSourceSide
                                      d (m + 1)
                                      (1 : Equiv.Perm (Fin (m + 1)))
                                      (-1 : ℝ) 0 ηsrc u ∈ Ωminus) ∧
                                  (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
                                      tsupport
                                        (ψ : NPointDomain d m → ℂ) ⊆
                                    Usrc ∧
                                  (∀ᶠ ε : ℝ in
                                    nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
                                    ∀ u,
                                      ((BHW.reducedTestLift m d
                                          (BHW.normalizedCutoffOfBump d).toSchwartz
                                          ψ : SchwartzNPoint d (m + 1)) :
                                        NPointDomain d (m + 1) → ℂ) u ≠ 0 →
                                        BHW.os45FlatCommonChartSourceSide
                                            d (m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            (1 : ℝ) ε ηsrc u ∈
                                          BHW.ExtendedTube d (m + 1) ∧
                                        BHW.reducedDiffMap (m + 1) d
                                            (BHW.os45FlatCommonChartSourceSide
                                              d (m + 1)
                                              (1 : Equiv.Perm (Fin (m + 1)))
                                              (1 : ℝ) ε ηsrc u) =
                                          fun k μ =>
                                            (BHW.reducedDiffMapReal
                                              (m + 1) d u k μ : ℂ) +
                                              ε *
                                                canonicalReducedDirectionC
                                                  (d := d) m k μ *
                                                Complex.I) ∧
                                  (∀ᶠ ε : ℝ in
                                    nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
                                    ∀ u,
                                      ((BHW.reducedTestLift m d
                                          (BHW.normalizedCutoffOfBump d).toSchwartz
                                          ψ : SchwartzNPoint d (m + 1)) :
                                        NPointDomain d (m + 1) → ℂ) u ≠ 0 →
                                        BHW.permAct (d := d)
                                            (P.τ.symm *
                                              (1 : Equiv.Perm
                                                (Fin (m + 1)))).symm
                                            (BHW.os45FlatCommonChartSourceSide
                                              d (m + 1)
                                              (1 : Equiv.Perm (Fin (m + 1)))
                                              (-1 : ℝ) ε ηsrc u) ∈
                                          BHW.ExtendedTube d (m + 1) ∧
                                        BHW.reducedDiffMap (m + 1) d
                                            (BHW.permAct (d := d)
                                              (P.τ.symm *
                                                (1 : Equiv.Perm
                                                  (Fin (m + 1)))).symm
                                              (BHW.os45FlatCommonChartSourceSide
                                                d (m + 1)
                                                (1 : Equiv.Perm (Fin (m + 1)))
                                                (-1 : ℝ) ε ηsrc u)) =
                                          fun k μ =>
                                            (BHW.reducedDiffMapReal
                                              (m + 1) d u k μ : ℂ) +
                                              ε *
                                                permutedCanonicalReducedDirectionC
                                                  (d := d) m
                                                  (Equiv.swap i
                                                    ⟨i.val + 1, hi⟩) k μ *
                                                Complex.I)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  refine
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_branchDifference
      (d := d) OS lgc χ ?_
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hVlocal⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_tsupport
  rcases hVlocal ψ hψ_compact hψ_tsupport with
    ⟨P, D, Fred, U, Ucx, Hdiff, Ωplus, Ωminus, Usrc, Ksrc, ηsrc,
      hU_open, hU_nonempty, hUcx_open, hUcx_connected, hwick_mem,
      hcommon_mem, hHdiff_holo, hwick_pairing_zero, hcommon_trace,
      hΩplus_open, hΩminus_open, hFplus_cont, hFminus_cont,
      hUsrc_open, hUsrc_sub_K, hKsrc, hKsrc_sub_U, hUsrcP,
      h0_plus, h0_minus, hredSupportU, hplus_transport, hminus_transport⟩
  have hliftU :
      tsupport
          ((BHW.reducedTestLift m d
              (BHW.normalizedCutoffOfBump d).toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc := by
    exact
      (reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
        (d := d) (m := m)
        (BHW.normalizedCutoffOfBump d).toSchwartz ψ).trans hredSupportU
  exact
    tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_transport
      (d := d) OS lgc D Fred U hU_open hU_nonempty Ucx Hdiff
      hUcx_open hUcx_connected hwick_mem hcommon_mem hHdiff_holo
      hwick_pairing_zero hcommon_trace hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hKsrc_sub_U
      hUsrcP ηsrc h0_plus h0_minus (BHW.normalizedCutoffOfBump d) ψ
      (BHW.normalizedCutoffOfBump_hasCompactSupport d) hψ_compact
      hliftU hplus_transport hminus_transport

/-- Local Hdiff germs with flat side-branch endpoint transport supply the reduced
local boundary-CLM invariant at the integrated level.

This is the corrected distributional Path-2 consumer after the source-side
transport-shape audit.  The moving-source Hdiff theorem proves the flat
side-branch difference limit; the two remaining hypotheses are the genuine
flat-to-reduced endpoint transport/reindexing limits for the compact reduced
test. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_integrated_flat_transport
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ _D : BHW.OS45Figure24SourceCutoffData P,
                    ∃ U : Set (NPointDomain d (m + 1)),
                      ∃ Ucx : Set
                          (Fin (m + 1) → Fin (d + 1) → ℂ),
                        ∃ Hdiff :
                            (Fin (m + 1) →
                              Fin (d + 1) → ℂ) → ℂ,
                          ∃ Ωplus Ωminus :
                              Set (Fin (m + 1) →
                                Fin (d + 1) → ℂ),
                            ∃ Usrc Ksrc :
                                Set (NPointDomain d (m + 1)),
                              ∃ ηsrc :
                                  BHW.OS45FlatCommonChartReal d (m + 1),
                                IsOpen U ∧ U.Nonempty ∧
                                IsOpen Ucx ∧ IsConnected Ucx ∧
                                (∀ u ∈ U,
                                  (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
                                (∀ u ∈ U,
                                  (BHW.os45QuarterTurnCLE
                                      (d := d) (n := m + 1)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := m + 1)
                                        (1 : Equiv.Perm (Fin (m + 1)))
                                        u)) ∈ Ucx) ∧
                                DifferentiableOn ℂ Hdiff Ucx ∧
                                (∀ θ : SchwartzNPoint d (m + 1),
                                  HasCompactSupport
                                    (θ : NPointDomain d (m + 1) → ℂ) →
                                  tsupport
                                      (θ :
                                        NPointDomain d (m + 1) → ℂ) ⊆ U →
                                  ∫ u : NPointDomain d (m + 1),
                                    Hdiff (fun k => wickRotatePoint (u k)) *
                                      θ u = 0) ∧
                                (∀ u ∈ U,
                                  Hdiff
                                    ((BHW.os45QuarterTurnCLE
                                        (d := d) (n := m + 1)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := m + 1)
                                          (1 : Equiv.Perm (Fin (m + 1)))
                                          u))) =
                                    BHW.os45PulledRealBranch
                                        (d := d) (n := m + 1) OS lgc
                                        (P.τ.symm *
                                          (1 : Equiv.Perm (Fin (m + 1))))
                                        (BHW.realEmbed
                                          (BHW.os45CommonEdgeRealPoint
                                            (d := d) (n := m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            u)) -
                                      BHW.os45PulledRealBranch
                                        (d := d) (n := m + 1) OS lgc
                                        (1 : Equiv.Perm (Fin (m + 1)))
                                        (BHW.realEmbed
                                          (BHW.os45CommonEdgeRealPoint
                                            (d := d) (n := m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            u))) ∧
                                IsOpen Ωplus ∧ IsOpen Ωminus ∧
                                ContinuousOn
                                  (fun z : Fin (m + 1) →
                                      Fin (d + 1) → ℂ =>
                                    BHW.extendF (bvt_F OS lgc (m + 1)) z)
                                  Ωplus ∧
                                ContinuousOn
                                  (fun z : Fin (m + 1) →
                                      Fin (d + 1) → ℂ =>
                                    BHW.extendF (bvt_F OS lgc (m + 1))
                                      (BHW.permAct (d := d)
                                        (P.τ.symm *
                                          (1 : Equiv.Perm (Fin (m + 1)))).symm
                                        z))
                                  Ωminus ∧
                                IsOpen Usrc ∧ Usrc ⊆ Ksrc ∧
                                IsCompact Ksrc ∧ Ksrc ⊆ U ∧
                                Usrc ⊆ P.V ∧
                                ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1) ∧
                                (∀ u ∈ Ksrc,
                                  BHW.os45FlatCommonChartSourceSide
                                    d (m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1)))
                                    (1 : ℝ) 0 ηsrc u ∈ Ωplus) ∧
                                (∀ u ∈ Ksrc,
                                  BHW.os45FlatCommonChartSourceSide
                                    d (m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1)))
                                    (-1 : ℝ) 0 ηsrc u ∈ Ωminus) ∧
                                (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
                                    tsupport
                                      (ψ : NPointDomain d m → ℂ) ⊆
                                  Usrc ∧
                                Filter.Tendsto
                                  (fun ε : ℝ =>
                                  (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
                                    BHW.os45FlatCommonChartBranch d (m + 1)
                                      OS lgc
                                      (1 : Equiv.Perm (Fin (m + 1)))
                                      (fun a =>
                                        (x a : ℂ) +
                                          ((((1 : ℝ) * ε) • ηsrc) a : ℂ) *
                                            Complex.I) *
                                      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                          (1 : Equiv.Perm
                                            (Fin (m + 1)))).symm)
                                        (BHW.reducedTestLift m d
                                          (BHW.normalizedCutoffOfBump d).toSchwartz
                                          ψ : SchwartzNPoint d (m + 1)) :
                                        SchwartzMap
                                          (BHW.OS45FlatCommonChartReal d (m + 1))
                                          ℂ) x) -
                                    (BHW.os45CommonEdgeFlatJacobianAbs
                                        (m + 1) : ℂ) *
                                      ∫ ξ : NPointDomain d m,
                                        canonicalReducedBranch
                                            (d := d) OS lgc m ε ξ *
                                          ψ ξ)
                                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                                    Filter ℝ)
                                  (nhds 0) ∧
                                Filter.Tendsto
                                  (fun ε : ℝ =>
                                  (∫ x : BHW.OS45FlatCommonChartReal d (m + 1),
                                    BHW.os45FlatCommonChartBranch d (m + 1)
                                      OS lgc
                                      (P.τ.symm *
                                        (1 : Equiv.Perm (Fin (m + 1))))
                                      (fun a =>
                                        (x a : ℂ) +
                                          ((((-1 : ℝ) * ε) • ηsrc) a : ℂ) *
                                            Complex.I) *
                                      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                                        (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                          (1 : Equiv.Perm
                                            (Fin (m + 1)))).symm)
                                        (BHW.reducedTestLift m d
                                          (BHW.normalizedCutoffOfBump d).toSchwartz
                                          ψ : SchwartzNPoint d (m + 1)) :
                                        SchwartzMap
                                          (BHW.OS45FlatCommonChartReal d (m + 1))
                                          ℂ) x) -
                                    (BHW.os45CommonEdgeFlatJacobianAbs
                                        (m + 1) : ℂ) *
                                      ∫ ξ : NPointDomain d m,
                                        canonicalAfterReducedSwapBranch
                                            (d := d) OS lgc m i
                                            ⟨i.val + 1, hi⟩ ε ξ *
                                          ψ ξ)
                                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                                    Filter ℝ)
                                  (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  refine
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_branchDifference
      (d := d) OS lgc χ ?_
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hVlocal⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_tsupport
  rcases hVlocal ψ hψ_compact hψ_tsupport with
    ⟨P, D, U, Ucx, Hdiff, Ωplus, Ωminus, Usrc, Ksrc, ηsrc,
      hU_open, hU_nonempty, hUcx_open, hUcx_connected, hwick_mem,
      hcommon_mem, hHdiff_holo, hwick_pairing_zero, hcommon_trace,
      hΩplus_open, hΩminus_open, hFplus_cont, hFminus_cont,
      hUsrc_open, hUsrc_sub_K, hKsrc, hKsrc_sub_U, hUsrcP, hηsrcC,
      h0_plus, h0_minus, hredSupportU, hplus_flat_transport,
      hminus_flat_transport⟩
  have hliftU :
      tsupport
          ((BHW.reducedTestLift m d
              (BHW.normalizedCutoffOfBump d).toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc := by
    exact
      (reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
        (d := d) (m := m)
        (BHW.normalizedCutoffOfBump d).toSchwartz ψ).trans hredSupportU
  exact
    tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_flat_transport
      (d := d) OS lgc D U hU_open hU_nonempty Ucx Hdiff
      hUcx_open hUcx_connected hwick_mem hcommon_mem hHdiff_holo
      hwick_pairing_zero hcommon_trace hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hKsrc_sub_U
      hUsrcP ηsrc hηsrcC h0_plus h0_minus
      (BHW.normalizedCutoffOfBump d) ψ
      (BHW.normalizedCutoffOfBump_hasCompactSupport d) hψ_compact
      hliftU hplus_flat_transport hminus_flat_transport

/-- Local Hdiff germs with shifted source-side endpoint transport supply the
reduced local boundary-CLM invariant at the integrated level.

This is the source-side version of the corrected Path-2 consumer: the
coordinate/Jacobian bridge to the fixed flat side is discharged inside the
proof, so the local hypotheses name the remaining analytic DCT/reindexing
endpoint limits directly on the moving source-side path. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_integrated_sourceSide_shifted_transport
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ _D : BHW.OS45Figure24SourceCutoffData P,
                    ∃ U : Set (NPointDomain d (m + 1)),
                      ∃ Ucx : Set
                          (Fin (m + 1) → Fin (d + 1) → ℂ),
                        ∃ Hdiff :
                            (Fin (m + 1) →
                              Fin (d + 1) → ℂ) → ℂ,
                          ∃ Ωplus Ωminus :
                              Set (Fin (m + 1) →
                                Fin (d + 1) → ℂ),
                            ∃ Usrc Ksrc :
                                Set (NPointDomain d (m + 1)),
                              ∃ ηsrc :
                                  BHW.OS45FlatCommonChartReal d (m + 1),
                                IsOpen U ∧ U.Nonempty ∧
                                IsOpen Ucx ∧ IsConnected Ucx ∧
                                (∀ u ∈ U,
                                  (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
                                (∀ u ∈ U,
                                  (BHW.os45QuarterTurnCLE
                                      (d := d) (n := m + 1)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := m + 1)
                                        (1 : Equiv.Perm (Fin (m + 1)))
                                        u)) ∈ Ucx) ∧
                                DifferentiableOn ℂ Hdiff Ucx ∧
                                (∀ θ : SchwartzNPoint d (m + 1),
                                  HasCompactSupport
                                    (θ : NPointDomain d (m + 1) → ℂ) →
                                  tsupport
                                      (θ :
                                        NPointDomain d (m + 1) → ℂ) ⊆ U →
                                  ∫ u : NPointDomain d (m + 1),
                                    Hdiff (fun k => wickRotatePoint (u k)) *
                                      θ u = 0) ∧
                                (∀ u ∈ U,
                                  Hdiff
                                    ((BHW.os45QuarterTurnCLE
                                        (d := d) (n := m + 1)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := m + 1)
                                          (1 : Equiv.Perm (Fin (m + 1)))
                                          u))) =
                                    BHW.os45PulledRealBranch
                                        (d := d) (n := m + 1) OS lgc
                                        (P.τ.symm *
                                          (1 : Equiv.Perm (Fin (m + 1))))
                                        (BHW.realEmbed
                                          (BHW.os45CommonEdgeRealPoint
                                            (d := d) (n := m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            u)) -
                                      BHW.os45PulledRealBranch
                                        (d := d) (n := m + 1) OS lgc
                                        (1 : Equiv.Perm (Fin (m + 1)))
                                        (BHW.realEmbed
                                          (BHW.os45CommonEdgeRealPoint
                                            (d := d) (n := m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            u))) ∧
                                IsOpen Ωplus ∧ IsOpen Ωminus ∧
                                ContinuousOn
                                  (fun z : Fin (m + 1) →
                                      Fin (d + 1) → ℂ =>
                                    BHW.extendF (bvt_F OS lgc (m + 1)) z)
                                  Ωplus ∧
                                ContinuousOn
                                  (fun z : Fin (m + 1) →
                                      Fin (d + 1) → ℂ =>
                                    BHW.extendF (bvt_F OS lgc (m + 1))
                                      (BHW.permAct (d := d)
                                        (P.τ.symm *
                                          (1 : Equiv.Perm (Fin (m + 1)))).symm
                                        z))
                                  Ωminus ∧
                                IsOpen Usrc ∧ Usrc ⊆ Ksrc ∧
                                IsCompact Ksrc ∧ Ksrc ⊆ U ∧
                                Usrc ⊆ P.V ∧
                                ηsrc ∈ BHW.os45FlatCommonChartCone d (m + 1) ∧
                                (∀ u ∈ Ksrc,
                                  BHW.os45FlatCommonChartSourceSide
                                    d (m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1)))
                                    (1 : ℝ) 0 ηsrc u ∈ Ωplus) ∧
                                (∀ u ∈ Ksrc,
                                  BHW.os45FlatCommonChartSourceSide
                                    d (m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1)))
                                    (-1 : ℝ) 0 ηsrc u ∈ Ωminus) ∧
                                (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
                                    tsupport
                                      (ψ : NPointDomain d m → ℂ) ⊆
                                  Usrc ∧
                                Filter.Tendsto
                                  (fun ε : ℝ =>
                                  (((∫ u : NPointDomain d (m + 1),
                                      BHW.extendF (bvt_F OS lgc (m + 1))
                                        (BHW.permAct (d := d)
                                          (1 : Equiv.Perm (Fin (m + 1))).symm
                                          (BHW.os45FlatCommonChartSourceSide
                                            d (m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            (1 : ℝ) ε ηsrc u)) *
                                        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                                          (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                            (1 : Equiv.Perm
                                              (Fin (m + 1)))).symm)
                                          (BHW.reducedTestLift m d
                                            (BHW.normalizedCutoffOfBump d).toSchwartz
                                            ψ : SchwartzNPoint d (m + 1)) :
                                          SchwartzMap
                                            (BHW.OS45FlatCommonChartReal d (m + 1))
                                            ℂ)
                                          (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1))) u +
                                              (((1 : ℝ) * ε) • ηsrc))) -
                                    ∫ u : NPointDomain d (m + 1),
                                      BHW.extendF (bvt_F OS lgc (m + 1))
                                        (BHW.permAct (d := d)
                                          (P.τ.symm *
                                            (1 : Equiv.Perm (Fin (m + 1)))).symm
                                          (BHW.os45FlatCommonChartSourceSide
                                            d (m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1)))
                                            (-1 : ℝ) ε ηsrc u)) *
                                        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                                          (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                            (1 : Equiv.Perm
                                              (Fin (m + 1)))).symm)
                                          (BHW.reducedTestLift m d
                                            (BHW.normalizedCutoffOfBump d).toSchwartz
                                            ψ : SchwartzNPoint d (m + 1)) :
                                          SchwartzMap
                                            (BHW.OS45FlatCommonChartReal d (m + 1))
                                            ℂ)
                                          (BHW.os45CommonEdgeFlatCLE d (m + 1)
                                            (1 : Equiv.Perm (Fin (m + 1))) u +
                                              (((-1 : ℝ) * ε) • ηsrc))) -
                                    ((∫ ξ : NPointDomain d m,
                                        canonicalReducedBranch
                                            (d := d) OS lgc m ε ξ *
                                          ψ ξ) -
                                      ∫ ξ : NPointDomain d m,
                                        canonicalAfterReducedSwapBranch
                                            (d := d) OS lgc m i
                                            ⟨i.val + 1, hi⟩ ε ξ *
                                          ψ ξ)))
                                  (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                                    Filter ℝ)
                                  (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  refine
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_branchDifference
      (d := d) OS lgc χ ?_
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hVlocal⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_tsupport
  rcases hVlocal ψ hψ_compact hψ_tsupport with
    ⟨P, D, U, Ucx, Hdiff, Ωplus, Ωminus, Usrc, Ksrc, ηsrc,
      hU_open, hU_nonempty, hUcx_open, hUcx_connected, hwick_mem,
      hcommon_mem, hHdiff_holo, hwick_pairing_zero, hcommon_trace,
      hΩplus_open, hΩminus_open, hFplus_cont, hFminus_cont,
      hUsrc_open, hUsrc_sub_K, hKsrc, hKsrc_sub_U, hUsrcP, hηsrcC,
      h0_plus, h0_minus, htail⟩
  rcases htail with
    ⟨hredSupportU, hsource_reduced_transport⟩
  have hliftU :
      tsupport
          ((BHW.reducedTestLift m d
              (BHW.normalizedCutoffOfBump d).toSchwartz ψ :
              SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ) ⊆ Usrc := by
    exact
      (reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
        (d := d) (m := m)
        (BHW.normalizedCutoffOfBump d).toSchwartz ψ).trans hredSupportU
  exact
    tendsto_canonicalAfterSwapBranch_difference_zero_reducedTestLift_of_HdiffGerm_and_sourceSide_shifted_transport
      (d := d) OS lgc D U hU_open hU_nonempty Ucx Hdiff
      hUcx_open hUcx_connected hwick_mem hcommon_mem hHdiff_holo
      hwick_pairing_zero hcommon_trace hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc hKsrc_sub_U
      hUsrcP ηsrc hηsrcC h0_plus h0_minus
      (BHW.normalizedCutoffOfBump d) ψ
      (BHW.normalizedCutoffOfBump_hasCompactSupport d) hψ_compact
      hliftU hsource_reduced_transport

/-- Pull a Ruelle-overlap equality seed back to a reduced-normal branch packet.

The complex window `W` is the open connected seed produced by the
Jost/Ruelle overlap argument.  This theorem constructs the local source collar
by pulling `W` back along the OS45 common-edge chart, uses the existing Ruelle
overlap theorem to obtain source common-edge equality there, and then applies
the local reduced-normal OS45 packet constructor. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_OS45RuelleOverlapSeed
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    {W : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d), p)))) ∈ W)
    (heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W)
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let zc : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ := fun u =>
    (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ0 u))
  let U : Set (NPointDomain d (m + 1)) := P.V ∩ zc ⁻¹' W
  have hzc_cont : Continuous zc := by
    exact
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm.continuous.comp
        (by
          simpa [σ0] using
            BHW.continuous_realEmbed_os45CommonEdgeRealPoint
              (d := d) (n := m + 1) σ0)
  have hU_open : IsOpen U := by
    exact P.V_open.inter (hW_open.preimage hzc_cont)
  have hU_sub : U ⊆ P.V := by
    intro u hu
    exact hu.1
  have hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U := by
    exact ⟨hpP, by simpa [U, zc, σ0] using hzW⟩
  have hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    exact
      BHW.os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
        (d := d) hd OS lgc (P := P) (U := U) (Ucx := W)
        (by
          intro u hu
          simpa [zc, σ0, U] using hu.2)
        heq
  exact
    reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatchOn
      (d := d) OS lgc P U hU_open hU_sub p hpU hsource
      hplus_rep hminus_rep

/-- Local edge pairing supplies the local overlap seed needed by the
reduced-normal OS45 branch packet.

This is the local, non-selected version of the reduced-normal handoff: the
real-edge pairing on `Vedge` produces source common-edge equality on the
source patch, the checked flat common-chart bridge supplies a Ruelle overlap
seed, and the existing reduced-normal pullback builds the canonical-ray EOW
packet.  The two canonical-ray representation formulas remain explicit because
they are the genuine OS-I `(4.12)`--`(4.14)` source-side transfer leaf. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_localEdgePairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) P.τ z ∈
              BHW.ExtendedTube d (m + 1)})
    (Vedge : Set (NPointDomain d (m + 1)))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d (m + 1))
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈
          BHW.ExtendedTube d (m + 1))
    (hPairing :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (BHW.realEmbed x) * φ x)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  have hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) P.V :=
    BHW.os45_sourceCommonEdge_representsZero_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing (Usrc := P.V) (by intro u hu; exact hu)
  let hSeed :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
      (d := d) hd OS lgc (P := P)
      P.V_open (by intro u hu; exact hu) hrep
      ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalCanonicalRayEOWBranchDataOn_of_OS45RuelleOverlapSeed
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_rep hminus_rep

/-- Local edge pairing supplies the asymptotic reduced-normal sign-flip
comparison.

This is the local-edge analogue of
`reducedNormalCanonicalRayEOWBranchDataOn_of_localEdgePairing`, with the OS-I
side-to-canonical ray comparison stated as asymptotic transfer. -/
theorem reducedNormalSignFlip_pointwise_of_localEdgePairing_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) P.τ z ∈
              BHW.ExtendedTube d (m + 1)})
    (Vedge : Set (NPointDomain d (m + 1)))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d (m + 1))
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈
          BHW.ExtendedTube d (m + 1))
    (hPairing :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (BHW.realEmbed x) * φ x)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  have hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) P.V :=
    BHW.os45_sourceCommonEdge_representsZero_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing (Usrc := P.V) (by intro u hu; exact hu)
  let hSeed :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
      (d := d) hd OS lgc (P := P)
      P.V_open (by intro u hu; exact hu) hrep
      ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_transfer hminus_transfer

/-- Selected Jost/Ruelle data supplies the local overlap seed needed by the
reduced-normal OS45 branch packet.

This is the support-point version of the OS I Section 4.5 handoff: the
selected distributional Jost anchor and adjacent ET-overlap connectedness
produce the local Ruelle `EqOn` seed at the source point corresponding to the
reduced-normal real edge.  The remaining visible assumptions are the honest
point-local Figure-2-4 membership and the two canonical-ray representation
formulas. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_selectedJostData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      ∀ (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc (m + 1))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  let Uruelle : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    BHW.ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_sub :
      Uruelle ⊆ BHW.ruelleOverlapDomain d (m + 1) P.τ := by
    intro z hz
    exact hz
  have hUruelle_open : IsOpen Uruelle := by
    simpa [Uruelle] using BHW.isOpen_ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_connected : IsConnected Uruelle := by
    have hconn := hOverlap i hi
    simpa [Uruelle, BHW.ruelleOverlapDomain,
      BHW.permutedExtendedTubeSector, P.τ_eq, BHW.permAct] using hconn
  have hcommon_mem :
      ∀ u ∈ P.V,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Uruelle := by
    intro u hu
    change
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈
        BHW.ruelleOverlapDomain d (m + 1) P.τ
    exact
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := m + 1) (hd := hd) (P := P)
        (subset_closure hu)
  let hSeed :=
    BHW.os45_flat_seed_of_selectedJostData
      (d := d) hd OS lgc (P := P) hOverlap hData
      (Usrc := P.V) P.V_open (by intro u hu; exact hu)
      (Ucx := Uruelle) hUruelle_sub hUruelle_open hUruelle_connected
      hcommon_mem ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalCanonicalRayEOWBranchDataOn_of_OS45RuelleOverlapSeed
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_rep hminus_rep

/-- Selected Jost/Ruelle data supplies the reduced-normal pointwise sign-flip
limit when the OS45 side branches are only asymptotic to the two canonical
reduced rays.

This is the selected-data analogue of
`reducedNormalSignFlip_pointwise_of_localEdgePairing_asymptotic`: the selected
anchor and adjacent ET-overlap connectedness produce the local Ruelle `EqOn`
seed, while the OS-I `(4.14)` side-to-canonical ray comparisons remain in their
natural asymptotic form. -/
theorem reducedNormalSignFlip_pointwise_of_selectedJostData_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      ∀ (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc (m + 1))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  let Uruelle : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    BHW.ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_sub :
      Uruelle ⊆ BHW.ruelleOverlapDomain d (m + 1) P.τ := by
    intro z hz
    exact hz
  have hUruelle_open : IsOpen Uruelle := by
    simpa [Uruelle] using BHW.isOpen_ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_connected : IsConnected Uruelle := by
    have hconn := hOverlap i hi
    simpa [Uruelle, BHW.ruelleOverlapDomain,
      BHW.permutedExtendedTubeSector, P.τ_eq, BHW.permAct] using hconn
  have hcommon_mem :
      ∀ u ∈ P.V,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Uruelle := by
    intro u hu
    change
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈
        BHW.ruelleOverlapDomain d (m + 1) P.τ
    exact
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := m + 1) (hd := hd) (P := P)
        (subset_closure hu)
  let hSeed :=
    BHW.os45_flat_seed_of_selectedJostData
      (d := d) hd OS lgc (P := P) hOverlap hData
      (Usrc := P.V) P.V_open (by intro u hu; exact hu)
      (Ucx := Uruelle) hUruelle_sub hUruelle_open hUruelle_connected
      hcommon_mem ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_transfer hminus_transfer

/-- Pull an OS45 Figure-2-4 branch packet back to a reduced-normal collar.

This discharges the topology, holomorphy, and common-boundary-value fields of
`ReducedNormalCanonicalRayEOWBranchDataOn`.  The assumptions left visible are
exactly the remaining Jost/Ruelle payload: source common-edge equality and the
two canonical-ray representation formulas after the OS45 chart pullback. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hsource :
      ∀ u ∈ P.V,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  let q : ℕ :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let σadj : Equiv.Perm (Fin (m + 1)) := P.τ.symm * σ0
  let L : SCV.ComplexChartSpace q →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let E : Set (Fin q → ℝ) :=
    reducedNormalOS45SourcePatchPreimage (d := d) i hi P
  let Ωplus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σ0
  let Ωminus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σadj
  let Fplus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ0 (L z)
  let Fminus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σadj (L z)
  let bv : (Fin q → ℝ) → ℂ := fun x => Fplus (SCV.realEmbed x)
  have hE_open : IsOpen E := by
    simpa [E] using
      isOpen_reducedNormalOS45SourcePatchPreimage (d := d) i hi P
  have hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E := by
    simpa [E] using
      (reducedNormalFlatten_mem_reducedNormalOS45SourcePatchPreimage_iff
        (d := d) i hi P p).2 hpP
  have hΩplus_open : IsOpen Ωplus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σ0).preimage
        L.continuous
  have hΩminus_open : IsOpen Ωminus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σadj).preimage
        L.continuous
  have hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σ0 := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id
          (d := d) hd (P := P) (u := x) (by simpa [E] using hx)
    simpa [Ωplus] using hxΩ
  have hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σadj := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σadj, σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent
          (d := d) hd (P := P) (u := x) (by simpa [E] using hx)
    simpa [Ωminus] using hxΩ
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σ0).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σadj).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    have hreal :
        Continuous (fun x : Fin q → ℝ => SCV.realEmbed x) := by
      simpa [SCV.realEmbed] using
        (continuous_pi fun a =>
          Complex.continuous_ofReal.comp (continuous_apply a))
    exact hFplus_diff.continuousOn.comp hreal.continuousOn hplus0
  have htrace :
      ∀ x ∈ E, Fminus (SCV.realEmbed x) = Fplus (SCV.realEmbed x) := by
    intro x hx
    have hedge :
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x ∈
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P σ0 := by
      exact
        (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
          (d := d) i hi P x).2 (by simpa [E] using hx)
    have hflat :=
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eq
        (d := d) hd OS lgc (P := P) hsource
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) hedge
    have hL :
        L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) := by
      simpa [L, q] using
        reducedNormalToOS45CommonEdgeComplexCLM_realEmbed (d := d) i hi x
    simpa [Fplus, Fminus, σadj, σ0, hL] using hflat
  have hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    simpa [bv] using
      (hFplus_diff.continuousOn.continuousWithinAt
        (hplus0 x hx)).tendsto
  have hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hlim :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) :=
      (hFminus_diff.continuousOn.continuousWithinAt
        (hminus0 x hx)).tendsto
    simpa [bv, htrace x hx] using hlim
  have hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  refine
    ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem
      (d := d) (OS := OS) (lgc := lgc) (p := p)
      E hE_open hpE Ωplus Ωminus Set.univ
      hΩplus_open hΩminus_open isOpen_univ convex_univ Set.univ_nonempty
      hplus0 hminus0 Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv hplus_nhds hminus_nhds ?_ ?_
  · simpa [Fplus, L, σ0, q] using hplus_rep
  · simpa [Fminus, L, σadj, σ0, q] using hminus_rep

omit [NeZero d] in
/-- The cone-valid absolute OS45 height and the reduced-normal canonical height
have the same adjacent common-edge differences.  Equivalently, their mismatch
is only a common source translation, which disappears after quotienting by
reduced differences. -/
theorem os45CommonEdgeRealPoint_canonicalForward_diff_eq_reducedNormalCanonical
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (k : Fin (m + 1 - 1)) (μ : Fin (d + 1)) :
    BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (canonicalForwardConeDirection (d := d) (m + 1))
        ⟨k.val + 1, by omega⟩ μ -
      BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (canonicalForwardConeDirection (d := d) (m + 1))
        ⟨k.val, by omega⟩ μ =
    BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalAbsoluteSectionCLM (d := d) i hi
          (reducedNormalFlatCanonicalDirection (d := d) i hi))
        ⟨k.val + 1, by omega⟩ μ -
      BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalAbsoluteSectionCLM (d := d) i hi
          (reducedNormalFlatCanonicalDirection (d := d) i hi))
        ⟨k.val, by omega⟩ μ := by
  have hred :
      reducedNormalAbsoluteSectionCLM (d := d) i hi
            (reducedNormalFlatCanonicalDirection (d := d) i hi)
            ⟨k.val + 1, by omega⟩ μ -
          reducedNormalAbsoluteSectionCLM (d := d) i hi
            (reducedNormalFlatCanonicalDirection (d := d) i hi)
            ⟨k.val, by omega⟩ μ =
        canonicalReducedDirection (d := d) m k μ := by
    have hleft :=
      reducedCoordInv_left (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        (canonicalReducedDirection (d := d) m)
    have h := congrFun (congrFun hleft k) μ
    simpa [reducedNormalAbsoluteSectionCLM_apply,
      reducedNormalFlatCanonicalDirection, reducedCoordInv, reducedCoordCLE,
      BHW.reducedDiffMapReal_apply] using h
  have hcan :
      canonicalForwardConeDirection (d := d) (m + 1)
            ⟨k.val + 1, by omega⟩ μ -
          canonicalForwardConeDirection (d := d) (m + 1)
            ⟨k.val, by omega⟩ μ =
        canonicalReducedDirection (d := d) m k μ := by
    by_cases hμ : μ = (0 : Fin (d + 1))
    · subst μ
      simp [canonicalForwardConeDirection, canonicalReducedDirection,
        BHW.safeBasepointVec]
    · simp [canonicalForwardConeDirection, canonicalReducedDirection,
        BHW.safeBasepointVec, hμ]
  by_cases hμ : μ = (0 : Fin (d + 1))
  · subst μ
    simp [BHW.os45CommonEdgeRealPoint]
    calc
      canonicalForwardConeDirection (d := d) (m + 1)
              ⟨k.val + 1, by omega⟩ 0 / 2 -
            canonicalForwardConeDirection (d := d) (m + 1)
              ⟨k.val, by omega⟩ 0 / 2 =
          (canonicalForwardConeDirection (d := d) (m + 1)
                ⟨k.val + 1, by omega⟩ 0 -
              canonicalForwardConeDirection (d := d) (m + 1)
                ⟨k.val, by omega⟩ 0) / 2 := by ring
      _ = canonicalReducedDirection (d := d) m k 0 / 2 := by
        rw [hcan]
      _ =
          (reducedNormalAbsoluteSectionCLM (d := d) i hi
                (reducedNormalFlatCanonicalDirection (d := d) i hi)
                ⟨k.val + 1, by omega⟩ 0 -
              reducedNormalAbsoluteSectionCLM (d := d) i hi
                (reducedNormalFlatCanonicalDirection (d := d) i hi)
                ⟨k.val, by omega⟩ 0) / 2 := by
        rw [hred]
      _ =
          reducedNormalAbsoluteSectionCLM (d := d) i hi
                (reducedNormalFlatCanonicalDirection (d := d) i hi)
                ⟨k.val + 1, by omega⟩ 0 / 2 -
          reducedNormalAbsoluteSectionCLM (d := d) i hi
                (reducedNormalFlatCanonicalDirection (d := d) i hi)
                ⟨k.val, by omega⟩ 0 / 2 := by ring
  · simpa [BHW.os45CommonEdgeRealPoint, hμ] using hcan.trans hred.symm

set_option maxHeartbeats 1200000 in
/-- Replacing the reduced-normal side-height by the cone-valid canonical OS45
height preserves the upper moving source-side ray after quotienting by reduced
differences.

This is the coordinate bridge left after selecting the correct side-height for
OS-I Section 4.5.  Its target is still the OS45 quarter-turned absolute
reduced-normal ray; it is not a direct rewrite to the ordinary canonical
reduced PET approach.  The remaining branch-transfer leaf is the analytic
height/source-side comparison that removes this OS45 normalization. -/
theorem reducedDiffMap_coneHeight_sourceSide_eq_upperCanonicalRay
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (canonicalForwardConeDirection (d := d) (m + 1))
    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
    let uε : NPointDomain d (m + 1) :=
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • ηc)
    BHW.reducedDiffMap (m + 1) d
        (BHW.permAct (d := d) σ
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε)) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.permAct (d := d) σ
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.unflattenCfg (m + 1) d
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε))))) := by
  intro ηc x0 uε
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let zsrc : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.os45FlatCommonChartSourceSide d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε
  let zcan : Fin (m + 1) → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
      (BHW.unflattenCfg (m + 1) d
        (reducedNormalToOS45CommonEdgeComplexCLM
          (d := d) i hi
          (reducedNormalUpperCanonicalRay (d := d) i hi p ε)))
  have hbase :
      BHW.reducedDiffMap (m + 1) d zsrc =
        BHW.reducedDiffMap (m + 1) d zcan := by
    rw [show zcan =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.unflattenCfg (m + 1) d
            (fun a =>
              (x0 a : ℂ) +
                (ε : ℂ) *
                  (reducedNormalToOS45CommonEdgeFlatCLM
                    (d := d) i hi
                    (reducedNormalFlatCanonicalDirection (d := d) i hi) a : ℂ) *
                  Complex.I)) by
      simp [zcan, x0, reducedNormalToOS45CommonEdgeComplexCLM_upperRay]]
    ext k μ
    rw [BHW.reducedDiffMap_eq_successive_differences,
      BHW.reducedDiffMap_eq_successive_differences]
    have hdiv_succ :
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).divNat =
          (⟨k.val + 1, by omega⟩ : Fin (m + 1)) := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).1 =
          (⟨k.val + 1, by omega⟩ : Fin (m + 1))
      simp
    have hmod_succ :
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).2 = μ
      simp
    have hdiv_curr :
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).divNat =
          (⟨k.val, by omega⟩ : Fin (m + 1)) := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).1 =
          (⟨k.val, by omega⟩ : Fin (m + 1))
      simp
    have hmod_curr :
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).2 = μ
      simp
    have hη :
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))
            ⟨k.val + 1, by omega⟩ μ : ℂ) -
          BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))
            ⟨k.val, by omega⟩ μ =
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalAbsoluteSectionCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi))
            ⟨k.val + 1, by omega⟩ μ : ℂ) -
          BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalAbsoluteSectionCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi))
            ⟨k.val, by omega⟩ μ := by
      exact_mod_cast
        os45CommonEdgeRealPoint_canonicalForward_diff_eq_reducedNormalCanonical
          (d := d) (i := i) (hi := hi) k μ
    by_cases hμ : μ = (0 : Fin (d + 1))
    · subst μ
      simp [BHW.os45CommonEdgeRealPoint] at hη
      simp [zsrc, BHW.os45FlatCommonChartSourceSide, uε, x0, ηc,
        BHW.unflattenCfg, BHW.os45QuarterTurnCLE_symm_apply,
        BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
        flattenCLEquivReal_apply, sub_eq_add_neg, Pi.add_apply,
        Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hdiv_succ, hmod_succ,
        hdiv_curr, hmod_curr]
      ring_nf at hη ⊢
      linear_combination ((Complex.I + Complex.I ^ 2) * (ε : ℂ)) * hη
    · simp [zsrc, BHW.os45FlatCommonChartSourceSide, uε, x0, ηc,
        BHW.unflattenCfg, BHW.os45QuarterTurnCLE_symm_apply,
        BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
        flattenCLEquivReal_apply, sub_eq_add_neg, Pi.add_apply,
        Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hμ, hdiv_succ,
        hmod_succ, hdiv_curr, hmod_curr]
      simp [BHW.os45CommonEdgeRealPoint, hμ] at hη
      ring_nf at hη ⊢
      linear_combination (Complex.I * (ε : ℂ)) * hη
  calc
    BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) σ zsrc) =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d zsrc) := by
      simpa [zsrc, BHW.permAct] using
        (BHW.permOnReducedDiff_reducedDiffMap
          (d := d) (n := m + 1) σ zsrc).symm
    _ = BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d zcan) := by
      rw [hbase]
    _ = BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) σ zcan) := by
      simpa [zcan, BHW.permAct] using
        (BHW.permOnReducedDiff_reducedDiffMap
          (d := d) (n := m + 1) σ zcan)

set_option maxHeartbeats 1200000 in
/-- Replacing the reduced-normal side-height by the cone-valid canonical OS45
height preserves the lower moving source-side ray after quotienting by reduced
differences, including after the selected adjacent branch permutation.

As in the upper case, the target is the OS45 quarter-turned absolute lower
reduced-normal ray.  It should not be used as a direct adjacent positive-PET
reduced-difference normal form. -/
theorem reducedDiffMap_coneHeight_sourceSide_eq_lowerCanonicalRay
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (canonicalForwardConeDirection (d := d) (m + 1))
    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
    let uε : NPointDomain d (m + 1) :=
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • ηc)
    BHW.reducedDiffMap (m + 1) d
        (BHW.permAct (d := d) σ
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε)) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.permAct (d := d) σ
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.unflattenCfg (m + 1) d
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε))))) := by
  intro ηc x0 uε
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let zsrc : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.os45FlatCommonChartSourceSide d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε
  let zcan : Fin (m + 1) → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
      (BHW.unflattenCfg (m + 1) d
        (reducedNormalToOS45CommonEdgeComplexCLM
          (d := d) i hi
          (reducedNormalLowerCanonicalRay (d := d) i hi p ε)))
  have hbase :
      BHW.reducedDiffMap (m + 1) d zsrc =
        BHW.reducedDiffMap (m + 1) d zcan := by
    rw [show zcan =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.unflattenCfg (m + 1) d
            (fun a =>
              (x0 a : ℂ) -
                (ε : ℂ) *
                  (reducedNormalToOS45CommonEdgeFlatCLM
                    (d := d) i hi
                    (reducedNormalFlatCanonicalDirection (d := d) i hi) a : ℂ) *
                  Complex.I)) by
      simp [zcan, x0, reducedNormalToOS45CommonEdgeComplexCLM_lowerRay]]
    ext k μ
    rw [BHW.reducedDiffMap_eq_successive_differences,
      BHW.reducedDiffMap_eq_successive_differences]
    have hdiv_succ :
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).divNat =
          (⟨k.val + 1, by omega⟩ : Fin (m + 1)) := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).1 =
          (⟨k.val + 1, by omega⟩ : Fin (m + 1))
      simp
    have hmod_succ :
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).2 = μ
      simp
    have hdiv_curr :
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).divNat =
          (⟨k.val, by omega⟩ : Fin (m + 1)) := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).1 =
          (⟨k.val, by omega⟩ : Fin (m + 1))
      simp
    have hmod_curr :
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
      change
        (finProdFinEquiv.symm
          (finProdFinEquiv
            ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).2 = μ
      simp
    have hη :
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))
            ⟨k.val + 1, by omega⟩ μ : ℂ) -
          BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))
            ⟨k.val, by omega⟩ μ =
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalAbsoluteSectionCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi))
            ⟨k.val + 1, by omega⟩ μ : ℂ) -
          BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalAbsoluteSectionCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi))
            ⟨k.val, by omega⟩ μ := by
      exact_mod_cast
        os45CommonEdgeRealPoint_canonicalForward_diff_eq_reducedNormalCanonical
          (d := d) (i := i) (hi := hi) k μ
    by_cases hμ : μ = (0 : Fin (d + 1))
    · subst μ
      simp [BHW.os45CommonEdgeRealPoint] at hη
      simp [zsrc, BHW.os45FlatCommonChartSourceSide, uε, x0, ηc,
        BHW.unflattenCfg, BHW.os45QuarterTurnCLE_symm_apply,
        BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
        flattenCLEquivReal_apply, sub_eq_add_neg, Pi.add_apply,
        Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hdiv_succ, hmod_succ,
        hdiv_curr, hmod_curr]
      ring_nf at hη ⊢
      linear_combination (-((Complex.I + Complex.I ^ 2) * (ε : ℂ))) * hη
    · simp [zsrc, BHW.os45FlatCommonChartSourceSide, uε, x0, ηc,
        BHW.unflattenCfg, BHW.os45QuarterTurnCLE_symm_apply,
        BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
        flattenCLEquivReal_apply, sub_eq_add_neg, Pi.add_apply,
        Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hμ, hdiv_succ,
        hmod_succ, hdiv_curr, hmod_curr]
      simp [BHW.os45CommonEdgeRealPoint, hμ] at hη
      ring_nf at hη ⊢
      linear_combination (-(Complex.I * (ε : ℂ))) * hη
  calc
    BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) σ zsrc) =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d zsrc) := by
      simpa [zsrc, BHW.permAct] using
        (BHW.permOnReducedDiff_reducedDiffMap
          (d := d) (n := m + 1) σ zsrc).symm
    _ = BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d zcan) := by
      rw [hbase]
    _ = BHW.reducedDiffMap (m + 1) d (BHW.permAct (d := d) σ zcan) := by
      simpa [zcan, BHW.permAct] using
        (BHW.permOnReducedDiff_reducedDiffMap
          (d := d) (n := m + 1) σ zcan)

omit [NeZero d] in
/-- The OS45 quarter-turned upper reduced-normal ray has a definite
zero-height boundary in reduced-difference coordinates.

The limit is the reduced difference of the inverse-quarter-turned common-edge
carrier, not the ordinary real canonical reduced edge.  This is the coordinate
endpoint targeted by the remaining endpoint DCT/source-normalization step. -/
theorem tendsto_reducedDiffMap_permAct_os45QuarterTurnCLE_symm_reducedNormalUpperCanonicalRay_boundary
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun ε : ℝ =>
        BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (reducedNormalToOS45CommonEdgeComplexCLM
                  (d := d) i hi
                  (reducedNormalUpperCanonicalRay (d := d) i hi p ε))))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds
        (BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (SCV.realEmbed
                  (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlattenCLE
                      (d := d) i ⟨i.val + 1, hi⟩ p)))))))) := by
  let L := reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := m + 1)
  let T :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) →
        BHW.ReducedNPointConfig d m := fun γ =>
    BHW.reducedDiffMap (m + 1) d
      (BHW.permAct (d := d) σ
        (Q.symm (BHW.unflattenCfg (m + 1) d (L γ))))
  have hT_cont : Continuous T := by
    have hL : Continuous fun γ => L γ := L.continuous
    have hun : Continuous fun γ => BHW.unflattenCfg (m + 1) d (L γ) := by
      exact (differentiable_unflattenCfg_local (m + 1) d).continuous.comp hL
    have hperm :
        Continuous fun γ =>
          BHW.permAct (d := d) σ
            (Q.symm (BHW.unflattenCfg (m + 1) d (L γ))) := by
      exact
        (continuous_pi fun k =>
          continuous_pi fun μ =>
            (continuous_apply μ).comp
              ((continuous_apply (σ k)).comp (Q.symm.continuous.comp hun)))
    exact (BHW.reducedDiffMap (m + 1) d).continuous.comp hperm
  have hγ := reducedNormalUpperCanonicalRay_tendsto (d := d) i hi p
  have hcomp := hT_cont.tendsto _ |>.comp hγ
  simpa [T, L, Q] using hcomp

omit [NeZero d] in
/-- Lower companion to
`tendsto_reducedDiffMap_permAct_os45QuarterTurnCLE_symm_reducedNormalUpperCanonicalRay_boundary`. -/
theorem tendsto_reducedDiffMap_permAct_os45QuarterTurnCLE_symm_reducedNormalLowerCanonicalRay_boundary
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun ε : ℝ =>
        BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (reducedNormalToOS45CommonEdgeComplexCLM
                  (d := d) i hi
                  (reducedNormalLowerCanonicalRay (d := d) i hi p ε))))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds
        (BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (SCV.realEmbed
                  (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlattenCLE
                      (d := d) i ⟨i.val + 1, hi⟩ p)))))))) := by
  let L := reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := m + 1)
  let T :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) →
        BHW.ReducedNPointConfig d m := fun γ =>
    BHW.reducedDiffMap (m + 1) d
      (BHW.permAct (d := d) σ
        (Q.symm (BHW.unflattenCfg (m + 1) d (L γ))))
  have hT_cont : Continuous T := by
    have hL : Continuous fun γ => L γ := L.continuous
    have hun : Continuous fun γ => BHW.unflattenCfg (m + 1) d (L γ) := by
      exact (differentiable_unflattenCfg_local (m + 1) d).continuous.comp hL
    have hperm :
        Continuous fun γ =>
          BHW.permAct (d := d) σ
            (Q.symm (BHW.unflattenCfg (m + 1) d (L γ))) := by
      exact
        (continuous_pi fun k =>
          continuous_pi fun μ =>
            (continuous_apply μ).comp
              ((continuous_apply (σ k)).comp (Q.symm.continuous.comp hun)))
    exact (BHW.reducedDiffMap (m + 1) d).continuous.comp hperm
  have hγ := reducedNormalLowerCanonicalRay_tendsto (d := d) i hi p
  have hcomp := hT_cont.tendsto _ |>.comp hγ
  simpa [T, L, Q] using hcomp

/-- The actual upper cone-height source-side packet converges, in reduced
difference coordinates, to the OS45 zero-height common-edge boundary. -/
theorem tendsto_reducedDiffMap_coneHeight_sourceSide_upper_boundary
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun ε : ℝ =>
        let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))
        let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
          reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
        let uε : NPointDomain d (m + 1) :=
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • ηc)
        BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds
        (BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (SCV.realEmbed
                  (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlattenCLE
                      (d := d) i ⟨i.val + 1, hi⟩ p)))))))) := by
  have htarget :=
    tendsto_reducedDiffMap_permAct_os45QuarterTurnCLE_symm_reducedNormalUpperCanonicalRay_boundary
      (d := d) (i := i) (hi := hi) σ p
  refine Filter.Tendsto.congr' ?_ htarget
  filter_upwards with ε
  exact
    (reducedDiffMap_coneHeight_sourceSide_eq_upperCanonicalRay
      (d := d) (i := i) (hi := hi) σ p ε).symm

/-- Lower companion to
`tendsto_reducedDiffMap_coneHeight_sourceSide_upper_boundary`. -/
theorem tendsto_reducedDiffMap_coneHeight_sourceSide_lower_boundary
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (σ : Equiv.Perm (Fin (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun ε : ℝ =>
        let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))
        let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
          reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
        let uε : NPointDomain d (m + 1) :=
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • ηc)
        BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds
        (BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d) σ
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (SCV.realEmbed
                  (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
                    (reducedNormalFlattenCLE
                      (d := d) i ⟨i.val + 1, hi⟩ p)))))))) := by
  have htarget :=
    tendsto_reducedDiffMap_permAct_os45QuarterTurnCLE_symm_reducedNormalLowerCanonicalRay_boundary
      (d := d) (i := i) (hi := hi) σ p
  refine Filter.Tendsto.congr' ?_ htarget
  filter_upwards with ε
  exact
    (reducedDiffMap_coneHeight_sourceSide_eq_lowerCanonicalRay
      (d := d) (i := i) (hi := hi) σ p ε).symm

set_option maxHeartbeats 1200000 in
/-- The deterministic upper OS45 source-side ray selected by the cone-valid
canonical height is eventually on the extended tube.

This is the Figure-2-4 sheet-membership half of the OS-I `(4.12)`--`(4.14)`
source transfer: once the reduced-normal base point is represented inside the
source patch, the local wedge gives a uniform collar in the selected branch
domain, and the source-side normal form converts that branch-domain membership
to extended-tube membership. -/
theorem eventually_sourceSide_coneHeight_upper_mem_extendedTube
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
        BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))
          (canonicalForwardConeDirection (d := d) (m + 1))
      let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      let uε : NPointDomain d (m + 1) :=
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • ηc)
      BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε ∈
        BHW.ExtendedTube d (m + 1) := by
  classical
  let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
      (canonicalForwardConeDirection (d := d) (m + 1))
  let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
      (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
  have hpPatch :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈
        reducedNormalOS45SourcePatchPreimage (d := d) i hi P :=
    (reducedNormalFlatten_mem_reducedNormalOS45SourcePatchPreimage_iff
      (d := d) i hi P p).2 hpP
  have hx0_edge :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1))) := by
    simpa [x0] using
      (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
        (d := d) i hi P
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)).2 hpPatch
  have hηc_cone :
      ηc ∈ BHW.os45FlatCommonChartCone d (m + 1) := by
    simpa [ηc] using
      BHW.os45CommonEdgeFlatCLE_canonicalForwardConeDirection_mem_cone
        (d := d) m
  have hK_sub :
      ({x0} : Set (BHW.OS45FlatCommonChartReal d (m + 1))) ⊆
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hx0_edge
  have hKη_sub :
      ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1))) ⊆
        BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    rw [Set.mem_singleton_iff] at hη
    subst η
    exact hηc_cone
  obtain ⟨r, hr_pos, hside⟩ :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P)
      ({x0} : Set (BHW.OS45FlatCommonChartReal d (m + 1)))
      isCompact_singleton hK_sub
      ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1)))
      isCompact_singleton hKη_sub
  have hsmall :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ε < r := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds hr_pos)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt
  let uε : NPointDomain d (m + 1) :=
    (BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • ηc)
  have homega :
      (fun a => (x0 a : ℂ) + (ε : ℂ) * (ηc a : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) :=
    (hside x0 (by simp) ηc (by simp) ε hε_pos hε_lt).1
  have hflat_eq :
      (fun a =>
          ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) uε +
              ((1 : ℝ) * ε) • ηc) a : ℂ) +
            ((((1 : ℝ) * ε) • ηc) a : ℂ) * Complex.I) =
        fun a => (x0 a : ℂ) + (ε : ℂ) * (ηc a : ℂ) * Complex.I := by
    funext a
    simp [uε, sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hflat :
      (fun a =>
          ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) uε +
              ((1 : ℝ) * ε) • ηc) a : ℂ) +
            ((((1 : ℝ) * ε) • ηc) a : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) := by
    rw [hflat_eq]
    exact homega
  have hET :=
    (BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
      d (m + 1) (1 : Equiv.Perm (Fin (m + 1)))
      (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε).1 hflat
  simpa [ηc, x0, uε] using hET

set_option maxHeartbeats 1200000 in
/-- The deterministic lower OS45 source-side ray selected by the cone-valid
canonical height is eventually on the extended tube after the adjacent branch
label is applied. -/
theorem eventually_sourceSide_coneHeight_lower_mem_extendedTube
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
        BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))
          (canonicalForwardConeDirection (d := d) (m + 1))
      let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      let uε : NPointDomain d (m + 1) :=
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • ηc)
      BHW.permAct (d := d)
          ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm)
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε) ∈
        BHW.ExtendedTube d (m + 1) := by
  classical
  let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
    BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))
      (canonicalForwardConeDirection (d := d) (m + 1))
  let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
      (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
  have hpPatch :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈
        reducedNormalOS45SourcePatchPreimage (d := d) i hi P :=
    (reducedNormalFlatten_mem_reducedNormalOS45SourcePatchPreimage_iff
      (d := d) i hi P p).2 hpP
  have hx0_edge :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1))) := by
    simpa [x0] using
      (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
        (d := d) i hi P
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)).2 hpPatch
  have hηc_cone :
      ηc ∈ BHW.os45FlatCommonChartCone d (m + 1) := by
    simpa [ηc] using
      BHW.os45CommonEdgeFlatCLE_canonicalForwardConeDirection_mem_cone
        (d := d) m
  have hK_sub :
      ({x0} : Set (BHW.OS45FlatCommonChartReal d (m + 1))) ⊆
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hx0_edge
  have hKη_sub :
      ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1))) ⊆
        BHW.os45FlatCommonChartCone d (m + 1) := by
    intro η hη
    rw [Set.mem_singleton_iff] at hη
    subst η
    exact hηc_cone
  obtain ⟨r, hr_pos, hside⟩ :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P)
      ({x0} : Set (BHW.OS45FlatCommonChartReal d (m + 1)))
      isCompact_singleton hK_sub
      ({ηc} : Set (BHW.OS45FlatCommonChartReal d (m + 1)))
      isCompact_singleton hKη_sub
  have hsmall :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ε < r := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds hr_pos)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt
  let uε : NPointDomain d (m + 1) :=
    (BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • ηc)
  have homega :
      (fun a => (x0 a : ℂ) - (ε : ℂ) * (ηc a : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) :=
    (hside x0 (by simp) ηc (by simp) ε hε_pos hε_lt).2
  have hflat_eq :
      (fun a =>
          ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) uε +
              ((-1 : ℝ) * ε) • ηc) a : ℂ) +
            ((((-1 : ℝ) * ε) • ηc) a : ℂ) * Complex.I) =
        fun a => (x0 a : ℂ) - (ε : ℂ) * (ηc a : ℂ) * Complex.I := by
    funext a
    simp [uε, sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hflat :
      (fun a =>
          ((BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) uε +
              ((-1 : ℝ) * ε) • ηc) a : ℂ) +
            ((((-1 : ℝ) * ε) • ηc) a : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) := by
    rw [hflat_eq]
    exact homega
  exact
    (BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
      d (m + 1) (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε).1 hflat

/-- Upper moving-source transport packet for the cone-valid OS45 height.

This combines the local-wedge membership statement with the exact
reduced-difference coordinate identity.  The source variable is the moving
`uε = e.symm (x0 - ε • ηc)`, matching the genuine source-side Figure-2-4
geometry; no unshifted-source PET normal form is asserted here. -/
theorem eventually_sourceSide_coneHeight_upper_transport_packet
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
        BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))
          (canonicalForwardConeDirection (d := d) (m + 1))
      let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      let uε : NPointDomain d (m + 1) :=
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • ηc)
      BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε ∈
        BHW.ExtendedTube d (m + 1) ∧
      BHW.reducedDiffMap (m + 1) d
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε ηc uε) =
        BHW.reducedDiffMap (m + 1) d
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.unflattenCfg (m + 1) d
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)))) := by
  have hmem :=
    eventually_sourceSide_coneHeight_upper_mem_extendedTube
      (d := d) P p hpP
  filter_upwards [hmem] with ε hmemε
  refine ⟨?_, ?_⟩
  · simpa using hmemε
  · simpa [BHW.permAct] using
      (reducedDiffMap_coneHeight_sourceSide_eq_upperCanonicalRay
        (d := d) (i := i) (hi := hi)
        (σ := (1 : Equiv.Perm (Fin (m + 1)))) p ε)

/-- Lower moving-source transport packet for the cone-valid OS45 height after
the adjacent branch permutation.

This is the lower companion to
`eventually_sourceSide_coneHeight_upper_transport_packet`, again using the
moving source point `uε = e.symm (x0 + ε • ηc)` rather than an unshifted source
variable. -/
theorem eventually_sourceSide_coneHeight_lower_transport_packet
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      let ηc : BHW.OS45FlatCommonChartReal d (m + 1) :=
        BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))
          (canonicalForwardConeDirection (d := d) (m + 1))
      let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      let uε : NPointDomain d (m + 1) :=
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • ηc)
      BHW.permAct (d := d)
          ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm)
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε) ∈
        BHW.ExtendedTube d (m + 1) ∧
      BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d)
            ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm)
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε ηc uε)) =
        BHW.reducedDiffMap (m + 1) d
          (BHW.permAct (d := d)
            ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm)
            ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
              (BHW.unflattenCfg (m + 1) d
                (reducedNormalToOS45CommonEdgeComplexCLM
                  (d := d) i hi
                  (reducedNormalLowerCanonicalRay (d := d) i hi p ε))))) := by
  have hmem :=
    eventually_sourceSide_coneHeight_lower_mem_extendedTube
      (d := d) P p hpP
  filter_upwards [hmem] with ε hmemε
  refine ⟨?_, ?_⟩
  · simpa using hmemε
  · simpa using
      (reducedDiffMap_coneHeight_sourceSide_eq_lowerCanonicalRay
        (d := d) (i := i) (hi := hi)
        (σ := ((P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm))
        p ε)

end AdjacentNormal

end OSReconstruction
