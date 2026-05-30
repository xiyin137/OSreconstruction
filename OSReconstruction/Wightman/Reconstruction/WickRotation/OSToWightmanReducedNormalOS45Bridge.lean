import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSide
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
OS-I Section 4.5: the analytic branch value still has to be transported through
the reduced extension/uniqueness step, but no further coordinate correction is
needed. -/
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
differences, including after the selected adjacent branch permutation. -/
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

end AdjacentNormal

end OSReconstruction
