import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceClosure
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity

/-!
# R→E Section 4.3 Spectral Pairing

This file starts the reflection-positivity proof lane for the Wightman-to-
Euclidean direction.  It isolates the quotient-level spectral pairing used by
the OS-paper positivity argument.

The main point of the file is deliberately modest: once the Wightman
distribution has been supplied as a flattened Fourier-side functional supported
on the Section 4.3 Wightman spectral region, the pairing descends through the
positive-energy frequency quotients and its finite diagonal quadratic is
nonnegative by the Wightman positivity axiom.

The remaining R→E work is to produce `RToESection43WightmanSupport` from
`Wfn.spectrum_condition`, and then identify compact ordered Euclidean
Fourier-Laplace data with this quotient pairing.
-/

noncomputable section

open scoped Topology FourierTransform BigOperators
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Flattened Section 4.3 spectral support data for a Wightman family.

This is the exact support theorem needed by the R→E quotient pairing.  It is
kept explicit here because the codebase does not yet expose a public theorem
transporting `Wfn.spectrum_condition` all the way to
`section43WightmanSpectralRegion`.
-/
structure RToESection43WightmanSupport (Wfn : WightmanFunctions d) where
  Tflat :
    (N : ℕ) →
      SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ
  support :
    ∀ N, HasFourierSupportIn
      (section43WightmanSpectralRegion d N) (Tflat N)
  boundary :
    ∀ N (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
      Wfn.W N (unflattenSchwartzNPoint (d := d) φflat) =
        Tflat N (physicsFourierFlatCLM φflat)

/-- Wightman-side Fourier-Laplace representation data for the same flattened
frequency-side distribution used to represent the boundary value. -/
structure RToESection43DualConeFLPackage
    (Wfn : WightmanFunctions d) (N : ℕ) where
  Tflat :
    SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ
  hCflat_open :
    IsOpen ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hCflat_conv :
    Convex ℝ ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hCflat_cone :
    IsCone ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hCflat_salient :
    IsSalientCone ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  dualSupport :
    HasFourierSupportInDualCone
      ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) Tflat
  boundary :
    ∀ (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
      Wfn.W N (unflattenSchwartzNPoint (d := d) φflat) =
        Tflat (physicsFourierFlatCLM φflat)
  fourierLaplace :
    ∀ z : Fin N → Fin (d + 1) → ℂ,
      z ∈ TubeDomainSetPi (ForwardConeAbs d N) →
        F_ext_on_translatedPET_total Wfn z =
          fourierLaplaceExtMultiDim
            ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            Tflat (flattenCLEquiv N (d + 1) z)

/-- The flattened Wightman distribution is invariant under diagonal translation
of all Euclidean/Minkowski variables. -/
private theorem wfn_W_flat_diagonalTranslate_eq
    (Wfn : WightmanFunctions d)
    {N : ℕ}
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    Wfn.W N
        (unflattenSchwartzNPoint (d := d)
          (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) =
      Wfn.W N (unflattenSchwartzNPoint (d := d) φflat) := by
  let f : SchwartzNPoint d N := unflattenSchwartzNPoint (d := d) φflat
  let g : SchwartzNPoint d N :=
    unflattenSchwartzNPoint (d := d)
      (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)
  have hfg : ∀ x : NPointDomain d N, g.toFun x = f.toFun (fun i => x i + a) := by
    intro x
    change (unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) x =
      (unflattenSchwartzNPoint (d := d) φflat) (fun i => x i + a)
    rw [unflattenSchwartzNPoint_apply, SCV.translateSchwartz_apply,
      unflattenSchwartzNPoint_apply]
    congr 1
  have h := Wfn.translation_invariant N a f g hfg
  simpa [f, g] using h.symm

/-- Translation invariance of `Wfn.W` becomes invariance of the flattened
frequency-side functional under total-momentum phase multiplication. -/
private theorem tflat_totalMomentumPhase_invariant_of_wfn_translationInvariant
    (Wfn : WightmanFunctions d)
    {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        Wfn.W N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∀ (a : Fin (d + 1) → ℝ)
      (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
      Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K := by
  intro a K
  obtain ⟨φflat, hφflat⟩ := physicsFourierFlatCLM_surjective (N * (d + 1)) K
  rw [← hφflat]
  calc
    Tflat (section43TotalMomentumPhaseCLM d N a (physicsFourierFlatCLM φflat))
        = Tflat (physicsFourierFlatCLM
            (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) := by
          rw [← physicsFourierFlatCLM_diagonalTranslate_eq_phaseCLM]
    _ = Wfn.W N
            (unflattenSchwartzNPoint (d := d)
              (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) := by
          rw [← hTflat_bv]
    _ = Wfn.W N (unflattenSchwartzNPoint (d := d) φflat) := by
          exact wfn_W_flat_diagonalTranslate_eq (d := d) Wfn a φflat
    _ = Tflat (physicsFourierFlatCLM φflat) := by
          rw [hTflat_bv]

/-- Dual-cone Fourier support for the flattened Wightman distribution, obtained
directly from the Wightman forward-tube boundary-value axiom. -/
private theorem exists_flattened_wfn_dualCone_distribution
    (Wfn : WightmanFunctions d)
    (N : ℕ) :
    ∃ (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone
          ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) Tflat ∧
        ∀ (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
          Wfn.W N (unflattenSchwartzNPoint (d := d) φflat) =
            Tflat (physicsFourierFlatCLM φflat) := by
  let Wcl : SchwartzNPoint d N →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := Wfn.W N
          map_add' := (Wfn.linear N).map_add
          map_smul' := (Wfn.linear N).map_smul }
      cont := Wfn.tempered N }
  have hWcl : ∀ f : SchwartzNPoint d N, Wcl f = Wfn.W N f := by
    intro f
    rfl
  have hC_open : IsOpen (ForwardConeAbs d N) := forwardConeAbs_isOpen d N
  have hC_conv : Convex ℝ (ForwardConeAbs d N) := forwardConeAbs_convex d N
  have hC_cone : IsCone (ForwardConeAbs d N) := by
    intro y hy t ht
    exact forwardConeAbs_smul d N t ht y hy
  have hC_salient : IsSalientCone (ForwardConeAbs d N) :=
    forwardConeAbs_salient d N
  let Wanalytic : (Fin N → Fin (d + 1) → ℂ) → ℂ :=
    (Wfn.spectrum_condition N).choose
  have hF_holo :
      DifferentiableOn ℂ Wanalytic
        (TubeDomainSetPi (ForwardConeAbs d N)) := by
    simpa [Wanalytic, forwardTube_eq_imPreimage] using
      (Wfn.spectrum_condition N).choose_spec.1
  have hF_growth :
      ∃ (C_bd : ℝ) (M : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ TubeDomainSetPi (ForwardConeAbs d N) →
          ‖Wanalytic z‖ ≤ C_bd * (1 + ‖z‖) ^ M := by
    obtain ⟨C_bd, M, hC_pos, hbound⟩ :=
      (Wfn.spectrum_condition N).choose_spec.2.1
    refine ⟨C_bd, M, hC_pos, ?_⟩
    intro z hz
    have hz' : z ∈ ForwardTube d N := by
      simpa [forwardTube_eq_imPreimage] using hz
    exact hbound z hz'
  have hF_bv :
      ∀ (η : Fin N → Fin (d + 1) → ℝ), η ∈ ForwardConeAbs d N →
        ∀ (φ : SchwartzNPoint d N),
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d N,
              Wanalytic
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * φ x)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Wcl φ)) := by
    intro η hη φ
    rw [hWcl]
    exact (Wfn.spectrum_condition N).choose_spec.2.2 φ η
      ((inForwardCone_iff_mem_forwardConeAbs (d := d) (n := N) η).2 hη)
  obtain ⟨Tflat, hTflat_supp, hTflat_repr⟩ :=
    bv_implies_fourier_support (C := ForwardConeAbs d N)
      hC_open hC_conv hC_cone hC_salient
      (F := Wanalytic) hF_holo hF_growth Wcl hF_bv
  refine ⟨Tflat, hTflat_supp, ?_⟩
  intro φflat
  simpa [Wcl, unflattenSchwartzNPoint] using hTflat_repr φflat

/-- Wightman-side Section 4.3 flattened boundary-value package, including the
interior Fourier-Laplace representation of the same `Tflat`.

This is the R→E analogue of the `bvt_F` package used by the E→R Section 4.3
closure.  The support and boundary fields come from Vladimirov-Tillmann
boundary-value support, while the interior representation uses the companion
Fourier-Laplace uniqueness theorem. -/
private theorem exists_rToESection43DualConeFLPackage_of_wightmanFunctions
    (Wfn : WightmanFunctions d) (N : ℕ) :
    ∃ _P : RToESection43DualConeFLPackage (d := d) Wfn N, True := by
  let C : Set (Fin N → Fin (d + 1) → ℝ) := ForwardConeAbs d N
  let eR := flattenCLEquivReal N (d + 1)
  let Cflat : Set (Fin (N * (d + 1)) → ℝ) := eR '' C
  let Wcl : SchwartzNPoint d N →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := Wfn.W N
          map_add' := (Wfn.linear N).map_add
          map_smul' := (Wfn.linear N).map_smul }
      cont := Wfn.tempered N }
  have hWcl : ∀ f : SchwartzNPoint d N, Wcl f = Wfn.W N f := by
    intro f
    rfl
  have hC_open : IsOpen C := by
    simpa [C] using forwardConeAbs_isOpen d N
  have hC_conv : Convex ℝ C := by
    simpa [C] using forwardConeAbs_convex d N
  have hC_cone : IsCone C := by
    intro y hy t ht
    exact forwardConeAbs_smul d N t ht y hy
  have hC_salient : IsSalientCone C := by
    simpa [C] using forwardConeAbs_salient d N
  have hFT_PET : ForwardTube d N ⊆ PermutedExtendedTube d N :=
    ForwardTube_subset_ComplexExtended d N |>.trans
      (ComplexExtended_subset_Permuted d N)
  have hF_holo :
      DifferentiableOn ℂ (F_ext_on_translatedPET_total Wfn) (TubeDomainSetPi C) := by
    have hBHW :
        DifferentiableOn ℂ (W_analytic_BHW Wfn N).val (ForwardTube d N) :=
      (W_analytic_BHW Wfn N).property.1.mono hFT_PET
    have hBHW_C :
        DifferentiableOn ℂ (W_analytic_BHW Wfn N).val (TubeDomainSetPi C) := by
      simpa [C, forwardTube_eq_imPreimage] using hBHW
    refine hBHW_C.congr ?_
    intro z hz
    have hzFT : z ∈ ForwardTube d N := by
      simpa [C, forwardTube_eq_imPreimage] using hz
    exact F_ext_on_translatedPET_total_eq_on_PET Wfn z (hFT_PET hzFT)
  have hF_growth :
      ∃ (C_bd : ℝ) (M : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ TubeDomainSetPi C →
          ‖F_ext_on_translatedPET_total Wfn z‖ ≤ C_bd * (1 + ‖z‖) ^ M := by
    obtain ⟨C_bd, M, hC_pos, hbound⟩ :=
      (Wfn.spectrum_condition N).choose_spec.2.1
    refine ⟨C_bd, M, hC_pos, ?_⟩
    intro z hz
    have hzFT : z ∈ ForwardTube d N := by
      simpa [C, forwardTube_eq_imPreimage] using hz
    have htotal_eq :
        F_ext_on_translatedPET_total Wfn z =
          (Wfn.spectrum_condition N).choose z := by
      calc
        F_ext_on_translatedPET_total Wfn z
            = (W_analytic_BHW Wfn N).val z :=
              F_ext_on_translatedPET_total_eq_on_PET Wfn z (hFT_PET hzFT)
        _ = (Wfn.spectrum_condition N).choose z :=
              (W_analytic_BHW Wfn N).property.2.1 z hzFT
    simpa [htotal_eq] using hbound z hzFT
  have hF_bv :
      ∀ (η : Fin N → Fin (d + 1) → ℝ), η ∈ C →
        ∀ (φ : SchwartzNPoint d N),
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d N,
              F_ext_on_translatedPET_total Wfn
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * φ x)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Wcl φ)) := by
    intro η hη φ
    rw [hWcl]
    have hη_forward : InForwardCone d N η :=
      (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := N) η).2
        (by simpa [C] using hη)
    have hlim := bhw_distributional_boundary_values Wfn φ η hη_forward
    refine Filter.Tendsto.congr' ?_ hlim
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε => ?_⟩
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hpoint :
        (fun k μ => (↑(x k μ) + ε * ↑(η k μ) * Complex.I : ℂ)) ∈
          ForwardTube d N := by
      intro k
      show InOpenForwardCone d _
      have him :
          (fun μ =>
              ((↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) -
                (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ) else
                  fun μ => ↑(x ⟨k.val - 1, by omega⟩ μ) +
                    ↑ε * ↑(η ⟨k.val - 1, by omega⟩ μ) * Complex.I) μ).im) =
            ε • (fun μ => η k μ -
              (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else
                η ⟨k.val - 1, by omega⟩) μ) := by
        ext μ
        by_cases hk : (k : ℕ) = 0
        · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
            Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply,
            smul_eq_mul]
        · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im,
            Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
            Pi.smul_apply, smul_eq_mul]
          ring
      rw [him]
      exact inOpenForwardCone_smul d ε (by simpa using hε) _ (hη_forward k)
    rw [F_ext_on_translatedPET_total_eq_on_PET Wfn _ (hFT_PET hpoint)]
  have hCflat_open : IsOpen Cflat := eR.toHomeomorph.isOpenMap _ hC_open
  have hCflat_conv : Convex ℝ Cflat :=
    hC_conv.linear_image eR.toLinearEquiv.toLinearMap
  have hCflat_cone : IsCone Cflat := by
    intro y hy t ht
    rcases hy with ⟨y', hy', rfl⟩
    exact ⟨t • y', hC_cone y' hy' t ht, by simp⟩
  have hCflat_salient : IsSalientCone Cflat := by
    intro y hy hy_neg
    rw [show closure Cflat = eR '' closure C from
      (eR.toHomeomorph.image_closure C).symm] at hy hy_neg
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨y'', hy'', hyw⟩ := hy_neg
    have h_neg : y'' = -y' := eR.injective (by rw [hyw, map_neg])
    subst h_neg
    exact show eR y' = 0 from by rw [hC_salient y' hy' hy'', map_zero]
  obtain ⟨Tflat, hTflat_supp, hTflat_repr⟩ :=
    bv_implies_fourier_support C hC_open hC_conv hC_cone hC_salient
      (F_ext_on_translatedPET_total Wfn) hF_holo hF_growth Wcl hF_bv
  have hFL_repr :
      ∀ z ∈ TubeDomainSetPi C,
        F_ext_on_translatedPET_total Wfn z =
          fourierLaplaceExtMultiDim Cflat
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            Tflat (flattenCLEquiv N (d + 1) z) :=
    fl_representation_from_bv C hC_open hC_conv hC_cone hC_salient
      (F_ext_on_translatedPET_total Wfn) hF_holo Wcl hF_bv
      Cflat rfl hCflat_open hCflat_conv hCflat_cone hCflat_salient
      Tflat hTflat_supp hTflat_repr
  refine
    ⟨{ Tflat := Tflat
       hCflat_open := hCflat_open
       hCflat_conv := hCflat_conv
       hCflat_cone := hCflat_cone
       hCflat_salient := hCflat_salient
       dualSupport := ?_
       boundary := ?_
       fourierLaplace := ?_ }, trivial⟩
  · simpa [Cflat, C, eR] using hTflat_supp
  · intro φflat
    simpa [Wcl, unflattenSchwartzNPoint] using hTflat_repr φflat
  · intro z hz
    simpa [Cflat, C, eR] using hFL_repr z (by simpa [C] using hz)

/-- The canonical Wightman-side Section 4.3 flattened boundary-value and
Fourier-Laplace package. -/
noncomputable def rToESection43DualConeFLPackage_of_wightmanFunctions
    (Wfn : WightmanFunctions d) (N : ℕ) :
    RToESection43DualConeFLPackage (d := d) Wfn N :=
  (exists_rToESection43DualConeFLPackage_of_wightmanFunctions
    (d := d) Wfn N).choose

/-- The Section 4.3 flattened Wightman spectral-region support package derived
from the Wightman axioms. -/
noncomputable def rToESection43WightmanSupport_of_wightmanFunctions
    (Wfn : WightmanFunctions d) :
    RToESection43WightmanSupport (d := d) Wfn := by
  refine
    { Tflat := fun N =>
        (rToESection43DualConeFLPackage_of_wightmanFunctions (d := d) Wfn N).Tflat
      support := ?_
      boundary := ?_ }
  · intro N
    let P := rToESection43DualConeFLPackage_of_wightmanFunctions (d := d) Wfn N
    have hphase :=
      tflat_totalMomentumPhase_invariant_of_wfn_translationInvariant
        (d := d) Wfn
        P.Tflat
        P.boundary
    have htotal :=
      hasFourierSupportIn_totalMomentumZero_of_phase_invariant
        d P.Tflat hphase
    exact hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero
      d N P.dualSupport htotal
  · intro N φflat
    exact
      (rToESection43DualConeFLPackage_of_wightmanFunctions
        (d := d) Wfn N).boundary φflat

/-- The canonical support package uses the same flattened distribution as the
canonical Wightman-side Fourier-Laplace package. -/
theorem rToESection43WightmanSupport_of_wightmanFunctions_fourierLaplace
    (Wfn : WightmanFunctions d)
    (N : ℕ)
    (z : Fin N → Fin (d + 1) → ℂ)
    (hz : z ∈ TubeDomainSetPi (ForwardConeAbs d N)) :
    F_ext_on_translatedPET_total Wfn z =
      fourierLaplaceExtMultiDim
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
        (rToESection43DualConeFLPackage_of_wightmanFunctions
          (d := d) Wfn N).hCflat_open
        (rToESection43DualConeFLPackage_of_wightmanFunctions
          (d := d) Wfn N).hCflat_conv
        (rToESection43DualConeFLPackage_of_wightmanFunctions
          (d := d) Wfn N).hCflat_cone
        (rToESection43DualConeFLPackage_of_wightmanFunctions
          (d := d) Wfn N).hCflat_salient
        ((rToESection43WightmanSupport_of_wightmanFunctions
          (d := d) Wfn).Tflat N)
        (flattenCLEquiv N (d + 1) z) := by
  exact
    (rToESection43DualConeFLPackage_of_wightmanFunctions
      (d := d) Wfn N).fourierLaplace z hz

/-- Successor-right descent of the Wightman tensor scalar through Section 4.3
frequency projections, assuming the flattened Section 4.3 spectral support
package for `Wfn.W`.

This is the R→E analogue of
`bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight`.
-/
theorem rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    {n m : ℕ}
    (φ₁ φ₂ : SchwartzNPoint d n)
    (ψ₁ ψ₂ : SchwartzNPoint d (m + 1))
    (hφ :
      section43FrequencyProjection (d := d) n φ₁ =
        section43FrequencyProjection (d := d) n φ₂)
    (hψ :
      section43FrequencyProjection (d := d) (m + 1) ψ₁ =
        section43FrequencyProjection (d := d) (m + 1) ψ₂) :
    Wfn.W (n + (m + 1)) (φ₁.conjTensorProduct ψ₁) =
      Wfn.W (n + (m + 1)) (φ₂.conjTensorProduct ψ₂) := by
  have hφ_quot :
      section43PositiveEnergyQuotientMap (d := d) n
          (section43FrequencyRepresentative (d := d) n φ₁) =
        section43PositiveEnergyQuotientMap (d := d) n
          (section43FrequencyRepresentative (d := d) n φ₂) := by
    simpa [section43FrequencyProjection] using hφ
  have hψ_quot :
      section43PositiveEnergyQuotientMap (d := d) (m + 1)
          (section43FrequencyRepresentative (d := d) (m + 1) ψ₁) =
        section43PositiveEnergyQuotientMap (d := d) (m + 1)
          (section43FrequencyRepresentative (d := d) (m + 1) ψ₂) := by
    simpa [section43FrequencyProjection] using hψ
  have hφ_eqOn :
      Set.EqOn
        (section43FrequencyRepresentative (d := d) n φ₁ :
          NPointDomain d n → ℂ)
        (section43FrequencyRepresentative (d := d) n φ₂ :
          NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) hφ_quot
  have hψ_eqOn :
      Set.EqOn
        (section43FrequencyRepresentative (d := d) (m + 1) ψ₁ :
          NPointDomain d (m + 1) → ℂ)
        (section43FrequencyRepresentative (d := d) (m + 1) ψ₂ :
          NPointDomain d (m + 1) → ℂ)
        (section43PositiveEnergyRegion d (m + 1)) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := m + 1) hψ_quot
  have hEqSpectral :
      Set.EqOn
        (physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁)) :
            (Fin ((n + (m + 1)) * (d + 1)) → ℝ) → ℂ)
        (physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂)) :
            (Fin ((n + (m + 1)) * (d + 1)) → ℝ) → ℂ)
        (section43WightmanSpectralRegion d (n + (m + 1))) := by
    intro ξ hξ
    let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
    have hleft_mem :
        section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ ∈
          section43PositiveEnergyRegion d n := by
      simpa [qξ] using
        section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
          (d := d) (n := n) (r := m + 1) (Nat.succ_pos m) hξ
    have hright_mem :
        section43RightTailBlock d n (m + 1) qξ ∈
          section43PositiveEnergyRegion d (m + 1) := by
      simpa [qξ] using
        section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
          (d := d) (n := n) (r := m + 1) hξ
    have hleft_eq := hφ_eqOn hleft_mem
    have hright_eq := hψ_eqOn hright_mem
    have hfac₁ :=
      physicsFourierFlatCLM_flatten_conjTensorProduct_eq_frequencyRepresentatives_on_spectralRegion
        (d := d) (n := n) (m := m) φ₁ ψ₁ hξ
    have hfac₂ :=
      physicsFourierFlatCLM_flatten_conjTensorProduct_eq_frequencyRepresentatives_on_spectralRegion
        (d := d) (n := n) (m := m) φ₂ ψ₂ hξ
    dsimp only at hfac₁ hfac₂
    rw [hfac₁, hfac₂, hleft_eq, hright_eq]
  have hflat₁ :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁)) =
        φ₁.conjTensorProduct ψ₁ := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  have hflat₂ :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂)) =
        φ₂.conjTensorProduct ψ₂ := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  calc
    Wfn.W (n + (m + 1)) (φ₁.conjTensorProduct ψ₁)
        = Wfn.W (n + (m + 1))
            (unflattenSchwartzNPoint (d := d)
              (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁))) := by
          rw [hflat₁]
    _ = hSupp.Tflat (n + (m + 1))
          (physicsFourierFlatCLM
            (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁))) := by
          simpa using
            hSupp.boundary (n + (m + 1))
              (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁))
    _ = hSupp.Tflat (n + (m + 1))
          (physicsFourierFlatCLM
            (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂))) := by
          exact hasFourierSupportIn_eqOn (hSupp.support (n + (m + 1))) hEqSpectral
    _ = Wfn.W (n + (m + 1))
            (unflattenSchwartzNPoint (d := d)
              (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂))) := by
          simpa using
            (hSupp.boundary (n + (m + 1))
              (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂))).symm
    _ = Wfn.W (n + (m + 1)) (φ₂.conjTensorProduct ψ₂) := by
          rw [hflat₂]

/-- Wightman tensor scalar descent through both Section 4.3 component frequency
projections.

The positive-right-degree branch is spectral-region descent.  The right-degree
zero branch is handled as in the E→R closure: `(0,0)` is scalar evaluation,
while `(n+1,0)` is flipped to successor-right by Wightman Hermiticity.
-/
theorem rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    {n m : ℕ}
    (φ₁ φ₂ : SchwartzNPoint d n)
    (ψ₁ ψ₂ : SchwartzNPoint d m)
    (hφ :
      section43FrequencyProjection (d := d) n φ₁ =
        section43FrequencyProjection (d := d) n φ₂)
    (hψ :
      section43FrequencyProjection (d := d) m ψ₁ =
        section43FrequencyProjection (d := d) m ψ₂) :
    Wfn.W (n + m) (φ₁.conjTensorProduct ψ₁) =
      Wfn.W (n + m) (φ₂.conjTensorProduct ψ₂) := by
  cases m with
  | succ m =>
      exact
        rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight
          (d := d) Wfn hSupp φ₁ φ₂ ψ₁ ψ₂ hφ hψ
  | zero =>
      cases n with
      | zero =>
          have hφ0 := section43FrequencyProjection_zero_eval_eq (d := d) φ₁ φ₂ hφ
          have hψ0 := section43FrequencyProjection_zero_eval_eq (d := d) ψ₁ ψ₂ hψ
          have hφ_eq : φ₁ = φ₂ := by
            ext x
            have hx : x = (0 : NPointDomain d 0) := Subsingleton.elim _ _
            rw [hx]
            exact hφ0
          have hψ_eq : ψ₁ = ψ₂ := by
            ext x
            have hx : x = (0 : NPointDomain d 0) := Subsingleton.elim _ _
            rw [hx]
            exact hψ0
          rw [hφ_eq, hψ_eq]
      | succ n =>
          have hscalar :
              ∀ (φ : SchwartzNPoint d (n + 1)) (ψ : SchwartzNPoint d 0),
                Wfn.W ((n + 1) + 0) (φ.conjTensorProduct ψ) =
                  starRingEnd ℂ
                    (Wfn.W (0 + (n + 1)) (ψ.conjTensorProduct φ)) := by
            intro φ ψ
            let Fφ : BorchersSequence d := BorchersSequence.single (n + 1) φ
            let Gψ : BorchersSequence d := BorchersSequence.single 0 ψ
            have hFG :
                WightmanInnerProduct d Wfn.W Fφ Gψ =
                  Wfn.W ((n + 1) + 0) (φ.conjTensorProduct ψ) := by
              simpa [Fφ, Gψ] using
                WightmanInnerProduct_single_single (d := d) (W := Wfn.W)
                  (hlin := Wfn.linear)
                  (n := n + 1) (m := 0) (f := φ) (g := ψ)
            have hGF :
                WightmanInnerProduct d Wfn.W Gψ Fφ =
                  Wfn.W (0 + (n + 1)) (ψ.conjTensorProduct φ) := by
              simpa [Fφ, Gψ] using
                WightmanInnerProduct_single_single (d := d) (W := Wfn.W)
                  (hlin := Wfn.linear)
                  (n := 0) (m := n + 1) (f := ψ) (g := φ)
            have hherm :
                WightmanInnerProduct d Wfn.W Fφ Gψ =
                  starRingEnd ℂ
                    (WightmanInnerProduct d Wfn.W Gψ Fφ) :=
              WightmanInnerProduct_hermitian_of (d := d) (W := Wfn.W)
                Wfn.hermitian Fφ Gψ
            calc
              Wfn.W ((n + 1) + 0) (φ.conjTensorProduct ψ)
                  = WightmanInnerProduct d Wfn.W Fφ Gψ := hFG.symm
              _ = starRingEnd ℂ
                    (WightmanInnerProduct d Wfn.W Gψ Fφ) := hherm
              _ = starRingEnd ℂ
                    (Wfn.W (0 + (n + 1)) (ψ.conjTensorProduct φ)) := by
                    rw [hGF]
          have hflip :
              Wfn.W (0 + (n + 1)) (ψ₁.conjTensorProduct φ₁) =
                Wfn.W (0 + (n + 1)) (ψ₂.conjTensorProduct φ₂) :=
            rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight
              (d := d) (n := 0) (m := n) Wfn hSupp ψ₁ ψ₂ φ₁ φ₂ hψ hφ
          calc
            Wfn.W ((n + 1) + 0) (φ₁.conjTensorProduct ψ₁)
                = starRingEnd ℂ
                    (Wfn.W (0 + (n + 1)) (ψ₁.conjTensorProduct φ₁)) :=
                  hscalar φ₁ ψ₁
            _ = starRingEnd ℂ
                    (Wfn.W (0 + (n + 1)) (ψ₂.conjTensorProduct φ₂)) := by
                  rw [hflip]
            _ = Wfn.W ((n + 1) + 0) (φ₂.conjTensorProduct ψ₂) :=
                  (hscalar φ₂ ψ₂).symm

/-- Wightman tensor scalar descent through Section 4.3 frequency projections,
with the spectral-support package derived from the Wightman axioms. -/
theorem rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_from_wfn
    (Wfn : WightmanFunctions d)
    {n m : ℕ}
    (φ₁ φ₂ : SchwartzNPoint d n)
    (ψ₁ ψ₂ : SchwartzNPoint d m)
    (hφ :
      section43FrequencyProjection (d := d) n φ₁ =
        section43FrequencyProjection (d := d) n φ₂)
    (hψ :
      section43FrequencyProjection (d := d) m ψ₁ =
        section43FrequencyProjection (d := d) m ψ₂) :
    Wfn.W (n + m) (φ₁.conjTensorProduct ψ₁) =
      Wfn.W (n + m) (φ₂.conjTensorProduct ψ₂) :=
  rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
    (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    φ₁ φ₂ ψ₁ ψ₂ hφ hψ

/-- The R→E Wightman tensor scalar descended to the two Section 4.3 frequency
quotients. -/
noncomputable def rToESection43SpectralPairing
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (n m : ℕ) :
    Section43PositiveEnergyComponent (d := d) n →
      Section43PositiveEnergyComponent (d := d) m → ℂ := by
  intro u v
  refine Quotient.liftOn₂ u v
    (fun (Φ : SchwartzNPoint d n) (Ψ : SchwartzNPoint d m) =>
      Wfn.W (n + m)
        ((section43FrequencyRepresentativeInv d n Φ).conjTensorProduct
          (section43FrequencyRepresentativeInv d m Ψ))) ?_
  intro Φ₁ Ψ₁ Φ₂ Ψ₂ hΦ hΨ
  have hΦq :
      (Submodule.Quotient.mk Φ₁ : Section43PositiveEnergyComponent (d := d) n) =
        Submodule.Quotient.mk Φ₂ :=
    Quotient.sound hΦ
  have hΨq :
      (Submodule.Quotient.mk Ψ₁ : Section43PositiveEnergyComponent (d := d) m) =
        Submodule.Quotient.mk Ψ₂ :=
    Quotient.sound hΨ
  have hΦproj :
      section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n Φ₁) =
        section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n Φ₂) := by
    simpa [section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hΦq
  have hΨproj :
      section43FrequencyProjection (d := d) m
          (section43FrequencyRepresentativeInv d m Ψ₁) =
        section43FrequencyProjection (d := d) m
          (section43FrequencyRepresentativeInv d m Ψ₂) := by
    simpa [section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hΨq
  exact
    rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
      (d := d) Wfn hSupp
      (section43FrequencyRepresentativeInv d n Φ₁)
      (section43FrequencyRepresentativeInv d n Φ₂)
      (section43FrequencyRepresentativeInv d m Ψ₁)
      (section43FrequencyRepresentativeInv d m Ψ₂)
      hΦproj hΨproj

/-- Applying the descended R→E spectral pairing to actual frequency projections
recovers the original Wightman tensor scalar. -/
theorem rToESection43SpectralPairing_apply
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (n m : ℕ)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) :
    rToESection43SpectralPairing (d := d) Wfn hSupp n m
        (section43FrequencyProjection (d := d) n φ)
        (section43FrequencyProjection (d := d) m ψ) =
      Wfn.W (n + m) (φ.conjTensorProduct ψ) := by
  unfold rToESection43SpectralPairing section43FrequencyProjection
    section43PositiveEnergyQuotientMap
  change
    Wfn.W (n + m)
        ((section43FrequencyRepresentativeInv d n
            (section43FrequencyRepresentative (d := d) n φ)).conjTensorProduct
          (section43FrequencyRepresentativeInv d m
            (section43FrequencyRepresentative (d := d) m ψ))) =
      Wfn.W (n + m) (φ.conjTensorProduct ψ)
  have hφproj :
      section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n
            (section43FrequencyRepresentative (d := d) n φ)) =
        section43FrequencyProjection (d := d) n φ := by
    simp [section43FrequencyProjection, section43FrequencyRepresentativeInv_right]
  have hψproj :
      section43FrequencyProjection (d := d) m
          (section43FrequencyRepresentativeInv d m
            (section43FrequencyRepresentative (d := d) m ψ)) =
        section43FrequencyProjection (d := d) m ψ := by
    simp [section43FrequencyProjection, section43FrequencyRepresentativeInv_right]
  exact
    rToE_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
      (d := d) Wfn hSupp
      (section43FrequencyRepresentativeInv d n
        (section43FrequencyRepresentative (d := d) n φ))
      φ
      (section43FrequencyRepresentativeInv d m
        (section43FrequencyRepresentative (d := d) m ψ))
      ψ
      hφproj hψproj

/-- The R→E descended spectral pairing is continuous on the product of the two
Section 4.3 positive-energy frequency quotients. -/
theorem continuous_rToESection43SpectralPairing
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (n m : ℕ) :
    Continuous
      (fun p : Section43PositiveEnergyComponent (d := d) n ×
          Section43PositiveEnergyComponent (d := d) m =>
        rToESection43SpectralPairing (d := d) Wfn hSupp n m p.1 p.2) := by
  have hqn :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap (d := d) n :
          SchwartzNPoint d n → Section43PositiveEnergyComponent (d := d) n) := by
    simpa [section43PositiveEnergyQuotientMap] using
      (section43PositiveEnergyVanishingSubmodule (d := d) n).isOpenQuotientMap_mkQ
  have hqm :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap (d := d) m :
          SchwartzNPoint d m → Section43PositiveEnergyComponent (d := d) m) := by
    simpa [section43PositiveEnergyQuotientMap] using
      (section43PositiveEnergyVanishingSubmodule (d := d) m).isOpenQuotientMap_mkQ
  let invn : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    section43FrequencyRepresentativeInv d n
  let invm : SchwartzNPoint d m →L[ℂ] SchwartzNPoint d m :=
    section43FrequencyRepresentativeInv d m
  have hraw :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          Wfn.W (n + m)
            ((invn p.1).conjTensorProduct (invm p.2))) := by
    have hinv :
        Continuous
          (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
            (invn p.1, invm p.2)) :=
      (invn.continuous.comp continuous_fst).prodMk
        (invm.continuous.comp continuous_snd)
    have hct :
        Continuous
          (fun q : SchwartzNPoint d n × SchwartzNPoint d m =>
            q.1.conjTensorProduct q.2) :=
      conjTensorProduct_continuous_closure (d := d) (n := n) (m := m)
    have htensor_comp :
        Continuous
          ((fun q : SchwartzNPoint d n × SchwartzNPoint d m =>
              q.1.conjTensorProduct q.2) ∘
            fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
              (invn p.1, invm p.2)) :=
      hct.comp hinv
    have htensor :
        Continuous
          (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
            (invn p.1).conjTensorProduct (invm p.2)) := by
      simpa only [Function.comp] using htensor_comp
    exact (Wfn.tempered (n + m)).comp htensor
  refine (hqn.prodMap hqm).isQuotientMap.continuous_iff.2 ?_
  have hcomp :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          rToESection43SpectralPairing (d := d) Wfn hSupp n m
            (section43PositiveEnergyQuotientMap (d := d) n p.1)
            (section43PositiveEnergyQuotientMap (d := d) m p.2)) := by
    refine hraw.congr ?_
    intro p
    unfold rToESection43SpectralPairing section43PositiveEnergyQuotientMap
    rfl
  exact hcomp

/-- Canonical R→E Section 4.3 spectral pairing, with the support package derived
from the Wightman axioms. -/
noncomputable def rToESection43SpectralPairingOfWfn
    (Wfn : WightmanFunctions d)
    (n m : ℕ) :
    Section43PositiveEnergyComponent (d := d) n →
      Section43PositiveEnergyComponent (d := d) m → ℂ :=
  rToESection43SpectralPairing (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn) n m

/-- Applying the canonical descended R→E spectral pairing to actual frequency
projections recovers the original Wightman tensor scalar. -/
theorem rToESection43SpectralPairingOfWfn_apply
    (Wfn : WightmanFunctions d)
    (n m : ℕ)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) :
    rToESection43SpectralPairingOfWfn (d := d) Wfn n m
        (section43FrequencyProjection (d := d) n φ)
        (section43FrequencyProjection (d := d) m ψ) =
      Wfn.W (n + m) (φ.conjTensorProduct ψ) :=
  rToESection43SpectralPairing_apply (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    n m φ ψ

/-- Finite Section 4.3 quadratic form built from the R→E descended spectral
pairing. -/
noncomputable def rToE_finiteSection43Quadratic
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ) :
    Section43FiniteComponentProduct d B → ℂ :=
  fun u =>
    ∑ n : Fin (B + 1), ∑ m : Fin (B + 1),
      rToESection43SpectralPairing (d := d) Wfn hSupp n.val m.val
        (u n) (u m)

/-- The finite R→E Section 4.3 quadratic is continuous. -/
theorem continuous_rToE_finiteSection43Quadratic
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ) :
    Continuous (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B) := by
  unfold rToE_finiteSection43Quadratic
  refine continuous_finset_sum _ (fun n _hn => ?_)
  refine continuous_finset_sum _ (fun m _hm => ?_)
  have hcoords :
      Continuous
        (fun u : Section43FiniteComponentProduct d B => (u n, u m)) :=
    (continuous_apply n).prodMk (continuous_apply m)
  exact
    (continuous_rToESection43SpectralPairing
      (d := d) Wfn hSupp n.val m.val).comp hcoords

/-- Evaluating the finite R→E Section 4.3 quadratic on the component frequency
projections of a bounded Borchers sequence recovers the Wightman inner product.

This is the quotient-safe positivity entry point.  We do not choose arbitrary
representatives of quotient tuples here; we only use tuples that actually come
from Schwartz-space frequency projections. -/
theorem rToE_finiteSection43Quadratic_apply_borchers
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (F : BorchersSequence d)
    (hB : F.bound ≤ B) :
    rToE_finiteSection43Quadratic (d := d) Wfn hSupp B
        (fun n =>
          section43FrequencyProjection (d := d) n.val (F.funcs n.val)) =
      WightmanInnerProduct d Wfn.W F F := by
  have hF_eq :
      WightmanInnerProduct d Wfn.W F F =
        WightmanInnerProductN d Wfn.W F F (B + 1) (B + 1) := by
    exact WightmanInnerProduct_eq_extended (d := d) (W := Wfn.W)
      (hlin := Wfn.linear) (F := F) (G := F) (N₁ := B + 1) (N₂ := B + 1)
      (Nat.succ_le_succ hB) (Nat.succ_le_succ hB)
  rw [hF_eq]
  unfold rToE_finiteSection43Quadratic WightmanInnerProductN
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < B + 1 := Finset.mem_range.mp hn
  rw [dif_pos hnlt]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlt : m < B + 1 := Finset.mem_range.mp hm
  rw [dif_pos hmlt]
  exact rToESection43SpectralPairing_apply
    (d := d) Wfn hSupp n m (F.funcs n) (F.funcs m)

/-- Positivity of the finite R→E Section 4.3 quadratic on genuine frequency
projection tuples. -/
theorem rToE_finiteSection43Quadratic_nonneg_on_frequencyProjection
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (F : BorchersSequence d)
    (hB : F.bound ≤ B) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B
        (fun n =>
          section43FrequencyProjection (d := d) n.val (F.funcs n.val))).re := by
  rw [rToE_finiteSection43Quadratic_apply_borchers
    (d := d) Wfn hSupp B F hB]
  exact Wfn.positive_definite F

/-- Positivity of the finite R→E Section 4.3 quadratic on genuine frequency
projection tuples, with support derived from the Wightman axioms. -/
theorem rToE_finiteSection43Quadratic_nonneg_on_frequencyProjection_from_wfn
    (Wfn : WightmanFunctions d)
    (B : ℕ)
    (F : BorchersSequence d)
    (hB : F.bound ≤ B) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn
        (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn) B
        (fun n =>
          section43FrequencyProjection (d := d) n.val (F.funcs n.val))).re :=
  rToE_finiteSection43Quadratic_nonneg_on_frequencyProjection
    (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    B F hB

/-- The finite R→E Section 4.3 quadratic is nonnegative on the finite product
of genuine compact ordered Fourier-Laplace transform components.

This is the first OS-paper positivity form: compact positive-time test
functions are mapped by the Section 4.3 Fourier-Laplace transform carrier into
positive-energy frequency quotients, and the descended quadratic agrees there
with the original Wightman Hilbert-space quadratic. -/
theorem rToE_finiteSection43Quadratic_nonneg_on_finiteTransformComponentMap
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B
        (section43FiniteTransformComponentMap d B src)).re := by
  let A := section43FiniteSource_to_BvtTransformComponentSequence d B src
  have htuple :
      (fun n : Fin (B + 1) =>
        section43FrequencyProjection (d := d) n.val (A.toBorchers.funcs n.val)) =
        section43FiniteTransformComponentMap d B src := by
    funext n
    have hn : n.val ≤ B := Nat.lt_succ_iff.mp n.isLt
    have hfreq := A.freq_eq n.val
    simpa [A, section43FiniteSource_to_BvtTransformComponentSequence,
      section43FiniteSource_to_positiveTimeBorchersSequence,
      section43FiniteTransformComponentMap,
      section43FourierLaplaceTransformComponentMap, hn] using hfreq
  have hA_bound : A.toBorchers.bound ≤ B := by
    rfl
  have hquad :
      rToE_finiteSection43Quadratic (d := d) Wfn hSupp B
          (section43FiniteTransformComponentMap d B src) =
        WightmanInnerProduct d Wfn.W A.toBorchers A.toBorchers := by
    rw [← htuple]
    exact rToE_finiteSection43Quadratic_apply_borchers
      (d := d) Wfn hSupp B A.toBorchers hA_bound
  rw [hquad]
  exact Wfn.positive_definite A.toBorchers

/-- The canonical Wightman-axiom version of finite compact ordered
Fourier-Laplace transform positivity. -/
theorem rToE_finiteSection43Quadratic_nonneg_on_finiteTransformComponentMap_from_wfn
    (Wfn : WightmanFunctions d)
    (B : ℕ)
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn
        (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn) B
        (section43FiniteTransformComponentMap d B src)).re :=
  rToE_finiteSection43Quadratic_nonneg_on_finiteTransformComponentMap
    (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    B src

/-- Closed-set bridge for the finite R→E Section 4.3 quadratic: if a dense
family of finite component tuples has nonnegative quadratic value, then every
finite component tuple has nonnegative quadratic value. -/
theorem rToE_finiteSection43Quadratic_nonneg_of_denseRange
    {X : Type*}
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (T : X → Section43FiniteComponentProduct d B)
    (hT_dense : DenseRange T)
    (hT_nonneg :
      ∀ x : X,
        0 ≤
          (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B (T x)).re)
    (u : Section43FiniteComponentProduct d B) :
    0 ≤ (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B u).re := by
  let Q : Section43FiniteComponentProduct d B → ℂ :=
    rToE_finiteSection43Quadratic (d := d) Wfn hSupp B
  let S : Set (Section43FiniteComponentProduct d B) := {u | 0 ≤ (Q u).re}
  have hclosed : IsClosed S := by
    have hcont : Continuous (fun u : Section43FiniteComponentProduct d B => (Q u).re) :=
      Complex.continuous_re.comp
        (continuous_rToE_finiteSection43Quadratic (d := d) Wfn hSupp B)
    change IsClosed
      ((fun u : Section43FiniteComponentProduct d B => (Q u).re) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.preimage hcont
  have hrange : Set.range T ⊆ S := by
    rintro _ ⟨x, rfl⟩
    exact hT_nonneg x
  have hclosure_subset : closure (Set.range T) ⊆ S :=
    hclosed.closure_subset_iff.mpr hrange
  have hu_closure : u ∈ closure (Set.range T) := by
    rw [hT_dense.closure_eq]
    exact Set.mem_univ u
  exact hclosure_subset hu_closure

/-- Conditional finite-component R→E positivity: once the compact ordered
Section 4.3 Fourier-Laplace transform components are dense in each degree, the
descended finite quadratic is nonnegative on every finite component tuple. -/
theorem rToE_finiteSection43Quadratic_nonneg_of_component_denseRange
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (hdense :
      ∀ n : Fin (B + 1),
        DenseRange (section43FourierLaplaceTransformComponentMap d n.val))
    (u : Section43FiniteComponentProduct d B) :
    0 ≤ (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B u).re := by
  exact
    rToE_finiteSection43Quadratic_nonneg_of_denseRange
      (d := d) Wfn hSupp B
      (section43FiniteTransformComponentMap d B)
      (denseRange_section43FiniteTransformComponentMap_of_components d B hdense)
      (fun src =>
        rToE_finiteSection43Quadratic_nonneg_on_finiteTransformComponentMap
          (d := d) Wfn hSupp B src)
      u

/-- Canonical Wightman-axiom version of conditional finite-component R→E
positivity from componentwise dense range of compact ordered
Fourier-Laplace transform components. -/
theorem rToE_finiteSection43Quadratic_nonneg_of_component_denseRange_from_wfn
    (Wfn : WightmanFunctions d)
    (B : ℕ)
    (hdense :
      ∀ n : Fin (B + 1),
        DenseRange (section43FourierLaplaceTransformComponentMap d n.val))
    (u : Section43FiniteComponentProduct d B) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn
        (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn) B u).re :=
  rToE_finiteSection43Quadratic_nonneg_of_component_denseRange
    (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    B hdense u

/-- Conditional finite-component R→E positivity from the ambient-Schwartz
preimage-density form of the remaining analytic Fourier-Laplace density
theorem. -/
theorem rToE_finiteSection43Quadratic_nonneg_of_component_dense_preimage
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (hdense_pre :
      ∀ n : Fin (B + 1),
        Dense
          ((section43PositiveEnergyQuotientMap (d := d) n.val) ⁻¹'
            Set.range (section43FourierLaplaceTransformComponentMap d n.val)))
    (u : Section43FiniteComponentProduct d B) :
    0 ≤ (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B u).re :=
  rToE_finiteSection43Quadratic_nonneg_of_component_denseRange
    (d := d) Wfn hSupp B
    (fun n =>
      denseRange_section43FourierLaplaceTransformComponentMap_of_dense_preimage
        d n.val (hdense_pre n))
    u

/-- Canonical Wightman-axiom version of finite-component R→E positivity from
the ambient-Schwartz preimage-density form of the remaining analytic
Fourier-Laplace density theorem. -/
theorem rToE_finiteSection43Quadratic_nonneg_of_component_dense_preimage_from_wfn
    (Wfn : WightmanFunctions d)
    (B : ℕ)
    (hdense_pre :
      ∀ n : Fin (B + 1),
        Dense
          ((section43PositiveEnergyQuotientMap (d := d) n.val) ⁻¹'
            Set.range (section43FourierLaplaceTransformComponentMap d n.val)))
    (u : Section43FiniteComponentProduct d B) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn
        (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn) B u).re :=
  rToE_finiteSection43Quadratic_nonneg_of_component_dense_preimage
    (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    B hdense_pre u

/-- Unconditional finite-component R→E positivity, using the proved OS Section
4.3 compact ordered Fourier-Laplace density theorem. -/
theorem rToE_finiteSection43Quadratic_nonneg
    (Wfn : WightmanFunctions d)
    (hSupp : RToESection43WightmanSupport (d := d) Wfn)
    (B : ℕ)
    (u : Section43FiniteComponentProduct d B) :
    0 ≤ (rToE_finiteSection43Quadratic (d := d) Wfn hSupp B u).re :=
  rToE_finiteSection43Quadratic_nonneg_of_component_dense_preimage
    (d := d) Wfn hSupp B
    (fun n =>
      dense_section43FourierLaplace_compact_ordered_preimage_raw d n.val)
    u

/-- Canonical Wightman-axiom version of unconditional finite-component R→E
positivity. -/
theorem rToE_finiteSection43Quadratic_nonneg_from_wfn
    (Wfn : WightmanFunctions d)
    (B : ℕ)
    (u : Section43FiniteComponentProduct d B) :
    0 ≤
      (rToE_finiteSection43Quadratic (d := d) Wfn
        (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn) B u).re :=
  rToE_finiteSection43Quadratic_nonneg
    (d := d) Wfn
    (rToESection43WightmanSupport_of_wightmanFunctions (d := d) Wfn)
    B u

end OSReconstruction
