import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice

/-!
# Section 4.3 Fourier-Laplace Density

This file contains the pure-analysis density packet needed by the final
Section 4.3 positivity closure.  It deliberately stays below the Wightman /
OS-Hilbert layers: the theorems here should mention only Schwartz maps,
Fourier-Laplace kernels, and the positive-energy quotient.
-/

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Compact Schwartz source on the strict positive half-line.  The strict
support condition is the one-dimensional analogue of compact support inside
`OrderedPositiveTimeRegion`. -/
structure Section43CompactPositiveTimeSource1D where
  f : SchwartzMap ℝ ℂ
  positive :
    tsupport (f : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)
  compact : HasCompactSupport (f : ℝ → ℂ)

/-- A one-dimensional ambient representative of the compact one-sided Laplace
transform, modulo equality on the closed half-line. -/
def section43OneSidedLaplaceRepresentative1D
    (g : Section43CompactPositiveTimeSource1D)
    (Φ : SchwartzMap ℝ ℂ) : Prop :=
  ∀ σ : ℝ, 0 ≤ σ →
    Φ σ =
      ∫ t : ℝ,
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t

/-- The raw one-sided Laplace scalar associated to a compact strict-positive
source. -/
noncomputable def section43OneSidedLaplaceRaw
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t

theorem Section43CompactPositiveTimeSource1D.tsupport_subset_Ici
    (g : Section43CompactPositiveTimeSource1D) :
    tsupport (g.f : ℝ → ℂ) ⊆ Set.Ici (0 : ℝ) := by
  intro t ht
  exact le_of_lt (Set.mem_Ioi.mp (g.positive ht))

theorem section43OneSidedLaplaceRaw_eq_complexLaplaceTransform
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) :
    section43OneSidedLaplaceRaw g σ =
      section43ComplexLaplaceTransform (g.f : ℝ → ℂ) (σ : ℂ) := by
  unfold section43OneSidedLaplaceRaw section43ComplexLaplaceTransform
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  congr 1
  ring_nf

theorem section43OneSidedLaplaceRaw_integrable_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable
      (fun t : ℝ =>
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t) := by
  have hbase :=
    section43ComplexLaplaceTransform_integrable_of_nonneg_re
      (f := g.f) g.tsupport_subset_Ici (σ : ℂ) (by simpa using hσ)
  refine hbase.congr ?_
  filter_upwards with t
  congr 1
  ring_nf

theorem section43OneSidedLaplaceRaw_eq_fourierInvPairingCanonicalExtension_of_pos
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 < σ) :
    section43OneSidedLaplaceRaw g σ =
      section43FourierInvPairingCanonicalExtension g.f
        ((σ / (2 * Real.pi)) * Complex.I) := by
  rw [section43OneSidedLaplaceRaw_eq_complexLaplaceTransform]
  exact section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos
    (f := g.f) g.tsupport_subset_Ici hσ

theorem section43SmoothCutoff_complex_iteratedFDeriv_support_subset_Ici_neg_one :
    ∀ r : ℕ, ∀ σ : ℝ,
      iteratedFDeriv ℝ r (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ ≠ 0 →
        σ ∈ Set.Ici (-1 : ℝ) := by
  intro r σ hne
  by_contra hσ_mem
  have hσ_lt : σ < -1 := by
    simpa [Set.mem_Ici, not_le] using hσ_mem
  have hEqNeg : Set.EqOn (fun ξ : ℝ => (SCV.smoothCutoff ξ : ℂ))
      (fun _ => 0) (Set.Iio (-1 : ℝ)) := by
    intro ξ hξ
    show (SCV.smoothCutoff ξ : ℂ) = 0
    exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one (le_of_lt hξ)
  have hDerivNeg : Set.EqOn
      (iteratedDeriv r (fun ξ : ℝ => (SCV.smoothCutoff ξ : ℂ)))
      (fun _ => 0) (Set.Iio (-1 : ℝ)) :=
    hEqNeg.iteratedDeriv_of_isOpen isOpen_Iio r |>.trans
      (by intro x _; simp)
  have hderiv_zero :
      iteratedDeriv r (fun ξ : ℝ => (SCV.smoothCutoff ξ : ℂ)) σ = 0 :=
    hDerivNeg (Set.mem_Iio.mpr hσ_lt)
  have hF_zero :
      iteratedFDeriv ℝ r (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hderiv_zero, norm_zero]
  exact hne hF_zero

noncomputable def section43OneSidedLaplaceCutoffFun
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) : ℂ :=
  (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ

theorem section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    section43OneSidedLaplaceCutoffFun g σ =
      section43OneSidedLaplaceRaw g σ := by
  change (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ =
    section43OneSidedLaplaceRaw g σ
  have hcut : (SCV.smoothCutoff σ : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hσ
  rw [hcut]
  simp

/-- Compact support inside the strict positive half-line is uniformly separated
from the boundary. -/
theorem exists_positive_margin_of_compact_tsupport_subset_Ioi
    (g : SchwartzMap ℝ ℂ)
    (hg_pos : tsupport (g : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hg_compact : HasCompactSupport (g : ℝ → ℂ)) :
    ∃ δ > 0, tsupport (g : ℝ → ℂ) ⊆ Set.Ici δ := by
  classical
  let K : Set ℝ := tsupport (g : ℝ → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hg_compact
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hx0_min⟩ :=
      hK_compact.exists_isMinOn hne continuous_id.continuousOn
    have hx0_pos : 0 < x0 := hg_pos hx0
    refine ⟨x0 / 2, by linarith, ?_⟩
    intro x hx
    have hle : x0 ≤ x := isMinOn_iff.mp hx0_min x hx
    exact Set.mem_Ici.mpr (by linarith)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

theorem exists_Icc_bounds_of_compact_tsupport_subset_Ici
    (g : SchwartzMap ℝ ℂ)
    {δ : ℝ}
    (hδ : tsupport (g : ℝ → ℂ) ⊆ Set.Ici δ)
    (hg_compact : HasCompactSupport (g : ℝ → ℂ)) :
    ∃ R, δ ≤ R ∧ tsupport (g : ℝ → ℂ) ⊆ Set.Icc δ R := by
  classical
  let K : Set ℝ := tsupport (g : ℝ → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hg_compact
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hx0_max⟩ :=
      hK_compact.exists_isMaxOn hne continuous_id.continuousOn
    have hδx0 : δ ≤ x0 := hδ hx0
    refine ⟨x0, hδx0, ?_⟩
    intro x hx
    exact Set.mem_Icc.mpr ⟨hδ hx, isMaxOn_iff.mp hx0_max x hx⟩
  · refine ⟨δ, le_rfl, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

theorem exists_positive_Icc_bounds_of_compactPositiveTimeSource
    (g : Section43CompactPositiveTimeSource1D) :
    ∃ δ R, 0 < δ ∧ δ ≤ R ∧
      tsupport (g.f : ℝ → ℂ) ⊆ Set.Icc δ R := by
  rcases exists_positive_margin_of_compact_tsupport_subset_Ioi
      g.f g.positive g.compact with
    ⟨δ, hδ_pos, hδ_supp⟩
  rcases exists_Icc_bounds_of_compact_tsupport_subset_Ici
      (g := g.f) hδ_supp g.compact with
    ⟨R, hδR, hR⟩
  exact ⟨δ, R, hδ_pos, hδR, hR⟩

/-- Local name for Mathlib's inverse Fourier continuous linear map on
one-dimensional Schwartz space. -/
noncomputable def section43FourierInvCLM1D :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)

@[simp] theorem section43FourierInvCLM1D_apply
    (φ : SchwartzMap ℝ ℂ) :
    section43FourierInvCLM1D φ = FourierTransform.fourierInv φ := rfl

/-- Turn a continuous functional on the half-line quotient into a tempered
functional with one-sided Fourier support by precomposing with inverse Fourier
transform. -/
noncomputable def section43PositiveEnergy1D_to_oneSidedFourierFunctional
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  (A.comp section43PositiveEnergyQuotientMap1D).comp
    section43FourierInvCLM1D

/-- The inverse-Fourier pullback of a half-line quotient functional has
one-sided Fourier support. -/
theorem section43PositiveEnergy1D_to_oneSidedFourierFunctional_support
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    SCV.HasOneSidedFourierSupport
      (section43PositiveEnergy1D_to_oneSidedFourierFunctional A) := by
  intro φ hφ
  dsimp [section43PositiveEnergy1D_to_oneSidedFourierFunctional,
    section43FourierInvCLM1D]
  rw [FourierTransform.fourierInv_fourier_eq]
  have hEqOn : Set.EqOn (φ : ℝ → ℂ) (0 : ℝ → ℂ) (Set.Ici (0 : ℝ)) := by
    intro x hx
    by_contra hne
    have hx_supp : x ∈ Function.support (φ : ℝ → ℂ) := by
      simpa [Function.mem_support] using hne
    have hx_neg := hφ x hx_supp
    exact (not_lt_of_ge hx) hx_neg
  have hqzero : section43PositiveEnergyQuotientMap1D φ = 0 := by
    have hsub :=
      section43PositiveEnergyQuotientMap1D_sub_eq_zero_of_eqOn_nonneg
        (f := φ) (g := 0) hEqOn
    simpa using hsub
  rw [hqzero]
  simp

/-- Descending the inverse-Fourier pullback functional recovers the original
half-line quotient functional. -/
theorem fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    fourierPairingDescendsToSection43PositiveEnergy1D
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional A)
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional_support A)
      = A := by
  ext u
  obtain ⟨φ, hφ⟩ := surjective_section43PositiveEnergyQuotientMap1D u
  rw [← hφ]
  rw [fourierPairingDescendsToSection43PositiveEnergy1D_apply]
  dsimp [section43PositiveEnergy1D_to_oneSidedFourierFunctional,
    section43FourierInvCLM1D]
  rw [FourierTransform.fourierInv_fourier_eq]

/-- Fourier-Laplace transform of a half-line quotient functional, expressed via
the existing `SCV.schwartzPsiZ` kernel. -/
noncomputable def section43OneSidedAnnihilatorFL
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) : ℂ :=
  A (section43PositiveEnergyQuotientMap1D (SCV.schwartzPsiZ z hz))

theorem section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    section43OneSidedAnnihilatorFL A z hz =
      SCV.fourierLaplaceExt
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional A) z hz := by
  rw [SCV.fourierLaplaceExt_eq]
  dsimp [section43OneSidedAnnihilatorFL,
    section43PositiveEnergy1D_to_oneSidedFourierFunctional,
    section43FourierInvCLM1D]
  rw [FourierTransform.fourierInv_fourier_eq]

/-- Imaginary-axis version of `section43OneSidedAnnihilatorFL`, with an
off-half-line zero branch to avoid dependent positivity proofs inside
integrals. -/
noncomputable def section43OneSidedAnnihilatorFLOnImag
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (t : ℝ) : ℂ :=
  if ht : 0 < t then
    section43OneSidedAnnihilatorFL A ((t : ℂ) * Complex.I)
      (by simpa using ht)
  else
    0

@[simp] theorem section43OneSidedAnnihilatorFLOnImag_of_pos
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    {t : ℝ} (ht : 0 < t) :
    section43OneSidedAnnihilatorFLOnImag A t =
      section43OneSidedAnnihilatorFL A ((t : ℂ) * Complex.I)
        (by simpa using ht) := by
  simp [section43OneSidedAnnihilatorFLOnImag, ht]

theorem section43OneSidedAnnihilatorFLOnImag_of_not_pos
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    {t : ℝ} (ht : ¬ 0 < t) :
    section43OneSidedAnnihilatorFLOnImag A t = 0 := by
  simp [section43OneSidedAnnihilatorFLOnImag, ht]

theorem section43PositiveEnergy1D_ext_of_FL_zero
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hFL :
      ∀ (z : ℂ) (hz : 0 < z.im),
        section43OneSidedAnnihilatorFL A z hz = 0) :
    A = 0 := by
  let T := section43PositiveEnergy1D_to_oneSidedFourierFunctional A
  have hT_supp : SCV.HasOneSidedFourierSupport T := by
    simpa [T] using section43PositiveEnergy1D_to_oneSidedFourierFunctional_support A
  have hT_zero : T = 0 := by
    ext φ
    have hpw := (SCV.paley_wiener_half_line_explicit T hT_supp).2.2 φ
    have hEventually_zero :
        (fun η : ℝ =>
          ∫ x : ℝ,
            (if hw : 0 < (↑x + ↑η * Complex.I).im then
              SCV.fourierLaplaceExt T
                ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (↑x + ↑η * Complex.I).im :=
                    mul_pos Real.two_pi_pos hw
                  simpa [Complex.mul_im] using hscaled)
            else 0) * φ x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun _ : ℝ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη_pos : 0 < η := by simpa using hη
      apply integral_eq_zero_of_ae
      filter_upwards with x
      have hw : 0 < (↑x + ↑η * Complex.I).im := by
        simpa using hη_pos
      have hscaled :
          0 < ((((2 * Real.pi : ℝ) : ℂ) *
            (↑x + ↑η * Complex.I)).im) := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      have hz0 :
          SCV.fourierLaplaceExt T
              ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) hscaled =
            0 := by
        have hEq :=
          section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
            (A := A)
            ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) hscaled
        simpa [T] using (hEq.symm.trans (hFL _ hscaled))
      rw [dif_pos hw]
      rw [show
          SCV.fourierLaplaceExt T
              ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) _ =
            0 by
          convert hz0 using 1]
      simp
    have hlim_zero :
        Tendsto
          (fun η : ℝ =>
            ∫ x : ℝ,
              (if hw : 0 < (↑x + ↑η * Complex.I).im then
                SCV.fourierLaplaceExt T
                  ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I)))
                  (by
                    have hscaled : 0 < (2 * Real.pi) *
                        (↑x + ↑η * Complex.I).im :=
                      mul_pos Real.two_pi_pos hw
                    simpa [Complex.mul_im] using hscaled)
              else 0) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      (tendsto_congr' hEventually_zero).2 tendsto_const_nhds
    exact tendsto_nhds_unique hpw hlim_zero
  have hdesc := fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided A
  rw [← hdesc]
  ext u
  obtain ⟨φ, hφ⟩ := surjective_section43PositiveEnergyQuotientMap1D u
  rw [← hφ]
  rw [fourierPairingDescendsToSection43PositiveEnergy1D_apply]
  have hTφ : T ((SchwartzMap.fourierTransformCLM ℂ) φ) = 0 := by
    rw [hT_zero]
    rfl
  simpa [T] using hTφ

end OSReconstruction
