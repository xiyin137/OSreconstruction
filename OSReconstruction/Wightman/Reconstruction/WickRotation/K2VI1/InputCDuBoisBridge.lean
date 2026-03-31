import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCSwapSymmetry
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private def twoPointSwapMeasurableEquiv_bridge_local :
    NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin 2 => SpacetimeDim d)
    (Equiv.swap (0 : Fin 2) (1 : Fin 2))

private theorem twoPointSwapMeasurableEquiv_bridge_eq_local :
    ((twoPointSwapMeasurableEquiv_bridge_local (d := d)) :
      NPointDomain d 2 → NPointDomain d 2) =
        swapTwoPointAssembly_local (d := d) := by
  funext x
  let x' :
      (a : Fin 2) →
        (fun _ : Fin 2 => SpacetimeDim d) ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) a) := x
  funext i
  fin_cases i
  · simpa [twoPointSwapMeasurableEquiv_bridge_local, swapTwoPointAssembly_local] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
        (β := fun _ : Fin 2 => SpacetimeDim d)
        (x := x') (i := (1 : Fin 2)))
  · simpa [twoPointSwapMeasurableEquiv_bridge_local, swapTwoPointAssembly_local] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
        (β := fun _ : Fin 2 => SpacetimeDim d)
        (x := x') (i := (0 : Fin 2)))

/-- Swapping the two Euclidean points preserves Lebesgue measure. This is the
public change-of-variables wrapper needed by the final DuBois-Reymond route. -/
theorem swapTwoPointAssembly_measurePreserving_local :
    MeasureTheory.MeasurePreserving
      (swapTwoPointAssembly_local (d := d)) volume volume := by
  have hme :
      MeasureTheory.MeasurePreserving
        (twoPointSwapMeasurableEquiv_bridge_local (d := d)) volume volume := by
    simpa [twoPointSwapMeasurableEquiv_bridge_local] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin 2 => SpacetimeDim d)
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)))
  simpa [twoPointSwapMeasurableEquiv_bridge_eq_local (d := d)] using hme

/-- Swap change of variables for two-point Euclidean integrals. -/
theorem integral_comp_swapTwoPointAssembly_local
    (F : NPointDomain d 2 → ℂ) :
    ∫ x : NPointDomain d 2, F (swapTwoPointAssembly_local (d := d) x) =
      ∫ x : NPointDomain d 2, F x := by
  let e := twoPointSwapMeasurableEquiv_bridge_local (d := d)
  have hme :
      MeasureTheory.MeasurePreserving e volume volume := by
    simpa [e, twoPointSwapMeasurableEquiv_bridge_local] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin 2 => SpacetimeDim d)
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)))
  calc
    ∫ x : NPointDomain d 2, F (swapTwoPointAssembly_local (d := d) x)
      = ∫ x : NPointDomain d 2, F (((e : NPointDomain d 2 → NPointDomain d 2) x)) := by
          rw [twoPointSwapMeasurableEquiv_bridge_eq_local (d := d)]
    _ = ∫ x : NPointDomain d 2, F x := by
          exact hme.integral_comp' (f := e) (g := F)

/-- Any Schwartz two-point test supported in the positive time-ordering sector
is automatically a zero-diagonal Schwartz test. This is the direct bridge from
sector-supported smooth cutoffs into the `ZeroDiagonalSchwartz` interface used
by the `k = 2` OS route. -/
def zeroDiagonalSchwartz_of_tsupport_subset_posTimeSector_local
    (f : SchwartzNPoint d 2)
    (hf : tsupport (f : NPointDomain d 2 → ℂ) ⊆ posTimeSector_local (d := d)) :
    ZeroDiagonalSchwartz d 2 :=
  ⟨f, vanishesOnCoincidence_of_tsupport_subset_posTimeSector_local (d := d) f hf⟩

/-- Complex-valued compactly-supported smooth tests on the positive sector can
be lifted directly into `ZeroDiagonalSchwartz`. -/
def zeroDiagonalSchwartz_of_compactSupport_contDiff_subset_posTimeSector_local
    {f : NPointDomain d 2 → ℂ}
    (hf_compact : HasCompactSupport f)
    (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hf_tsupport : tsupport f ⊆ posTimeSector_local (d := d)) :
    ZeroDiagonalSchwartz d 2 := by
  let fS : SchwartzNPoint d 2 := hf_compact.toSchwartzMap hf_smooth
  have htsupport :
      tsupport ((fS : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ⊆
        posTimeSector_local (d := d) := by
    intro x hx
    have hx' : x ∈ tsupport (f : NPointDomain d 2 → ℂ) := by
      simpa [fS] using hx
    exact hf_tsupport hx'
  exact zeroDiagonalSchwartz_of_tsupport_subset_posTimeSector_local
    (d := d) fS htsupport

/-- For real scalar tests and complex kernels, the DuBois-Reymond pairing
`∫ g • Δ` is exactly the same as the complex integral `∫ (g : ℂ) * Δ`. -/
theorem integral_real_smul_eq_ofReal_mul_local
    (g : NPointDomain d 2 → ℝ)
    (Δ : NPointDomain d 2 → ℂ) :
    ∫ x, g x • Δ x = ∫ x, (↑(g x) : ℂ) * Δ x := by
  simp_rw [Complex.real_smul]

/-- DuBois-Reymond on the positive time-ordering sector, packaged in the
`ZeroDiagonalSchwartz` language used by the `k = 2` OS route.

If a locally integrable complex kernel `Δ` has zero pairing against every
complex Schwartz test supported in the positive sector, then it vanishes almost
everywhere on that sector. This is the exact bridge from sector-supported ZDS
pairings to the standard real-valued compactly supported `ContDiff` uniqueness
lemma in Mathlib. -/
theorem ae_eq_zero_on_posTimeSector_of_zeroDiagonal_pairing_eq_zero_local
    (Δ : NPointDomain d 2 → ℂ)
    (hΔ_loc : LocallyIntegrableOn Δ (posTimeSector_local (d := d)) volume)
    (hint : ∀ f : ZeroDiagonalSchwartz d 2,
      Function.support (f.1 : NPointDomain d 2 → ℂ) ⊆ posTimeSector_local (d := d) →
      ∫ x : NPointDomain d 2, Δ x * (f.1 x) = 0) :
    ∀ᵐ x : NPointDomain d 2 ∂volume,
      x ∈ posTimeSector_local (d := d) → Δ x = 0 := by
  refine (isOpen_posTimeSector_local (d := d)).ae_eq_zero_of_integral_contDiff_smul_eq_zero hΔ_loc ?_
  intro g hg_smooth hg_compact hg_tsupport
  have hgC_smooth :
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => (g x : ℂ)) := by
    rw [contDiff_infty] at hg_smooth
    rw [contDiff_infty]
    intro n
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hg_smooth n)
  have hgC_compact :
      HasCompactSupport (fun x : NPointDomain d 2 => (g x : ℂ)) := by
    exact hg_compact.comp_left Complex.ofReal_zero
  let gSch : SchwartzNPoint d 2 := hgC_compact.toSchwartzMap hgC_smooth
  have hgSch_eval :
      ∀ x : NPointDomain d 2, gSch x = (g x : ℂ) :=
    HasCompactSupport.toSchwartzMap_toFun hgC_compact hgC_smooth
  have hgSch_tsupport :
      tsupport ((gSch : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ⊆
        posTimeSector_local (d := d) := by
    intro x hx
    have hSuppEqC :
        Function.support ((gSch : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) =
          Function.support (fun y : NPointDomain d 2 => (g y : ℂ)) := by
      ext y
      simp [hgSch_eval y]
    have hx_tsupportC : x ∈ tsupport (fun y : NPointDomain d 2 => (g y : ℂ)) := by
      simpa [tsupport, hSuppEqC] using hx
    have hSuppEqR :
        Function.support (fun y : NPointDomain d 2 => (g y : ℂ)) =
          Function.support g := by
      ext y
      simp [Complex.ofReal_eq_zero]
    have hx_tsupportR : x ∈ tsupport g := by
      simpa [tsupport, hSuppEqR] using hx_tsupportC
    exact hg_tsupport hx_tsupportR
  let gS : ZeroDiagonalSchwartz d 2 :=
    zeroDiagonalSchwartz_of_tsupport_subset_posTimeSector_local
      (d := d) gSch hgSch_tsupport
  have hgS_eval :
      ∀ x : NPointDomain d 2, gS.1 x = (g x : ℂ) := by
    intro x
    simpa [gS] using hgSch_eval x
  have hgS_support :
      Function.support (gS.1 : NPointDomain d 2 → ℂ) ⊆ posTimeSector_local (d := d) := by
    intro x hx
    have hx_tsupport :
        x ∈ tsupport (gS.1 : NPointDomain d 2 → ℂ) := subset_closure hx
    exact hgSch_tsupport (by simpa [gS] using hx_tsupport)
  have hzeroC :
      ∫ x : NPointDomain d 2, (↑(g x) : ℂ) * Δ x = 0 := by
    calc
      ∫ x : NPointDomain d 2, (↑(g x) : ℂ) * Δ x
          = ∫ x : NPointDomain d 2, Δ x * (gS.1 x) := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [hgS_eval x, mul_comm]
      _ = 0 := hint gS hgS_support
  calc
    ∫ x : NPointDomain d 2, g x • Δ x
        = ∫ x : NPointDomain d 2, (↑(g x) : ℂ) * Δ x :=
          integral_real_smul_eq_ofReal_mul_local (d := d) g Δ
    _ = 0 := hzeroC

end OSReconstruction
