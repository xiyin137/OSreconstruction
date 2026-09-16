import OSReconstruction.Wightman.Reconstruction.Core

/-!
# Configuration translations on n-point Schwartz space

This file contains the generic operation of translating every spacetime slot
of an `n`-point Schwartz function by an independently prescribed
displacement.  Quantitative growth estimates and Chapter V differentiation
properties live in their respective downstream modules.
-/

noncomputable section

open Set

namespace OSReconstruction

/-- Translate every spacetime slot of an `n`-point Schwartz function by its
own displacement. -/
def translateSchwartzConfiguration
    {d n : ℕ}
    (a : NPointDomain d n) (f : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  ⟨fun x => f (x + a),
   f.smooth'.comp (contDiff_id.add contDiff_const),
   fun k l => by
     obtain ⟨Ck, hCk⟩ := f.decay' k l
     obtain ⟨C0, hC0⟩ := f.decay' 0 l
     have hderiv :
         ∀ x,
           iteratedFDeriv ℝ l (fun z => f.toFun (z + a)) x =
             iteratedFDeriv ℝ l f.toFun (x + a) :=
       fun x => iteratedFDeriv_comp_add_right l a x
     have hC0' :
         ∀ y, ‖iteratedFDeriv ℝ l f.toFun y‖ ≤ C0 := by
       intro y
       have hy := hC0 y
       simpa using hy
     refine
       ⟨2 ^ (k - 1) * (Ck + ‖a‖ ^ k * C0), fun x => ?_⟩
     show
       ‖x‖ ^ k *
           ‖iteratedFDeriv ℝ l (fun z => f.toFun (z + a)) x‖ ≤
         _
     rw [hderiv]
     have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
       calc
         ‖x‖ = ‖(x + a) - a‖ := by ring_nf
         _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
     calc
       ‖x‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖
           ≤ (‖x + a‖ + ‖a‖) ^ k *
               ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
             gcongr
       _ ≤
           (2 ^ (k - 1) * (‖x + a‖ ^ k + ‖a‖ ^ k)) *
             ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
             gcongr
             exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
       _ =
           2 ^ (k - 1) *
             (‖x + a‖ ^ k *
                 ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ +
               ‖a‖ ^ k *
                 ‖iteratedFDeriv ℝ l f.toFun (x + a)‖) := by
             ring
       _ ≤ 2 ^ (k - 1) * (Ck + ‖a‖ ^ k * C0) := by
             gcongr
             · exact hCk (x + a)
             · exact hC0' (x + a)⟩

@[simp]
theorem translateSchwartzConfiguration_apply
    {d n : ℕ}
    (a : NPointDomain d n) (f : SchwartzNPoint d n)
    (x : NPointDomain d n) :
    translateSchwartzConfiguration a f x = f (x + a) :=
  rfl

@[simp]
theorem translateSchwartzConfiguration_zero
    {d n : ℕ}
    (f : SchwartzNPoint d n) :
    translateSchwartzConfiguration 0 f = f := by
  ext x
  simp

theorem translateSchwartzConfiguration_translateSchwartzConfiguration
    {d n : ℕ}
    (a b : NPointDomain d n) (f : SchwartzNPoint d n) :
    translateSchwartzConfiguration a
        (translateSchwartzConfiguration b f) =
      translateSchwartzConfiguration (a + b) f := by
  ext x
  simp [add_assoc]

/-- Fixed independent translations as a continuous linear operation on the
full configuration Schwartz space. -/
noncomputable def translateSchwartzConfigurationCLM
    {d n : ℕ}
    (a : NPointDomain d n) :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n := by
  let g : NPointDomain d n → NPointDomain d n := fun x => x + a
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper :
      ∃ (m : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ m := by
    refine ⟨1, 1 + ‖a‖, ?_⟩
    intro x
    have htri : ‖x‖ ≤ ‖g x‖ + ‖a‖ := by
      calc
        ‖x‖ = ‖(x + a) - a‖ := by simp
        _ ≤ ‖g x‖ + ‖a‖ := by
          simpa [g] using norm_sub_le (x + a) a
    have hfac :
        ‖g x‖ + ‖a‖ ≤ (1 + ‖a‖) * (1 + ‖g x‖) := by
      nlinarith [norm_nonneg (g x), norm_nonneg a]
    simpa using htri.trans hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem translateSchwartzConfigurationCLM_apply
    {d n : ℕ}
    (a : NPointDomain d n) (f : SchwartzNPoint d n) :
    translateSchwartzConfigurationCLM a f =
      translateSchwartzConfiguration a f := by
  ext x
  rfl

namespace OSIIChapterV

/-- Translation carries Schwartz support by the corresponding additive
homeomorphism. -/
theorem tsupport_translateSchwartz_eq_preimage
    {m : ℕ}
    (s : Fin m → ℝ)
    (η : SchwartzMap (Fin m → ℝ) ℂ) :
    tsupport
        ((SCV.translateSchwartz s η :
          SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) =
      (Homeomorph.addRight s) ⁻¹'
        tsupport (η : (Fin m → ℝ) → ℂ) := by
  change closure (Function.support (fun x : Fin m → ℝ => η (x + s))) = _
  simpa [tsupport, Function.comp_def] using
    (tsupport_comp_eq_preimage
      (g := (η : (Fin m → ℝ) → ℂ))
      (Homeomorph.addRight s))

end OSIIChapterV

end OSReconstruction
