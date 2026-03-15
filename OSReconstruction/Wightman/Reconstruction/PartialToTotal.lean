import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section

open ContinuousLinearMap

namespace OSReconstruction

/-- If `g : ℝ × E → F` has Fréchet derivatives in each variable at `(a, b)` and
the mixed remainder is `o(‖(h₁, h₂)‖)`, then `g` has the expected total
Fréchet derivative on the product. This packages the standard FTC+DCT style
combination used in the interval-piece argument. -/
theorem hasFDerivAt_of_hasDerivAt_fst_hasFDerivAt_snd
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : ℝ × E → F} {a : ℝ} {b : E}
    {d₁ : F} {d₂ : E →L[ℝ] F}
    (hg₁ : HasFDerivAt (fun x : ℝ => g (x, b)) (smulRight (1 : ℝ →L[ℝ] ℝ) d₁) a)
    (hg₂ : HasFDerivAt (fun y => g (a, y)) d₂ b)
    (hcross : ∀ ε > 0, ∃ δ > 0, ∀ h₁ : ℝ, ∀ h₂ : E,
      ‖h₁‖ < δ → ‖h₂‖ < δ →
        ‖g (a + h₁, b + h₂) - g (a + h₁, b) - g (a, b + h₂) + g (a, b)‖ ≤
          ε * (‖h₁‖ + ‖h₂‖)) :
    HasFDerivAt g (smulRight (fst ℝ ℝ E) d₁ + d₂.comp (snd ℝ ℝ E)) (a, b) := by
  simp only [hasFDerivAt_iff_isLittleO_nhds_zero] at hg₁ hg₂ ⊢
  set R₁ := fun h : ℝ × E => g (a + h.1, b) - g (a, b) - (smulRight (1 : ℝ →L[ℝ] ℝ) d₁) h.1
  set R₂ := fun h : ℝ × E => g (a, b + h.2) - g (a, b) - d₂ h.2
  set R₃ := fun h : ℝ × E => g (a + h.1, b + h.2) - g (a + h.1, b) - g (a, b + h.2) + g (a, b)
  set R := fun h : ℝ × E => g ((a, b) + h) - g (a, b) -
    ((fst ℝ ℝ E).smulRight d₁ + d₂.comp (snd ℝ ℝ E)) h
  have hR_eq : ∀ h, R h = R₁ h + R₂ h + R₃ h := by
    intro h
    simp only [R, R₁, R₂, R₃, Prod.add_def, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      smulRight_apply, one_apply]
    abel
  show R =o[nhds 0] fun h => h
  rw [show R = fun h => R₁ h + R₂ h + R₃ h from funext hR_eq]
  apply Asymptotics.IsLittleO.add
  apply Asymptotics.IsLittleO.add
  ·
    have : (fun h : ℝ × E => R₁ h) =o[nhds (0 : ℝ × E)] fun h => h := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      rw [Asymptotics.isLittleO_iff] at hg₁
      obtain ⟨s, hs, hbound⟩ := (hg₁ hc).exists_mem
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hδ] with h hh
      have hh_fst : h.1 ∈ s := by
        apply hball
        calc
          dist h.1 0 = ‖h.1‖ := by simp [dist_zero_right]
          _ ≤ ‖h‖ := norm_fst_le h
          _ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hh
      calc
        ‖R₁ h‖ ≤ c * ‖h.1‖ := hbound h.1 hh_fst
        _ ≤ c * ‖h‖ := by gcongr; exact norm_fst_le h
    exact this
  ·
    have : (fun h : ℝ × E => R₂ h) =o[nhds (0 : ℝ × E)] fun h => h := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      rw [Asymptotics.isLittleO_iff] at hg₂
      obtain ⟨s, hs, hbound⟩ := (hg₂ hc).exists_mem
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hδ] with h hh
      have hh_snd : h.2 ∈ s := by
        apply hball
        calc
          dist h.2 0 = ‖h.2‖ := by simp [dist_zero_right]
          _ ≤ ‖h‖ := norm_snd_le h
          _ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hh
      calc
        ‖R₂ h‖ ≤ c * ‖h.2‖ := hbound h.2 hh_snd
        _ ≤ c * ‖h‖ := by gcongr; exact norm_snd_le h
    exact this
  ·
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨δ, hδ, hball⟩ := hcross (c / 2) (by positivity)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hδ] with h hh
    rw [Metric.mem_ball, dist_zero_right] at hh
    have hh1 : ‖h.1‖ < δ := lt_of_le_of_lt (norm_fst_le h) hh
    have hh2 : ‖h.2‖ < δ := lt_of_le_of_lt (norm_snd_le h) hh
    calc
      ‖R₃ h‖ = ‖g (a + h.1, b + h.2) - g (a + h.1, b) - g (a, b + h.2) + g (a, b)‖ := rfl
      _ ≤ (c / 2) * (‖h.1‖ + ‖h.2‖) := hball h.1 h.2 hh1 hh2
      _ ≤ (c / 2) * (‖h‖ + ‖h‖) := by
        gcongr
        · exact norm_fst_le h
        · exact norm_snd_le h
      _ = c * ‖h‖ := by ring

end OSReconstruction
