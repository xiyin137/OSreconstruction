import OSReconstruction.Mathlib429Compat
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz

open scoped SchwartzMap

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace OSReconstruction

variable {n : ℕ}

/-- A continuous Schwartz functional on `Fin (n + 1) → ℝ` is head-translation
invariant if translating only the distinguished head coordinate leaves it
unchanged. This is the one-variable factorization surface behind the OS
"active time variable, remaining variables as parameters" mechanism. -/
def IsHeadTranslationInvariantSchwartzCLM
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ a : ℝ, T.comp (SCV.translateSchwartzCLM (Fin.cons a 0)) = T

/-- Head-translation-invariant Schwartz functionals annihilate the head
directional derivative. -/
theorem map_lineDeriv_eq_zero_of_headTranslationInvariant
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (f : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    T (LineDeriv.lineDerivOp ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) f) = 0 := by
  let e0 : Fin (n + 1) → ℝ := Pi.single 0 1
  have hquot :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (SCV.translateSchwartz (t • e0) f - f)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (T (LineDeriv.lineDerivOp e0 f))) :=
    (T.continuous.tendsto (LineDeriv.lineDerivOp e0 f)).comp
      (tendsto_diffQuotient_translateSchwartz_zero f e0)
  have hzero :
      Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) :=
    tendsto_const_nhds
  have he0 : ∀ t : ℝ, t • e0 = Fin.cons t 0 := by
    intro t
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [e0]
    · intro j
      simp [e0]
  have heq :
      (fun t : ℝ => T (t⁻¹ • (SCV.translateSchwartz (t • e0) f - f))) = fun _ => (0 : ℂ) := by
    funext t
    have htrans :
        T (SCV.translateSchwartz (t • e0) f) = T f := by
      have := congrArg
        (fun S : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ => S f)
        (hT t)
      simpa [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply, he0 t] using this
    rw [T.map_smul_of_tower, map_sub, sub_eq_zero.mpr htrans, smul_zero]
  have hzero' :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (SCV.translateSchwartz (t • e0) f - f)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa only [heq] using hzero
  exact tendsto_nhds_unique hquot hzero'

/-- A Schwartz test with zero head slice integral lies in the kernel of every
head-translation-invariant functional. This is the one-step factorization
theorem through `sliceIntegral`. -/
theorem map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : sliceIntegral F = 0) :
    T F = 0 := by
  have hzero' : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0 := by
    intro y
    have hy := congrArg (fun G : SchwartzMap (Fin n → ℝ) ℂ => G y) hzero
    simpa [sliceIntegral_apply, sliceIntegralRaw] using hy
  have hderiv :
      LineDeriv.lineDerivOp ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)
        (fiberwiseAntideriv F hzero') = F := by
    ext v
    simpa [SchwartzMap.lineDerivOp_apply] using
      lineDeriv_fiberwiseAntideriv F hzero' v
  rw [← hderiv]
  exact map_lineDeriv_eq_zero_of_headTranslationInvariant T hT (fiberwiseAntideriv F hzero')

/-- Two Schwartz tests with the same head slice integral are indistinguishable
to any head-translation-invariant functional. -/
theorem map_eq_of_sliceIntegral_eq_of_headTranslationInvariant
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (F G : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hFG : sliceIntegral F = sliceIntegral G) :
    T F = T G := by
  have hFG' : sliceIntegral (F - G) = 0 := by
    ext y
    have hy := congrArg (fun H : SchwartzMap (Fin n → ℝ) ℂ => H y) hFG
    have hy' : ∫ x : ℝ, F (Fin.cons x y) = ∫ x : ℝ, G (Fin.cons x y) := by
      simpa [sliceIntegral_apply, sliceIntegralRaw] using hy
    have hsub :
        ∫ x : ℝ, (F - G) (Fin.cons x y) =
          (∫ x : ℝ, F (Fin.cons x y)) - (∫ x : ℝ, G (Fin.cons x y)) := by
      rw [show (fun x : ℝ => (F - G) (Fin.cons x y)) =
          (fun x : ℝ => F (Fin.cons x y) - G (Fin.cons x y)) by
            funext x
            simp [SchwartzMap.sub_apply]]
      exact MeasureTheory.integral_sub
        (integrable_sliceSection F y)
        (integrable_sliceSection G y)
    rw [sliceIntegral_apply, sliceIntegralRaw, hsub]
    show (∫ x : ℝ, F (Fin.cons x y)) - (∫ x : ℝ, G (Fin.cons x y)) = (0 : ℂ)
    exact sub_eq_zero.mpr hy'
  have hsub :
      T (F - G) = 0 :=
    map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant
      T hT (F - G) hFG'
  exact sub_eq_zero.mp <| by simpa [map_sub] using hsub

/-- Any continuous linear functional that factors through `sliceIntegral` is
automatically invariant under translations of the head coordinate. This is the
cheap lift from the final reduced quotient back to the one-step `R`-surface
used in the current two-point `E -> R` seam. -/
theorem isHeadTranslationInvariant_of_factors_through_sliceIntegral
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hfac : ∀ F : SchwartzMap (Fin (n + 1) → ℝ) ℂ, T F = L (sliceIntegral F)) :
    IsHeadTranslationInvariantSchwartzCLM T := by
  intro a
  ext F
  rw [ContinuousLinearMap.comp_apply, hfac, hfac, SCV.translateSchwartzCLM_apply,
    sliceIntegral_translateSchwartz_head]

/-- Descend a head-translation-invariant functional to the tail Schwartz space
by choosing a normalized head cutoff. The factorization theorem below shows
that the resulting descended functional is independent of the choice of
representative with the same slice integral. -/
noncomputable def headTranslationDescentCLM
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
  T.comp (SchwartzMap.prependFieldCLMRight (E := ℝ) φ)

/-- If the head cutoff `φ` is normalized by `∫ φ = 1`, then a
head-translation-invariant functional factors through `sliceIntegral` via
`headTranslationDescentCLM T φ`. -/
theorem map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (φ : SchwartzMap ℝ ℂ)
    (hφ : ∫ x : ℝ, φ x = 1)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    T F = headTranslationDescentCLM T φ (sliceIntegral F) := by
  refine map_eq_of_sliceIntegral_eq_of_headTranslationInvariant T hT F
    (φ.prependField (sliceIntegral F)) ?_
  simpa [headTranslationDescentCLM] using
    (sliceIntegral_prependField_eq_self φ (sliceIntegral F) hφ).symm

/-- If a functional factors through `sliceIntegral`, then its descended
functional recovers exactly the final quotient functional. -/
theorem headTranslationDescentCLM_eq_of_factors_through_sliceIntegral
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap ℝ ℂ)
    (hφ : ∫ x : ℝ, φ x = 1)
    (hfac : ∀ F : SchwartzMap (Fin (n + 1) → ℝ) ℂ, T F = L (sliceIntegral F)) :
    headTranslationDescentCLM T φ = L := by
  ext f
  rw [headTranslationDescentCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.prependFieldCLMRight_apply, hfac]
  have hs : sliceIntegral (φ.prependField f) = f := by
    simpa using sliceIntegral_prependField_eq_self φ f hφ
  rw [hs]

/-- A compactly supported Schwartz test on `Fin (n + 1) → ℝ` can be translated
far enough in the distinguished head coordinate so that its topological support
lies in the positive head half-space. This is the support-geometry input behind
extending head-translation-invariant identities from positive-support tests to
arbitrary compactly supported ones. -/
theorem exists_headTranslate_positive_tsupport_of_hasCompactSupport
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : HasCompactSupport (F : (Fin (n + 1) → ℝ) → ℂ)) :
    ∃ a : ℝ, 0 < a ∧
      tsupport (((SCV.translateSchwartz (Fin.cons (-a) 0) F :
        SchwartzMap (Fin (n + 1) → ℝ) ℂ) : (Fin (n + 1) → ℝ) → ℂ))
        ⊆ {x : Fin (n + 1) → ℝ | 0 < x 0} := by
  obtain ⟨R, hR_pos, hR⟩ := hF.exists_pos_le_norm
  let v : Fin (n + 1) → ℝ := Fin.cons (-(R + 1)) (fun _ => 0)
  refine ⟨R + 1, by linarith, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq]
  -- x ∈ tsupport(translate(v, F)) ⟹ x ∈ closure(support) ⟹ x ∈ tsupport(F ∘ (· + v))
  -- ⟹ (x + v) ∈ tsupport F (since translate is a homeomorphism)
  -- ⟹ ‖x + v‖ < R (contrapositive of hR: ‖y‖ ≥ R → F y = 0 → y ∉ support F)
  -- ⟹ |x₀ + v₀| < R ⟹ |x₀ - (R+1)| < R ⟹ x₀ > 1
  -- Actually: x ∈ tsupport of translate means there's no open nhd of x where translate = 0
  -- Contrapositive: if x₀ ≤ 0, show x ∉ tsupport by showing translate = 0 near x
  by_contra h_neg; push_neg at h_neg
  -- For any y with y₀ ≤ 1: ‖y + v‖ ≥ |y₀ + v₀| = |y₀ - (R+1)| ≥ R, so F(y+v) = 0
  have h_vanish : ∀ y : Fin (n + 1) → ℝ, y 0 ≤ 1 →
      (F : (Fin (n + 1) → ℝ) → ℂ) (y + v) = 0 := by
    intro y hy
    apply hR
    calc R ≤ R + 1 - y 0 := by linarith
      _ = |y 0 + (-(R + 1))| := by rw [abs_of_nonpos (by linarith)]; ring
      _ = ‖(y + v) 0‖ := by simp [v, Pi.add_apply, Fin.cons, Real.norm_eq_abs]
      _ ≤ ‖y + v‖ := norm_le_pi_norm _ 0
  -- The set {y | y₀ < 1} is open and contains x (since x₀ ≤ 0 < 1)
  -- On this set, translate(v, F) = F(· + v) = 0
  -- So x is in the interior of {translate = 0}, hence x ∉ tsupport
  have h_not_tsupport : x ∉ tsupport
      ((SCV.translateSchwartz v F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
        (Fin (n + 1) → ℝ) → ℂ) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds x (show (0 : ℝ) < 1 by norm_num)) ?_
    intro y hy
    show (F : (Fin (n + 1) → ℝ) → ℂ) (y + v) = 0
    exact h_vanish y (by
      have h_dist : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
      have h0 : ‖(y - x) 0‖ ≤ ‖y - x‖ := norm_le_pi_norm _ 0
      rw [Real.norm_eq_abs, Pi.sub_apply] at h0
      linarith [abs_le.mp (le_of_lt (lt_of_le_of_lt h0 h_dist))])
  exact h_not_tsupport hx

/-- Head-translation-invariant Schwartz functionals are already determined on
all compactly supported tests once they agree on the compactly supported tests
whose topological support lies in the positive head half-space. -/
theorem map_eq_on_compactSupport_of_eq_on_positive_tsupport_of_headTranslationInvariant
    (T U : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (hU : IsHeadTranslationInvariantSchwartzCLM U)
    (hEq_pos : ∀ F : SchwartzMap (Fin (n + 1) → ℝ) ℂ,
      HasCompactSupport (F : (Fin (n + 1) → ℝ) → ℂ) →
      tsupport (F : (Fin (n + 1) → ℝ) → ℂ) ⊆ {x : Fin (n + 1) → ℝ | 0 < x 0} →
      T F = U F)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : HasCompactSupport (F : (Fin (n + 1) → ℝ) → ℂ)) :
    T F = U F := by
  -- Translate F so its support is in the positive head half-space
  obtain ⟨a, ha_pos, ha_supp⟩ :=
    exists_headTranslate_positive_tsupport_of_hasCompactSupport F hF
  let F' := SCV.translateSchwartz (Fin.cons (-a) 0) F
  -- F' has compact support and positive head-time support
  have hF'_compact : HasCompactSupport (F' : (Fin (n + 1) → ℝ) → ℂ) := by
    simpa [F', SCV.translateSchwartz] using
      hF.comp_homeomorph (Homeomorph.addRight (Fin.cons (-a) 0))
  -- T(F) = T(F') by head-TI (translate by +a undoes the -a shift)
  -- Key: T(F) = T(translate(-a) F) by head-TI, and translate(-a) F = F'
  have hshift : SCV.translateSchwartzCLM (Fin.cons a (0 : Fin n → ℝ)) F' = F := by
    ext x
    show F (x + Fin.cons a 0 + Fin.cons (-a) 0) = F x
    congr 1; funext j
    simp only [Pi.add_apply]
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cons]
  have hT_eq : T F = T F' := by
    rw [← hshift]
    exact congr_fun (congr_arg DFunLike.coe (hT a)) F'
  have hU_eq : U F = U F' := by
    rw [← hshift]
    exact congr_fun (congr_arg DFunLike.coe (hU a)) F'
  rw [hT_eq, hU_eq]
  exact hEq_pos F' hF'_compact ha_supp

/-- If two head-translation-invariant functionals agree on compactly supported
tests whose support lies in the positive head half-space, then after choosing a
compactly supported normalized head cutoff they also agree on the descended
compactly supported tail tests. This is the abstract support-shift bridge used
to pass from positive reduced-shell identities to compact reduced-shell
identities in the current two-point `E -> R` packaging route. -/
theorem headTranslationDescentCLM_eq_on_compactSupport_of_eq_on_positive_tsupport
    (T U : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (hU : IsHeadTranslationInvariantSchwartzCLM U)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hψ_compact : HasCompactSupport ψ)
    (hEq_pos : ∀ F : SchwartzMap (Fin (n + 1) → ℝ) ℂ,
      HasCompactSupport (F : (Fin (n + 1) → ℝ) → ℂ) →
      tsupport (F : (Fin (n + 1) → ℝ) → ℂ) ⊆ {x : Fin (n + 1) → ℝ | 0 < x 0} →
      T F = U F)
    (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin n → ℝ) → ℂ)) :
    headTranslationDescentCLM T ψ f = headTranslationDescentCLM U ψ f := by
  have hprepend : HasCompactSupport (ψ.prependField f) :=
    hasCompactSupport_prependField ψ f hψ_compact hf
  have hfull :
      T (ψ.prependField f) = U (ψ.prependField f) :=
    map_eq_on_compactSupport_of_eq_on_positive_tsupport_of_headTranslationInvariant
      T U hT hU hEq_pos (ψ.prependField f) (by simpa using hprepend)
  simpa [headTranslationDescentCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.prependFieldCLMRight_apply] using hfull


end OSReconstruction
