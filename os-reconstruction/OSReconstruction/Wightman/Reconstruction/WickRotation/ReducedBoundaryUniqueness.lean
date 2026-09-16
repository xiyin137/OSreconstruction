import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedInput
import OSReconstruction.SCV.TubeBoundaryUniqueness

noncomputable section

open Complex Topology Filter MeasureTheory Set

namespace BHW

variable {d m : ℕ} [NeZero d]

/-- The existing reduced boundary contract determines the forward-tube input.
No additional growth or global slice-integrability hypothesis is needed. -/
theorem eqOn_reducedForwardTube_of_boundary_values
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    {F G : ReducedNPointConfig d m → ℂ}
    (hF : DifferentiableOn ℂ F (ReducedForwardTubeN d m))
    (hG : DifferentiableOn ℂ G (ReducedForwardTubeN d m))
    (hFb : HasReducedBoundaryValues W m F)
    (hGb : HasReducedBoundaryValues W m G) :
    EqOn F G (ReducedForwardTubeN d m) := by
  let e := flattenCLEquiv m (d + 1)
  let eR := flattenCLEquivReal m (d + 1)
  let C := FlatProductForwardConeReal d m
  have hmem : ∀ z, e.symm z ∈ ReducedForwardTubeN d m ↔ z ∈ SCV.TubeDomain C := by
    intro z
    change e.symm z ∈ ProductForwardCone d m ↔ _
    rw [mem_productForwardCone_iff_flat_im]
    have hflat : flattenCfg m d (e.symm z) = z := by
      exact flatten_unflatten_cfg m d z
    rw [hflat]
    rfl
  let Wflat : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ → ℂ :=
    fun ψ => W m (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR ψ)
  have hboundary : ∀ H : ReducedNPointConfig d m → ℂ,
      HasReducedBoundaryValues W m H →
      ∀ ψ : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ,
        HasCompactSupport (ψ : (Fin (m * (d + 1)) → ℝ) → ℂ) → ∀ η ∈ C,
          Tendsto (fun ε : ℝ => ∫ x : Fin (m * (d + 1)) → ℝ,
            (H ∘ e.symm) (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) * ψ x)
            (nhdsWithin 0 (Ioi 0)) (nhds (Wflat ψ)) := by
    intro H hH ψ _ η hη
    let f : SchwartzNPoint d m := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR ψ
    let η' : Fin m → Fin (d + 1) → ℝ := eR.symm η
    have hη' : η' ∈ ProductForwardConeReal d m := by
      change unflattenCfgReal m d η ∈ ProductForwardConeReal d m at hη
      exact hη
    refine (hH f η' hη').congr' (Eventually.of_forall fun ε => ?_)
    dsimp only
    rw [integral_flatten_change_of_variables m (d + 1)]
    apply integral_congr_ae
    filter_upwards with x
    have harg : e.symm (fun i => ((eR x) i : ℂ) + ε * (η i : ℂ) * I) =
        (fun k μ => (x k μ : ℂ) + ε * (η' k μ : ℂ) * I) := by
      ext k μ
      simp only [e, eR, η', flattenCLEquiv_symm_apply,
        flattenCLEquivReal_apply, flattenCLEquivReal_symm_apply,
        Equiv.symm_apply_apply]
    change H (fun k μ => (x k μ : ℂ) + ε * (η' k μ : ℂ) * I) * ψ (eR x) =
      H (e.symm (fun i => ((eR x) i : ℂ) + ε * (η i : ℂ) * I)) * ψ (eR x)
    simp only [harg]
    rfl
  have heq := SCV.eqOn_tube_of_compact_boundary_values
    (isOpen_flatProductForwardConeReal m d)
    (flatProductForwardConeReal_smul_pos m d)
    (hF.comp e.symm.differentiableOn (fun z hz => (hmem z).mpr hz))
    (hG.comp e.symm.differentiableOn (fun z hz => (hmem z).mpr hz))
    Wflat (hboundary F hFb) (hboundary G hGb)
  intro z hz
  have hz' : e z ∈ SCV.TubeDomain C := (hmem _).mp (by simpa using hz)
  simpa using heq hz'

theorem ReducedForwardTubeInput.eqOn
    {W : (n : ℕ) → SchwartzNPoint d n → ℂ}
    (F G : ReducedForwardTubeInput W m) :
    EqOn F.toFun G.toFun (ReducedForwardTubeN d m) :=
  eqOn_reducedForwardTube_of_boundary_values W F.holomorphic G.holomorphic
    F.boundary_values G.boundary_values

theorem Route1ReducedAnalyticInput.eqOn_canonical
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m) :
    EqOn F.toFun (route1ReducedPreInputFromSpectrumCondition Wfn m).toFun
      (ReducedForwardTubeN d m) :=
  F.eqOn (route1ReducedAnalyticInputExists Wfn χ m)

/-- Pulling any valid reduced input back to the absolute forward tube gives
the actual spectrum-condition witness, not a separately assumed branch. -/
theorem Route1ReducedAnalyticInput.pullback_eq_spectrum
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d (m + 1)) :
    pullbackReducedExtension F.toFun z = (Wfn.spectrum_condition (m + 1)).choose z := by
  have hred := (mem_forwardTube_iff_basepoint_and_reducedDiff z).mp hz
  exact (F.eqOn_canonical Wfn χ hred.2).trans
    (route1ReducedPreInputFromSpectrumCondition_factorization Wfn m z hz)

theorem Route1ReducedAnalyticInput.pullback_boundary_values
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m) :
    HasAbsoluteBoundaryValues m (Wfn.W (m + 1)) (pullbackReducedExtension F.toFun) := by
  intro f η hη
  refine ((spectrumConditionAbsoluteInput Wfn m).boundary_values f η hη).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  filter_upwards with x
  have hz : (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * I) ∈ ForwardTube d (m + 1) := by
    rw [BHW_forwardTube_eq, forwardTube_eq_imPreimage]
    have hsmul : (ε • η) = (fun k μ => ε * η k μ) := by
      ext k μ
      rfl
    simpa [Pi.smul_apply, hsmul] using forwardConeAbs_smul d (m + 1) ε hε η hη
  exact congrArg (fun a : ℂ => a * f x) (F.pullback_eq_spectrum Wfn χ _ hz).symm

/-- An inverse to forward-tube descent, preserving the literal absolute
boundary distribution. PET quotient descent is a separate obligation. -/
def Route1ReducedAnalyticInput.toAbsoluteInput
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m) :
    AbsoluteForwardTubeInput m (Wfn.W (m + 1)) where
  toFun := pullbackReducedExtension F.toFun
  holomorphic := F.holomorphic.comp (reducedDiffMap (m + 1) d).differentiableOn
    (fun z hz => ((mem_forwardTube_iff_basepoint_and_reducedDiff z).mp hz).2)
  real_lorentz_invariant := by
    intro Λ z hz
    have hz' : (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) ∈ ForwardTube d (m + 1) := by
      rw [BHW_forwardTube_eq] at hz ⊢
      exact restricted_preserves_forward_tube Λ z hz
    rw [F.pullback_eq_spectrum Wfn χ _ hz', F.pullback_eq_spectrum Wfn χ _ hz]
    exact (spectrumConditionAbsoluteInput Wfn m).real_lorentz_invariant Λ z hz
  translation_invariant := by
    intro z c _ _
    exact pullbackReducedExtension_translate_uniform F.toFun z c
  boundary_values := F.pullback_boundary_values Wfn χ

end BHW
