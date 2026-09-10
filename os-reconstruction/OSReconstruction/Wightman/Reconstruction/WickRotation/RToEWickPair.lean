import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation

/-!
# Wick Pairing for the Actual Schwinger Constructor

The translated-PET kernel gives both the original Wightman boundary values
and the honest zero-diagonal Euclidean pairing. This pins the constructor;
it does not merely assert that some Schwinger family has a Wick pairing.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace OSReconstruction
variable {d : ℕ} [NeZero d]

/-- The actual zero-diagonal constructor has the original Wightman boundary pairing. -/
theorem constructSchwingerFunctions_isWickRotationPair (Wfn : WightmanFunctions d) :
    IsWickRotationPair (constructSchwingerFunctions Wfn) Wfn.W := by
  intro n
  -- Witness the analytic continuation via the TranslatedPET-extended kernel,
  -- which agrees with F_ext on ForwardTube (⊆ PET) by
  -- `F_ext_on_translatedPET_total_eq_on_PET`.
  refine ⟨F_ext_on_translatedPET_total Wfn, ?_, ?_, fun _ => rfl⟩
  · -- Differentiable on ForwardTube: transport differentiability of F_ext via
    --   F_ext_on_translatedPET_total = F_ext on PET (hence on ForwardTube ⊆ PET).
    have hFT_PET : ForwardTube d n ⊆ PermutedExtendedTube d n :=
      ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)
    have hF_diff : DifferentiableOn ℂ (W_analytic_BHW Wfn n).val (ForwardTube d n) :=
      (W_analytic_BHW Wfn n).property.1.mono hFT_PET
    refine hF_diff.congr ?_
    intro z hz
    exact F_ext_on_translatedPET_total_eq_on_PET Wfn z (hFT_PET hz)
  · -- Boundary values: the limits agree with those of F_ext on ForwardTube,
    -- where the two kernels coincide pointwise.
    intro f η hη
    have hlim := bhw_distributional_boundary_values Wfn f η hη
    refine Filter.Tendsto.congr' ?_ hlim
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε => ?_⟩
    -- At each ε > 0 the integrands agree pointwise: x + iεη ∈ ForwardTube ⊆ PET.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hpoint : (fun k μ => (↑(x k μ) + ε * ↑(η k μ) * Complex.I : ℂ)) ∈
        ForwardTube d n := by
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
      exact inOpenForwardCone_smul d ε (by simpa using hε) _ (hη k)
    have hFT_PET : ForwardTube d n ⊆ PermutedExtendedTube d n :=
      ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)
    have hpet := hFT_PET hpoint
    rw [F_ext_on_translatedPET_total_eq_on_PET Wfn _ hpet]

end OSReconstruction
