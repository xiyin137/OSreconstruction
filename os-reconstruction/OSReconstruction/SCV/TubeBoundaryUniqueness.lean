import OSReconstruction.SCV.LocalBoundaryUniqueness

noncomputable section

open Complex Topology Filter MeasureTheory Set

namespace SCV

/-- Equal compact-test weak boundary limits determine a holomorphic tube
function. Compact slice integrability follows from holomorphy. -/
theorem eqOn_tube_of_compact_boundary_values {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C)
    (hcone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F G : (Fin m → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hG : DifferentiableOn ℂ G (TubeDomain C))
    (W : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (hFb : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) → ∀ η ∈ C,
        Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
          F (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds (W φ)))
    (hGb : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) → ∀ η ∈ C,
        Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
          G (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds (W φ))) :
    EqOn F G (TubeDomain C) := by
  have hb : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) → ∀ η ∈ C,
        Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
          (F (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) -
            G (fun i => (x i : ℂ) + ε * (η i : ℂ) * I)) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    intro φ hφ η hη
    have hlim := (hFb φ hφ η hη).sub (hGb φ hφ η hη)
    simp only [sub_self] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let shift : Fin m → ℂ := fun i => (ε : ℂ) * (η i : ℂ) * I
    have hm : ∀ x ∈ tsupport (φ : (Fin m → ℝ) → ℂ),
        shift + realEmbed x ∈ TubeDomain C := by
      intro x _
      change (fun i => (shift i + (x i : ℂ)).im) ∈ C
      exact Set.mem_of_eq_of_mem (by ext i; simp [shift]) (hcone ε hε η hη)
    have hIF := integrable_realMollifyLocal_integrand_of_translate_margin
      F φ (TubeDomain C) shift (tubeDomain_isOpen hC) hF hφ hm
    have hIG := integrable_realMollifyLocal_integrand_of_translate_margin
      G φ (TubeDomain C) shift (tubeDomain_isOpen hC) hG hφ hm
    have harg : ∀ x, shift + realEmbed x =
        (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) := by
      intro x
      ext i
      simp [shift, realEmbed, add_comm]
    simp only [harg] at hIF hIG
    rw [← integral_sub hIF hIG]
    apply integral_congr_ae
    filter_upwards with x
    ring
  intro z hz
  let R : ℝ := 8 * (‖z‖ + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have heq := local_distributional_uniqueness_tube hC hcone 0 hR
    ((hF.sub hG).mono inter_subset_right) (fun φ hφ _ η hη => hb φ hφ η hη)
  apply sub_eq_zero.mp (heq z ⟨?_, hz⟩)
  have h0 : realEmbed (0 : Fin m → ℝ) = 0 := by ext i; simp [realEmbed]
  rw [Metric.mem_ball, h0, dist_zero_right]
  dsimp [R]
  linarith

end SCV
