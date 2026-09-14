import OSReconstruction.SCV.SeparatelyAnalytic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphic smearing under local integrable domination

Cauchy's estimate gives an integrable derivative bound on a smaller disk.
Differentiation under the integral and Osgood's lemma then give joint
holomorphy. No derivative bound is assumed as an additional input.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction.OSIIChapterVI

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {k : Nat} {U : Set (Fin k -> Complex)}

set_option maxHeartbeats 600000 in
/-- Spatial integration preserves joint holomorphy under a single
integrable majorant on each compact complex parameter set. -/
theorem differentiableOn_integral_of_compact_domination
    (mu : Measure X) (hU : IsOpen U) (F : (Fin k -> Complex) -> X -> Complex)
    (hcont : ContinuousOn (fun p : (Fin k -> Complex) × X => F p.1 p.2) (U ×ˢ univ))
    (hholo : ∀ x, DifferentiableOn Complex (fun z => F z x) U)
    (hdom : ∀ K : Set (Fin k -> Complex), IsCompact K -> K ⊆ U ->
      ∃ g : X -> Real, Integrable g mu ∧ ∀ z ∈ K, ∀ x, ‖F z x‖ ≤ g x) :
    DifferentiableOn Complex (fun z => ∫ x, F z x ∂mu) U := by
  have hfixed (z : Fin k -> Complex) (hz : z ∈ U) : Continuous (F z) := by
    rw [← continuousOn_univ]
    exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨hz, mem_univ x⟩)
  have hlocal (z : Fin k -> Complex) (hz : z ∈ U) :
      ∃ r : Real, 0 < r ∧ Metric.closedBall z (2 * r) ⊆ U ∧
        ∃ g : X -> Real, Integrable g mu ∧
          ∀ w ∈ Metric.closedBall z (2 * r), ∀ x, ‖F w x‖ ≤ g x := by
    obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hU z hz
    have hr : 0 < R / 4 := by positivity
    have hsub : Metric.closedBall z (2 * (R / 4)) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hRsub
    obtain ⟨g, hg, hb⟩ := hdom _ (isCompact_closedBall z (2 * (R / 4))) hsub
    exact ⟨R / 4, hr, hsub, g, hg, hb⟩
  apply osgood_lemma hU
  · intro z hz
    obtain ⟨r, hr, hsub, g, hg, hb⟩ := hlocal z hz
    have hsmall : Metric.ball z r ⊆ Metric.closedBall z (2 * r) :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated (bound := g)
    · filter_upwards [Metric.ball_mem_nhds z hr] with w hw
      exact (hfixed w (hsub (hsmall hw))).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds z hr] with w hw
      exact Filter.Eventually.of_forall (hb w (hsmall hw))
    · exact hg
    · exact Filter.Eventually.of_forall (fun x =>
        ((hholo x z hz).differentiableAt (hU.mem_nhds hz)).continuousAt)
  · intro z hz j
    obtain ⟨r, hr, hsub, g, hg, hb⟩ := hlocal z hz
    have hdist (w : Complex) : dist (Function.update z j w) z ≤ dist w (z j) := by
      apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist w (z j))).mpr
      intro l
      by_cases hlj : l = j
      · subst l
        simp
      · simp [Function.update_of_ne hlj]
    have hupdate (w : Complex) (hw : dist w (z j) ≤ 2 * r) :
        Function.update z j w ∈ Metric.closedBall z (2 * r) :=
      Metric.mem_closedBall.mpr ((hdist w).trans hw)
    let G : Complex -> X -> Complex := fun w x => F (Function.update z j w) x
    let G' : Complex -> X -> Complex := fun w x => deriv (fun u => G u x) w
    have hupdate_diff (w : Complex) : DifferentiableAt Complex (Function.update z j) w := by
      apply differentiableAt_pi.mpr
      intro l
      by_cases hlj : l = j
      · subst l
        simp
      · simp only [Function.update_of_ne hlj]
        fun_prop
    have hupdate_cont : Continuous
        (fun p : Complex × X => (Function.update z j p.1, p.2)) := by
      apply Continuous.prodMk
      · apply continuous_pi
        intro l
        by_cases hlj : l = j
        · subst l
          simpa using (continuous_fst : Continuous (fun p : Complex × X => p.1))
        · simpa only [Function.update_of_ne hlj] using
            (continuous_const : Continuous (fun _ : Complex × X => z l))
      · exact continuous_snd
    have hd (x : X) (w : Complex) (hw : w ∈ Metric.ball (z j) (2 * r)) :
        HasDerivAt (fun u => G u x) (G' w x) w := by
      have hmem := hsub (hupdate w (Metric.mem_ball.mp hw).le)
      exact (((hholo x _ hmem).differentiableAt (hU.mem_nhds hmem)).comp w
        (hupdate_diff w)).hasDerivAt
    have hjoint : ContinuousOn (fun p : Complex × X => G p.1 p.2)
        (Metric.closedBall (z j) r ×ˢ univ) := by
      exact hcont.comp hupdate_cont.continuousOn
        (fun p hp => ⟨hsub (hupdate p.1
          ((Metric.mem_closedBall.mp hp.1).trans (by linarith))), mem_univ p.2⟩)
    have hderiv_cont : Continuous (G' (z j)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact continuousAt_deriv_of_continuousOn hr isOpen_univ
        (fun p : Complex × X => G p.1 p.2) hjoint
        (fun y _ w hw => (hd y w
          (Metric.closedBall_subset_ball (by linarith) hw)).differentiableAt.differentiableWithinAt)
        (mem_univ x)
    have hderiv_bound (x : X) (w : Complex) (hw : w ∈ Metric.ball (z j) r) :
        ‖G' w x‖ ≤ g x / r := by
      apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      · constructor
        · intro u hu
          apply (hd x u ?_).differentiableAt.differentiableWithinAt
          rw [Metric.mem_ball] at hu hw ⊢
          linarith [dist_triangle u w (z j)]
        · rw [closure_ball w hr.ne']
          intro u hu
          apply (hd x u ?_).continuousAt.continuousWithinAt
          rw [Metric.mem_closedBall] at hu
          rw [Metric.mem_ball] at hw ⊢
          linarith [dist_triangle u w (z j)]
      · intro u hu
        apply hb _ (hupdate u ?_) x
        have hu' := Metric.sphere_subset_closedBall hu
        rw [Metric.mem_closedBall] at hu'
        rw [Metric.mem_ball] at hw
        linarith [dist_triangle u w (z j)]
    have hmeas : ∀ᶠ w in nhds (z j), AEStronglyMeasurable (G w) mu := by
      filter_upwards [Metric.ball_mem_nhds (z j) hr] with w hw
      exact (hfixed _ (hsub (hupdate w (by
        have h := Metric.mem_ball.mp hw
        linarith)))).aestronglyMeasurable
    have hGint : Integrable (G (z j)) mu := by
      have h := hg.mono' ((hfixed z hz).aestronglyMeasurable)
        (Filter.Eventually.of_forall (hb z (Metric.mem_closedBall_self (by positivity))))
      simpa [G] using h
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := mu) (F := G) (F' := G') (bound := fun x => g x / r)
      (Metric.ball_mem_nhds (z j) hr) hmeas hGint hderiv_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x w hw => hderiv_bound x w hw))
      (hg.div_const r)
      (Filter.Eventually.of_forall (fun x w hw =>
        hd x w (Metric.ball_subset_ball (by linarith) hw)))
    exact hmain.2.differentiableAt

end OSReconstruction.OSIIChapterVI
