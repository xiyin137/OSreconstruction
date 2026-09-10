/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.TubeDomainExtension









noncomputable section

open BigOperators Topology MeasureTheory

namespace SCV

/-- Local one-variable edge-of-the-wedge on the disk over an interval.  This
variant only assumes holomorphy on the upper/lower halves of the output disk,
which is the form needed by the local Rudin map. -/
theorem local_edge_of_the_wedge_1d (a b : ℝ) (hab : a < b)
    (f_plus f_minus : ℂ → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus
      (Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ∩ EOW.UpperHalfPlane))
    (hf_minus : DifferentiableOn ℂ f_minus
      (Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ∩ EOW.LowerHalfPlane))
    (hcont_plus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto f_plus (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (f_plus x)))
    (hcont_minus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto f_minus (nhdsWithin (x : ℂ) EOW.LowerHalfPlane) (nhds (f_minus x)))
    (hmatch : ∀ x : ℝ, a < x → x < b → f_plus x = f_minus x)
    (hbv_cont : ∀ x₀ : ℝ, a < x₀ → x₀ < b →
      Filter.Tendsto f_plus (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (f_plus x₀))) :
    ∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧
      Convex ℝ U ∧
      (∀ z ∈ U, starRingEnd ℂ z ∈ U) ∧
      (∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ EOW.UpperHalfPlane, F z = f_plus z) ∧
      (∀ z ∈ U ∩ EOW.LowerHalfPlane, F z = f_minus z) ∧
      Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ⊆ U := by
  let mid : ℂ := ((a + b) / 2 : ℝ)
  let rad : ℝ := (b - a) / 2
  have hrad : rad > 0 := by
    show (b - a) / 2 > 0
    linarith
  let F : ℂ → ℂ := fun z =>
    if z.im > 0 then f_plus z
    else if z.im < 0 then f_minus z
    else f_plus z
  have ball_real_in_interval : ∀ z : ℂ, z ∈ Metric.ball mid rad → z.im = 0 →
      a < z.re ∧ z.re < b := by
    intro z hz hzim
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hsub : z - mid = ((z.re - (a + b) / 2 : ℝ) : ℂ) +
        ((z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [mid]
    rw [hsub, hzim, Complex.ofReal_zero, zero_mul, add_zero] at hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt] at hz
    dsimp [rad] at hz
    exact ⟨by linarith, by linarith⟩
  have real_eq : ∀ z : ℂ, z.im = 0 → (z.re : ℂ) = z := by
    intro z hz
    exact Complex.ext (by simp) (by simp [hz])
  have hFcont : ContinuousOn F (Metric.ball mid rad) := by
    intro z hz
    by_cases hzim : z.im = 0
    · obtain ⟨hza, hzb⟩ := ball_real_in_interval z hz hzim
      have hFz : F z = f_plus z := by
        simp only [F]
        split_ifs with h1 h2 <;> [linarith; linarith; rfl]
      have hzeq : (z.re : ℂ) = z := real_eq z hzim
      have hcp : Filter.Tendsto f_plus (𝓝[EOW.UpperHalfPlane] z) (nhds (f_plus z)) := by
        have := hcont_plus z.re hza hzb
        rwa [hzeq] at this
      have hcm : Filter.Tendsto f_minus (𝓝[EOW.LowerHalfPlane] z) (nhds (f_minus z)) := by
        have := hcont_minus z.re hza hzb
        rwa [hzeq] at this
      have hbvc : Filter.Tendsto f_plus (𝓝[{c | c.im = 0}] z) (nhds (f_plus z)) := by
        have := hbv_cont z.re hza hzb
        rwa [hzeq] at this
      have hmz : f_plus z = f_minus z := by
        rw [← hzeq]
        exact hmatch z.re hza hzb
      rw [ContinuousWithinAt]
      rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds hz)]
      have huniv : (Set.univ : Set ℂ) = {c | c.im > 0} ∪ {c | c.im ≤ 0} := by
        ext c
        simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
        exact lt_or_ge 0 c.im
      rw [nhds_eq_nhdsWithin_sup_nhdsWithin z huniv, hFz]
      apply Filter.Tendsto.sup
      · exact hcp.congr' (by
          filter_upwards [self_mem_nhdsWithin] with w (hw : w.im > 0)
          show f_plus w = F w
          simp only [F, hw, ite_true])
      · rw [show ({c : ℂ | c.im ≤ 0} : Set ℂ) =
            {c | c.im < 0} ∪ {c | c.im = 0} from by
          ext c
          simp only [Set.mem_setOf_eq, Set.mem_union]
          exact le_iff_lt_or_eq]
        rw [nhdsWithin_union]
        apply Filter.Tendsto.sup
        · rw [hmz]
          exact hcm.congr' (by
            filter_upwards [self_mem_nhdsWithin] with w (hw : w.im < 0)
            show f_minus w = F w
            simp only [F]
            split_ifs with h1 <;> [linarith; rfl])
        · exact hbvc.congr' (by
            filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
            show f_plus w = F w
            simp only [F]
            split_ifs with h1 h2 <;> [linarith; linarith; rfl])
    · rcases lt_or_gt_of_ne hzim with hlt | hgt
      · have hfd : DifferentiableAt ℂ f_minus z :=
          hf_minus.differentiableAt
            ((Metric.isOpen_ball.inter EOW.lowerHalfPlane_isOpen).mem_nhds ⟨hz, hlt⟩)
        exact (hfd.continuousAt.congr
          (by
            filter_upwards [EOW.lowerHalfPlane_isOpen.mem_nhds hlt] with w hw
            have hw' : w.im < 0 := by simpa [EOW.LowerHalfPlane] using hw
            show f_minus w = F w
            simp only [F]
            split_ifs with h1 <;> [linarith; rfl])).continuousWithinAt
      · have hfd : DifferentiableAt ℂ f_plus z :=
          hf_plus.differentiableAt
            ((Metric.isOpen_ball.inter EOW.upperHalfPlane_isOpen).mem_nhds ⟨hz, hgt⟩)
        exact (hfd.continuousAt.congr
          (by
            filter_upwards [EOW.upperHalfPlane_isOpen.mem_nhds hgt] with w hw
            have hw' : w.im > 0 := by simpa [EOW.UpperHalfPlane] using hw
            show f_plus w = F w
            simp only [F, hw', ite_true])).continuousWithinAt
  have hF_holo_off : DifferentiableOn ℂ F
      (Metric.ball mid rad \ {z : ℂ | z.im = 0}) := by
    intro z hz
    rcases hz with ⟨hzball, hzne⟩
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · have hfd : DifferentiableAt ℂ f_minus z :=
        hf_minus.differentiableAt
          ((Metric.isOpen_ball.inter EOW.lowerHalfPlane_isOpen).mem_nhds ⟨hzball, hlt⟩)
      exact (((show f_minus =ᶠ[𝓝 z] F from by
        filter_upwards [EOW.lowerHalfPlane_isOpen.mem_nhds hlt] with w hw
        have hw' : w.im < 0 := by simpa [EOW.LowerHalfPlane] using hw
        show f_minus w = F w
        simp only [F]
        split_ifs with h1 <;> [linarith; rfl]).differentiableAt_iff).mp
          hfd).differentiableWithinAt
    · have hfd : DifferentiableAt ℂ f_plus z :=
        hf_plus.differentiableAt
          ((Metric.isOpen_ball.inter EOW.upperHalfPlane_isOpen).mem_nhds ⟨hzball, hgt⟩)
      exact (((show f_plus =ᶠ[𝓝 z] F from by
        filter_upwards [EOW.upperHalfPlane_isOpen.mem_nhds hgt] with w hw
        have hw' : w.im > 0 := by simpa [EOW.UpperHalfPlane] using hw
        show f_plus w = F w
        simp only [F, hw', ite_true]).differentiableAt_iff).mp hfd).differentiableWithinAt
  have hFdiff : DifferentiableOn ℂ F (Metric.ball mid rad) :=
    differentiableOn_of_continuous_off_real_1d Metric.isOpen_ball F hFcont hF_holo_off
  refine ⟨Metric.ball mid rad, F, Metric.isOpen_ball, convex_ball mid rad, ?_,
    ?_, hFdiff, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball] at hz ⊢
    calc dist (starRingEnd ℂ z) mid
        = dist (starRingEnd ℂ z) (starRingEnd ℂ mid) := by
            rw [show starRingEnd ℂ mid = mid from Complex.conj_ofReal _]
      _ = dist z mid := Complex.dist_conj_conj z mid
      _ < rad := hz
  · intro x hax hxb
    show dist (x : ℂ) mid < rad
    rw [Complex.dist_eq]
    have hsub : (↑x - mid) = ((x - (a + b) / 2 : ℝ) : ℂ) := by
      simp [mid]
    rw [hsub, Complex.norm_real]
    show |x - (a + b) / 2| < (b - a) / 2
    rw [abs_lt]
    constructor <;> linarith
  · intro z ⟨_, (hz : z.im > 0)⟩
    exact if_pos hz
  · intro z ⟨_, (hz : z.im < 0)⟩
    show F z = f_minus z
    have h1 : ¬(z.im > 0) := by linarith
    simp only [F, h1, ite_false, hz, ite_true]
  · intro z hz
    exact hz

end SCV
