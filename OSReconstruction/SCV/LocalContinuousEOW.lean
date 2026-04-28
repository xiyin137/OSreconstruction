import OSReconstruction.SCV.TubeDomainExtension

/-!
# Local Continuous Edge-of-the-Wedge Geometry

This file contains the finite-dimensional local-wedge geometry needed to
extract a local continuous edge-of-the-wedge theorem from the checked global
tube-domain proof in `TubeDomainExtension.lean`.
-/

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

/-- The closed coefficient simplex in `Fin m -> ℝ`. -/
def localEOWCoefficientSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {a | (∀ j, a j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j, a j = 1}

/-- The compact set of cone directions obtained from convex combinations of a
chosen cone basis. -/
def localEOWSimplexDirections {m : ℕ}
    (ys : Fin m → Fin m → ℝ) : Set (Fin m → ℝ) :=
  (fun a : Fin m → ℝ => ∑ j, a j • ys j) ''
    localEOWCoefficientSimplex m

def localEOWRealChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    (Fin m → ℝ) → Fin m → ℝ :=
  fun u a => x0 a + ∑ j, u j * ys j a

def localEOWChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    (Fin m → ℂ) → Fin m → ℂ :=
  fun w a => (x0 a : ℂ) + ∑ j, w j * (ys j a : ℂ)

theorem localEOWChart_zero {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    localEOWChart x0 ys 0 = realEmbed x0 := by
  ext i
  simp [localEOWChart, realEmbed]

theorem differentiable_localEOWChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    Differentiable ℂ (localEOWChart x0 ys) := by
  change Differentiable ℂ
    (fun w : Fin m → ℂ => fun a => (x0 a : ℂ) + ∑ j, w j * (ys j a : ℂ))
  exact differentiable_pi.mpr fun _ =>
    (differentiable_const _).add <|
      Differentiable.fun_sum fun j _ =>
        (differentiable_apply j).mul (differentiable_const _)

theorem continuous_localEOWChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    Continuous (localEOWChart x0 ys) :=
  (differentiable_localEOWChart x0 ys).continuous

theorem localEOWChart_im {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w : Fin m → ℂ) (i : Fin m) :
    (localEOWChart x0 ys w i).im = ∑ j, (w j).im * ys j i := by
  simp [localEOWChart, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, mul_zero]

theorem localEOWChart_real {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (t : Fin m → ℝ) :
    localEOWChart x0 ys (fun j => (t j : ℂ)) =
      realEmbed (localEOWRealChart x0 ys t) := by
  ext i
  simp [localEOWChart, localEOWRealChart, realEmbed, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul]

theorem localEOWChart_conj {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w : Fin m → ℂ) :
    localEOWChart x0 ys (fun j => starRingEnd ℂ (w j)) =
      fun i => starRingEnd ℂ (localEOWChart x0 ys w i) := by
  ext i
  simp only [localEOWChart, map_add, map_sum, map_mul, Complex.conj_ofReal]

theorem localEOWChart_affine_real_combo {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w1 w2 : Fin m → ℂ) (a b : ℝ) (hab : a + b = 1) :
    localEOWChart x0 ys (a • w1 + b • w2) =
      a • localEOWChart x0 ys w1 + b • localEOWChart x0 ys w2 := by
  ext i
  simp only [localEOWChart, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
    add_mul, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add, mul_add]
  have habc : (a : ℂ) + (b : ℂ) = 1 := by
    exact_mod_cast hab
  linear_combination -↑(x0 i) * habc

theorem localEOWChart_inverse_conj {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Φinv : (Fin m → ℂ) → (Fin m → ℂ))
    (hleft : ∀ w, Φinv (localEOWChart x0 ys w) = w)
    (hright : ∀ z, localEOWChart x0 ys (Φinv z) = z)
    (z : Fin m → ℂ) :
    Φinv (fun i => starRingEnd ℂ (z i)) =
      fun j => starRingEnd ℂ (Φinv z j) := by
  have h1 := localEOWChart_conj x0 ys (Φinv z)
  have h2 : (fun i => starRingEnd ℂ (localEOWChart x0 ys (Φinv z) i)) =
      fun i => starRingEnd ℂ (z i) := by
    ext i
    congr 1
    exact congr_fun (hright z) i
  rw [h2] at h1
  rw [← h1]
  exact hleft _

theorem localEOWChart_equiv {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) :
    ∃ (Φinv : (Fin m → ℂ) → (Fin m → ℂ)),
      Differentiable ℂ Φinv ∧
      (∀ w, Φinv (localEOWChart x0 ys w) = w) ∧
      (∀ z, localEOWChart x0 ys (Φinv z) = z) := by
  let M : Matrix (Fin m) (Fin m) ℂ := fun i j => ((ys j) i : ℂ)
  have hPhi_eq : ∀ w, localEOWChart x0 ys w = realEmbed x0 + M.mulVec w := by
    intro w
    ext i
    simp only [localEOWChart, realEmbed, Pi.add_apply, Matrix.mulVec, dotProduct]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdet : IsUnit M.det := by
    let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of ys
    have hA_unit : IsUnit A :=
      Matrix.linearIndependent_rows_iff_isUnit.mp (by
        show LinearIndependent ℝ A.row
        simp only [Matrix.row_def, A]
        exact hli)
    have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA_unit
    change IsUnit M.det
    have hM_eq : M = (Matrix.of ys).transpose.map Complex.ofRealHom := by
      ext i j
      simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, M]
    rw [hM_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    exact hdetA.map _
  refine ⟨fun z => M⁻¹.mulVec (z - realEmbed x0), ?_, ?_, ?_⟩
  · have hmv : Differentiable ℂ (fun v : Fin m → ℂ => M⁻¹.mulVec v) := by
      apply differentiable_pi.mpr
      intro i
      simp only [Matrix.mulVec, dotProduct]
      exact Differentiable.fun_sum fun j _ =>
        (differentiable_const _).mul (differentiable_apply _)
    exact hmv.comp (differentiable_id.sub (differentiable_const _))
  · intro w
    simp only [hPhi_eq, add_sub_cancel_left]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · intro z
    rw [hPhi_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    abel

theorem localEOWChart_inverse_ball_geometry {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (Φinv : (Fin m → ℂ) → Fin m → ℂ)
    (hΦinv_diff : Differentiable ℂ Φinv)
    (hleft : ∀ w, Φinv (localEOWChart x0 ys w) = w)
    (hright : ∀ z, localEOWChart x0 ys (Φinv z) = z) :
    IsOpen (Φinv ⁻¹' Metric.ball (0 : Fin m → ℂ) ρ) ∧
    Convex ℝ (Φinv ⁻¹' Metric.ball (0 : Fin m → ℂ) ρ) ∧
    (∀ z ∈ Φinv ⁻¹' Metric.ball (0 : Fin m → ℂ) ρ,
      (fun i => starRingEnd ℂ (z i)) ∈ Φinv ⁻¹' Metric.ball (0 : Fin m → ℂ) ρ) ∧
    realEmbed x0 ∈ Φinv ⁻¹' Metric.ball (0 : Fin m → ℂ) ρ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Metric.isOpen_ball.preimage hΦinv_diff.continuous
  · intro z1 hz1 z2 hz2 a b ha hb hab
    let w1 := Φinv z1
    let w2 := Φinv z2
    have hcombo : a • z1 + b • z2 = localEOWChart x0 ys (a • w1 + b • w2) := by
      rw [← hright z1, ← hright z2,
        localEOWChart_affine_real_combo x0 ys w1 w2 a b hab]
    show Φinv (a • z1 + b • z2) ∈ Metric.ball (0 : Fin m → ℂ) ρ
    rw [hcombo, hleft]
    exact (convex_ball (0 : Fin m → ℂ) ρ) hz1 hz2 ha hb hab
  · intro z hz
    change Φinv (fun i => starRingEnd ℂ (z i)) ∈ Metric.ball (0 : Fin m → ℂ) ρ
    rw [localEOWChart_inverse_conj x0 ys Φinv hleft hright z]
    change Φinv z ∈ Metric.ball (0 : Fin m → ℂ) ρ at hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    suffices hnorm : ‖(fun j => starRingEnd ℂ (Φinv z j))‖ = ‖Φinv z‖ by
      rw [hnorm]
      exact hz
    simp only [Pi.norm_def]
    congr 1
    apply Finset.sup_congr rfl
    intro j _hj
    exact RCLike.nnnorm_conj _
  · show Φinv (realEmbed x0) ∈ Metric.ball (0 : Fin m → ℂ) ρ
    rw [show Φinv (realEmbed x0) = 0 from by rw [← localEOWChart_zero x0 ys, hleft]]
    exact Metric.mem_ball_self hρ

theorem continuous_localEOWRealChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    Continuous (localEOWRealChart x0 ys) := by
  change Continuous (fun u : Fin m → ℝ => fun a => x0 a + ∑ j, u j * ys j a)
  fun_prop

theorem localEOWRealChart_closedBall_subset {m : ℕ}
    {E : Set (Fin m → ℝ)}
    (hE_open : IsOpen E)
    (x0 : Fin m → ℝ) (hx0 : x0 ∈ E)
    (ys : Fin m → Fin m → ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ u : Fin m → ℝ, u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ →
        localEOWRealChart x0 ys u ∈ E := by
  have hpre_open : IsOpen ((localEOWRealChart x0 ys) ⁻¹' E) :=
    hE_open.preimage (continuous_localEOWRealChart x0 ys)
  have hzero : localEOWRealChart x0 ys 0 = x0 := by
    ext a
    simp [localEOWRealChart]
  have h0pre : (0 : Fin m → ℝ) ∈ (localEOWRealChart x0 ys) ⁻¹' E := by
    simpa [hzero] using hx0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre_open 0 h0pre
  refine ⟨ε / 2, by linarith, ?_⟩
  intro u hu
  exact hball (by
    have hdist : dist u (0 : Fin m → ℝ) ≤ ε / 2 := by
      simpa [Metric.mem_closedBall] using hu
    have hdist_lt : dist u (0 : Fin m → ℝ) < ε := by
      linarith
    simpa [Metric.mem_ball] using hdist_lt)

theorem localEOW_closedBall_support_margin {m : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) (ρ / 2),
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) r,
        u + t ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
  refine ⟨ρ / 2, by linarith, ?_⟩
  intro u hu t ht
  rw [Metric.mem_closedBall, dist_zero_right] at hu ht ⊢
  calc
    ‖u + t‖ ≤ ‖u‖ + ‖t‖ := norm_add_le u t
    _ ≤ ρ / 2 + ρ / 2 := add_le_add hu ht
    _ = ρ := by ring

def localEOWSmp {m : ℕ} (δ : ℝ)
    (w : Fin m → ℂ) (l : ℂ) : Fin m → ℂ :=
  fun j => (δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j

theorem localEOWSmp_zero {m : ℕ} {δ : ℝ}
    (hδ : δ ≠ 0) (w : Fin m → ℂ) :
    localEOWSmp δ w 0 = w := by
  ext j
  show (δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) 0 j = w j
  rw [moebiusProd_zero_right]
  exact (mul_comm _ _).trans (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hδ))

theorem localEOWSmp_im_pos_of_real {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {w : Fin m → ℂ}
    (hw_real : ∀ j, (w j).im = 0)
    (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
    {l : ℂ} (hl_pos : 0 < l.im) :
    ∀ j, 0 < (localEOWSmp δ w l j).im := by
  intro j
  show 0 < ((δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j).im
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_pos hδ
    (moebiusProd_im_pos_of_real
      (by
        intro k
        rw [Complex.div_ofReal_im]
        exact div_eq_zero_iff.mpr (Or.inl (hw_real k)))
      hw_norm hl_pos j)

theorem localEOWSmp_im_neg_of_real {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {w : Fin m → ℂ}
    (hw_real : ∀ j, (w j).im = 0)
    (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
    {l : ℂ} (hl_neg : l.im < 0) :
    ∀ j, (localEOWSmp δ w l j).im < 0 := by
  intro j
  show ((δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j).im < 0
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg hδ
    (moebiusProd_im_neg_of_real
      (by
        intro k
        rw [Complex.div_ofReal_im]
        exact div_eq_zero_iff.mpr (Or.inl (hw_real k)))
      hw_norm hl_neg j)

theorem localEOWSmp_norm_le_extended {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {w : Fin m → ℂ}
    (hw_half : ∀ j, ‖w j / (δ : ℂ)‖ ≤ 1 / 2)
    {l : ℂ} (hl : ‖l‖ ≤ 2) :
    ∀ j, ‖localEOWSmp δ w l j‖ ≤ δ * 10 := by
  intro j
  show ‖(δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j‖ ≤ δ * 10
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
  exact mul_le_mul_of_nonneg_left
    (moebiusProd_norm_le_extended hw_half hl j) hδ.le

theorem localEOWSmp_norm_le_extended_of_closedBall {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    {l : ℂ} (hl : ‖l‖ ≤ 2) :
    ∀ j, ‖localEOWSmp δ w l j‖ ≤ δ * 10 := by
  have hδ_cnorm : ‖(δ : ℂ)‖ = δ := by
    simp [Complex.norm_real, abs_of_pos hδ]
  have hw_half : ∀ j, ‖w j / (δ : ℂ)‖ ≤ 1 / 2 := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [norm_div, hδ_cnorm]
    calc
      ‖w j‖ / δ ≤ ‖w‖ / δ := by
        gcongr
        exact norm_le_pi_norm w j
      _ ≤ (δ / 2) / δ := by gcongr
      _ = 1 / 2 := by field_simp
  exact localEOWSmp_norm_le_extended hδ hw_half hl

theorem localEOWSmp_div_norm_lt_one_of_closedBall {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2)) :
    ∀ j, ‖w j / (δ : ℂ)‖ < 1 := by
  have hδ_cnorm : ‖(δ : ℂ)‖ = δ := by
    simp [Complex.norm_real, abs_of_pos hδ]
  intro j
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  rw [norm_div, hδ_cnorm]
  calc
    ‖w j‖ / δ ≤ ‖w‖ / δ := by
      gcongr
      exact norm_le_pi_norm w j
    _ ≤ (δ / 2) / δ := by gcongr
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

theorem localEOWSmp_im_zero_of_unit_real {m : ℕ} {δ : ℝ}
    {w : Fin m → ℂ} {l : ℂ}
    (hl_norm : Complex.normSq l = 1) (hl_im : l.im = 0) :
    ∀ j, (localEOWSmp δ w l j).im = 0 := by
  intro j
  show ((δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j).im = 0
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_eq_zero_of_right _ (moebiusProd_real_of_unit_real hl_norm hl_im j)

theorem localEOWSmp_im_zero_of_real {m : ℕ} {δ : ℝ}
    {w : Fin m → ℂ} {l : ℂ}
    (hw_real : ∀ j, (w j).im = 0) (hl_im : l.im = 0) :
    ∀ j, (localEOWSmp δ w l j).im = 0 := by
  have hw_div_real : ∀ j, (w j / (δ : ℂ)).im = 0 := by
    intro j
    rw [Complex.div_ofReal_im]
    exact div_eq_zero_iff.mpr (Or.inl (hw_real j))
  intro j
  show ((δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j).im = 0
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_eq_zero_of_right _ (moebiusProd_real hw_div_real hl_im j)

theorem localEOWChart_smp_realEdge_eq_of_unit_real {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ : ℝ} {w : Fin m → ℂ} {l : ℂ}
    (hl_norm : Complex.normSq l = 1) (hl_im : l.im = 0) :
    localEOWChart x0 ys (localEOWSmp δ w l) =
      realEmbed (localEOWRealChart x0 ys (fun j => (localEOWSmp δ w l j).re)) := by
  have him : ∀ j, (localEOWSmp δ w l j).im = 0 :=
    localEOWSmp_im_zero_of_unit_real hl_norm hl_im
  ext a
  simp only [localEOWChart, localEOWRealChart, realEmbed]
  rw [Complex.ofReal_add, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  have hsmp : localEOWSmp δ w l j = ((localEOWSmp δ w l j).re : ℂ) := by
    exact Complex.ext (by simp) (by simpa using him j)
  rw [hsmp, Complex.ofReal_mul]
  simp

theorem localEOWChart_smp_realEdge_eq_of_real {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ : ℝ} {w : Fin m → ℂ} {l : ℂ}
    (hw_real : ∀ j, (w j).im = 0) (hl_im : l.im = 0) :
    localEOWChart x0 ys (localEOWSmp δ w l) =
      realEmbed (localEOWRealChart x0 ys (fun j => (localEOWSmp δ w l j).re)) := by
  have him : ∀ j, (localEOWSmp δ w l j).im = 0 :=
    localEOWSmp_im_zero_of_real hw_real hl_im
  ext a
  simp only [localEOWChart, localEOWRealChart, realEmbed]
  rw [Complex.ofReal_add, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  have hsmp : localEOWSmp δ w l j = ((localEOWSmp δ w l j).re : ℂ) := by
    exact Complex.ext (by simp) (by simpa using him j)
  rw [hsmp, Complex.ofReal_mul]
  simp

theorem continuous_localEOWSmp_theta {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {w : Fin m → ℂ}
    (hw : w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) :
    Continuous (fun θ : ℝ =>
      localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))) := by
  apply continuous_pi fun j => ?_
  show Continuous (fun θ : ℝ =>
    (δ : ℂ) * moebiusRudin (w j / (δ : ℂ)) (Complex.exp ((θ : ℂ) * Complex.I)))
  have hwj : ‖w j / (δ : ℂ)‖ < 1 := by
    have hδ_cnorm : ‖(δ : ℂ)‖ = δ := by
      simp [Complex.norm_real, abs_of_pos hδ]
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_div, hδ_cnorm]
    calc
      ‖w j‖ / δ ≤ ‖w‖ / δ := by
        gcongr
        exact norm_le_pi_norm w j
      _ < (δ / 2) / δ := by gcongr
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  exact continuous_const.mul
    (moebiusRudin_continuousOn.comp_continuous
      (continuous_const.prodMk ((Complex.continuous_ofReal.mul continuous_const).cexp))
      (fun θ => Set.mem_prod.mpr
        ⟨by
          rw [Metric.mem_ball, dist_zero_right]
          exact hwj,
         by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (Complex.norm_exp_ofReal_mul_I θ).le⟩))

theorem continuousAt_localEOWSmp_of_norm_lt_two {m : ℕ} {δ : ℝ}
    {w : Fin m → ℂ} {l : ℂ}
    (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1) (hl : ‖l‖ < 2) :
    ContinuousAt (fun l' : ℂ => localEOWSmp δ w l') l := by
  apply continuousAt_pi.mpr
  intro j
  show ContinuousAt (fun l' : ℂ =>
    (δ : ℂ) * moebiusRudin (w j / (δ : ℂ)) l') l
  exact continuousAt_const.mul
    (moebiusRudin_differentiableAt_general
      (moebiusDenom_ne_zero_of_norm_prod (calc
        ‖(rudinC : ℂ) * l * (w j / (δ : ℂ))‖
            = rudinC * ‖l‖ * ‖w j / (δ : ℂ)‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real,
                Real.norm_of_nonneg rudinC_pos.le]
        _ ≤ rudinC * 2 * ‖w j / (δ : ℂ)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (le_of_lt hl) rudinC_pos.le) (norm_nonneg _)
        _ < rudinC * 2 * 1 :=
              mul_lt_mul_of_pos_left (hw_norm j) (mul_pos rudinC_pos (by norm_num))
        _ < 1 := by nlinarith [rudinC_lt_half]))).continuousAt

theorem continuousAt_localEOWChart_smp_of_norm_lt_two {m : ℕ} {δ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} {l : ℂ}
    (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1) (hl : ‖l‖ < 2) :
    ContinuousAt (fun l' : ℂ => localEOWChart x0 ys (localEOWSmp δ w l')) l :=
  (continuous_localEOWChart x0 ys).continuousAt.comp
    (continuousAt_localEOWSmp_of_norm_lt_two hw_norm hl)

theorem differentiableAt_localEOWSmp_of_real {m : ℕ} {δ : ℝ}
    {w : Fin m → ℂ} (hw_real : ∀ j, (w j).im = 0)
    {l : ℂ} (hl_ne : l.im ≠ 0) :
    DifferentiableAt ℂ (fun l' : ℂ => localEOWSmp δ w l') l := by
  rw [differentiableAt_pi]
  intro j
  show DifferentiableAt ℂ (fun l' : ℂ =>
    (δ : ℂ) * moebiusRudin (w j / (δ : ℂ)) l') l
  have hw_div_real : (w j / (δ : ℂ)).im = 0 := by
    rw [Complex.div_ofReal_im]
    exact div_eq_zero_iff.mpr (Or.inl (hw_real j))
  exact (differentiableAt_const _).mul
    (moebiusRudin_differentiableAt_of_real hw_div_real hl_ne)

theorem differentiableAt_localEOWChart_smp_of_real {m : ℕ} {δ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} (hw_real : ∀ j, (w j).im = 0)
    {l : ℂ} (hl_ne : l.im ≠ 0) :
    DifferentiableAt ℂ (fun l' : ℂ => localEOWChart x0 ys (localEOWSmp δ w l')) l :=
  (differentiable_localEOWChart x0 ys).differentiableAt.comp l
    (differentiableAt_localEOWSmp_of_real hw_real hl_ne)

theorem differentiableOn_localEOWChart_smp_upperHalfPlane_of_real {m : ℕ} {δ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} (hw_real : ∀ j, (w j).im = 0) :
    DifferentiableOn ℂ (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      EOW.UpperHalfPlane := by
  intro l hl
  exact (differentiableAt_localEOWChart_smp_of_real x0 ys hw_real
    (ne_of_gt hl)).differentiableWithinAt

theorem differentiableOn_localEOWChart_smp_lowerHalfPlane_of_real {m : ℕ} {δ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} (hw_real : ∀ j, (w j).im = 0) :
    DifferentiableOn ℂ (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      EOW.LowerHalfPlane := by
  intro l hl
  exact (differentiableAt_localEOWChart_smp_of_real x0 ys hw_real
    (ne_of_lt hl)).differentiableWithinAt

theorem localEOWSmp_re_mem_closedBall {m : ℕ} {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ) {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    {l : ℂ} (hl : ‖l‖ ≤ 2) :
    (fun j => (localEOWSmp δ w l j).re) ∈
      Metric.closedBall (0 : Fin m → ℝ) ρ := by
  have hnorm : ∀ j, ‖localEOWSmp δ w l j‖ ≤ δ * 10 :=
    localEOWSmp_norm_le_extended_of_closedBall hδ hw hl
  rw [Metric.mem_closedBall, dist_zero_right]
  exact
    (pi_norm_le_iff_of_nonneg
      (le_trans (mul_nonneg hδ.le (by norm_num)) hδρ)).mpr
      (by
        intro j
        rw [Real.norm_eq_abs]
        calc
          |(localEOWSmp δ w l j).re| ≤ ‖localEOWSmp δ w l j‖ :=
            Complex.abs_re_le_norm _
          _ ≤ δ * 10 := hnorm j
          _ ≤ ρ := hδρ)

theorem exists_localEOWSmp_delta {m : ℕ} (hm : 0 < m)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ * 10 ≤ ρ ∧
      (Fintype.card (Fin m) : ℝ) * (δ * 10) < r := by
  let c : ℝ := Fintype.card (Fin m)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟨0, hm⟩⟩ : 0 < Fintype.card (Fin m))
  let δ : ℝ := min (ρ / 20) (r / (c * 20))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (div_pos hr (mul_pos hc (by norm_num)))
  refine ⟨δ, hδpos, ?_, ?_⟩
  · have hδle : δ ≤ ρ / 20 := by
      dsimp [δ]
      exact min_le_left _ _
    nlinarith
  · have hδle : δ ≤ r / (c * 20) := by
      dsimp [δ]
      exact min_le_right _ _
    have hmul : c * (δ * 10) ≤ c * ((r / (c * 20)) * 10) := by
      gcongr
    have heq : c * ((r / (c * 20)) * 10) = r / 2 := by
      field_simp [ne_of_gt hc]
      ring
    calc
      c * (δ * 10) ≤ c * ((r / (c * 20)) * 10) := hmul
      _ = r / 2 := heq
      _ < r := by linarith

theorem localEOWChart_smp_upper_mem_of_delta {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {w : Fin m → ℂ} {l : ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    (hl_pos : 0 < l.im) (hl_norm : ‖l‖ ≤ 2) :
    localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus := by
  let u : Fin m → ℝ := fun j => (localEOWSmp δ w l j).re
  let v : Fin m → ℝ := fun j => (localEOWSmp δ w l j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWSmp_re_mem_closedBall hδ hδρ hw hl_norm
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  have hv_pos : ∀ j, 0 < v j := by
    intro j
    simpa [v] using localEOWSmp_im_pos_of_real hδ hw_real hw_norm hl_pos j
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => (hv_pos j).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : v j0 ≤ ∑ j, v j :=
      Finset.single_le_sum (fun j _ => hv_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (hv_pos j0) hle
  have hv_bound : ∀ j, v j ≤ δ * 10 := by
    intro j
    calc
      v j ≤ |v j| := le_abs_self _
      _ ≤ ‖localEOWSmp δ w l j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWSmp δ w l j)
      _ ≤ δ * 10 := localEOWSmp_norm_le_extended_of_closedBall hδ hw hl_norm j
  have hv_sum_lt : (∑ j, v j) < r := by
    calc
      ∑ j, v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hplus u hu v hv_nonneg hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) =
        localEOWSmp δ w l := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

theorem localEOWChart_smp_lower_mem_of_delta {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : Fin m → ℂ} {l : ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    (hl_neg : l.im < 0) (hl_norm : ‖l‖ ≤ 2) :
    localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus := by
  let u : Fin m → ℝ := fun j => (localEOWSmp δ w l j).re
  let v : Fin m → ℝ := fun j => (localEOWSmp δ w l j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWSmp_re_mem_closedBall hδ hδρ hw hl_norm
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  have hv_neg : ∀ j, v j < 0 := by
    intro j
    simpa [v] using localEOWSmp_im_neg_of_real hδ hw_real hw_norm hl_neg j
  have hv_nonpos : ∀ j, v j ≤ 0 := fun j => (hv_neg j).le
  have hneg_nonneg : ∀ j, 0 ≤ -v j := fun j => neg_nonneg.mpr (hv_nonpos j)
  have hv_sum_pos : 0 < ∑ j, -v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : -v j0 ≤ ∑ j, -v j :=
      Finset.single_le_sum (fun j _ => hneg_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (neg_pos.mpr (hv_neg j0)) hle
  have hv_bound : ∀ j, -v j ≤ δ * 10 := by
    intro j
    calc
      -v j ≤ |-v j| := le_abs_self _
      _ = |v j| := abs_neg _
      _ ≤ ‖localEOWSmp δ w l j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWSmp δ w l j)
      _ ≤ δ * 10 := localEOWSmp_norm_le_extended_of_closedBall hδ hw hl_norm j
  have hv_sum_lt : (∑ j, -v j) < r := by
    calc
      ∑ j, -v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hminus u hu v hv_nonpos hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) =
        localEOWSmp δ w l := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

theorem tendsto_localEOWChart_smp_upperHalfPlane_to_realEdge {m : ℕ}
    (hm : 0 < m)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {Ωplus : Set (Fin m → ℂ)} {δ ρ r : ℝ}
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    {x : ℝ} (hx : |x| < 2) :
    Filter.Tendsto (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
      (nhdsWithin
        (realEmbed (localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ w (x : ℂ) j).re))) Ωplus) := by
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  have hx_norm : ‖(x : ℂ)‖ < 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hca : ContinuousAt
      (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l)) (x : ℂ) :=
    continuousAt_localEOWChart_smp_of_norm_lt_two x0 ys hw_norm hx_norm
  have hreal : localEOWChart x0 ys (localEOWSmp δ w (x : ℂ)) =
      realEmbed (localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re)) :=
    localEOWChart_smp_realEdge_eq_of_real x0 ys hw_real (Complex.ofReal_im x)
  have h_nhds : Filter.Tendsto
      (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
      (nhds (realEmbed (localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re)))) := by
    rw [← hreal]
    exact hca.tendsto.mono_left nhdsWithin_le_nhds
  have h_event_norm_nhds : ∀ᶠ l : ℂ in nhds (x : ℂ), ‖l‖ < 2 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx_norm
  have h_event_norm :
      ∀ᶠ l : ℂ in nhdsWithin (x : ℂ) EOW.UpperHalfPlane, ‖l‖ < 2 :=
    h_event_norm_nhds.filter_mono nhdsWithin_le_nhds
  have h_mem : ∀ᶠ l : ℂ in nhdsWithin (x : ℂ) EOW.UpperHalfPlane,
      localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus := by
    filter_upwards [eventually_nhdsWithin_of_forall fun l hl => hl, h_event_norm]
      with l hlU hl_norm
    exact localEOWChart_smp_upper_mem_of_delta hm Ωplus x0 ys hδ hδρ hδsum hplus
      hw hw_real hlU (le_of_lt hl_norm)
  exact Filter.tendsto_inf.mpr ⟨h_nhds, Filter.tendsto_principal.mpr h_mem⟩

theorem tendsto_localEOWChart_smp_lowerHalfPlane_to_realEdge {m : ℕ}
    (hm : 0 < m)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {Ωminus : Set (Fin m → ℂ)} {δ ρ r : ℝ}
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    {x : ℝ} (hx : |x| < 2) :
    Filter.Tendsto (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
      (nhdsWithin
        (realEmbed (localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ w (x : ℂ) j).re))) Ωminus) := by
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  have hx_norm : ‖(x : ℂ)‖ < 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hca : ContinuousAt
      (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l)) (x : ℂ) :=
    continuousAt_localEOWChart_smp_of_norm_lt_two x0 ys hw_norm hx_norm
  have hreal : localEOWChart x0 ys (localEOWSmp δ w (x : ℂ)) =
      realEmbed (localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re)) :=
    localEOWChart_smp_realEdge_eq_of_real x0 ys hw_real (Complex.ofReal_im x)
  have h_nhds : Filter.Tendsto
      (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
      (nhds (realEmbed (localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re)))) := by
    rw [← hreal]
    exact hca.tendsto.mono_left nhdsWithin_le_nhds
  have h_event_norm_nhds : ∀ᶠ l : ℂ in nhds (x : ℂ), ‖l‖ < 2 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx_norm
  have h_event_norm :
      ∀ᶠ l : ℂ in nhdsWithin (x : ℂ) EOW.LowerHalfPlane, ‖l‖ < 2 :=
    h_event_norm_nhds.filter_mono nhdsWithin_le_nhds
  have h_mem : ∀ᶠ l : ℂ in nhdsWithin (x : ℂ) EOW.LowerHalfPlane,
      localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus := by
    filter_upwards [eventually_nhdsWithin_of_forall fun l hl => hl, h_event_norm]
      with l hlL hl_norm
    exact localEOWChart_smp_lower_mem_of_delta hm Ωminus x0 ys hδ hδρ hδsum hminus
      hw hw_real hlL (le_of_lt hl_norm)
  exact Filter.tendsto_inf.mpr ⟨h_nhds, Filter.tendsto_principal.mpr h_mem⟩

theorem continuousAt_localEOWRealChart_smp_re_of_norm_lt_two {m : ℕ} {δ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} {t : ℝ}
    (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1) (ht : |t| < 2) :
    ContinuousAt
      (fun s : ℝ =>
        localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (s : ℂ) j).re)) t := by
  have ht_norm : ‖(t : ℂ)‖ < 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ht
  have hsmp_ca : ContinuousAt (fun l : ℂ => localEOWSmp δ w l) (t : ℂ) :=
    continuousAt_localEOWSmp_of_norm_lt_two hw_norm ht_norm
  have hcoords : ContinuousAt
      (fun s : ℝ => fun j => (localEOWSmp δ w (s : ℂ) j).re) t := by
    apply continuousAt_pi.mpr
    intro j
    exact Complex.continuous_re.continuousAt.comp
      ((continuous_apply j).continuousAt.comp
        (hsmp_ca.comp Complex.continuous_ofReal.continuousAt))
  exact (continuous_localEOWRealChart x0 ys).continuousAt.comp hcoords

theorem continuousAt_localEOWBoundaryValue_smp {m : ℕ} {δ : ℝ}
    {E : Set (Fin m → ℝ)} (hE_open : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} {t : ℝ}
    (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1) (ht : |t| < 2)
    (hmem : ∀ s : ℝ, |s| < 2 →
      localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (s : ℂ) j).re) ∈ E) :
    ContinuousAt
      (fun s : ℝ =>
        bv (localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (s : ℂ) j).re))) t := by
  let chartPath : ℝ → Fin m → ℝ := fun s =>
    localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (s : ℂ) j).re)
  have hchart : ContinuousAt chartPath t := by
    simpa [chartPath] using
      continuousAt_localEOWRealChart_smp_re_of_norm_lt_two x0 ys hw_norm ht
  have hbv_ca : ContinuousAt bv (chartPath t) := by
    exact hbv_cont.continuousAt (hE_open.mem_nhds (by simpa [chartPath] using hmem t ht))
  change ContinuousAt (bv ∘ chartPath) t
  exact hbv_ca.comp hchart

theorem differentiableOn_localEOWUpperBranch_smp_of_real {m : ℕ} {δ : ℝ}
    (Ωplus : Set (Fin m → ℂ)) (hΩplus_open : IsOpen Ωplus)
    (Fplus : (Fin m → ℂ) → ℂ) (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} (hw_real : ∀ j, (w j).im = 0)
    (hmem : ∀ l ∈ Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane,
      localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus) :
    DifferentiableOn ℂ
      (fun l : ℂ => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)))
      (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) := by
  intro l hl
  have hl_ne : l.im ≠ 0 := ne_of_gt hl.2
  have hchart_da : DifferentiableAt ℂ
      (fun l' : ℂ => localEOWChart x0 ys (localEOWSmp δ w l')) l :=
    differentiableAt_localEOWChart_smp_of_real x0 ys hw_real hl_ne
  have hF_da : DifferentiableAt ℂ Fplus (localEOWChart x0 ys (localEOWSmp δ w l)) :=
    hFplus_diff.differentiableAt (hΩplus_open.mem_nhds (hmem l hl))
  exact (hF_da.comp l hchart_da).differentiableWithinAt

theorem differentiableOn_localEOWLowerBranch_smp_of_real {m : ℕ} {δ : ℝ}
    (Ωminus : Set (Fin m → ℂ)) (hΩminus_open : IsOpen Ωminus)
    (Fminus : (Fin m → ℂ) → ℂ) (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {w : Fin m → ℂ} (hw_real : ∀ j, (w j).im = 0)
    (hmem : ∀ l ∈ Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane,
      localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus) :
    DifferentiableOn ℂ
      (fun l : ℂ => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)))
      (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) := by
  intro l hl
  have hl_ne : l.im ≠ 0 := ne_of_lt hl.2
  have hchart_da : DifferentiableAt ℂ
      (fun l' : ℂ => localEOWChart x0 ys (localEOWSmp δ w l')) l :=
    differentiableAt_localEOWChart_smp_of_real x0 ys hw_real hl_ne
  have hF_da : DifferentiableAt ℂ Fminus (localEOWChart x0 ys (localEOWSmp δ w l)) :=
    hFminus_diff.differentiableAt (hΩminus_open.mem_nhds (hmem l hl))
  exact (hF_da.comp l hchart_da).differentiableWithinAt

theorem tendsto_localEOWUpperBranch_smp_to_boundaryValue {m : ℕ}
    (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {E : Set (Fin m → ℝ)}
    (Fplus : (Fin m → ℂ) → ℂ) (bv : (Fin m → ℝ) → ℂ)
    (hFplus_bv : ∀ y ∈ E,
      Filter.Tendsto Fplus (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    {x : ℝ} (hx : |x| < 2)
    (hE_mem : localEOWRealChart x0 ys
      (fun j => (localEOWSmp δ w (x : ℂ) j).re) ∈ E) :
    Filter.Tendsto
      (fun l : ℂ => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)))
      (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
      (nhds (bv (localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re)))) := by
  exact (hFplus_bv _ hE_mem).comp
    (tendsto_localEOWChart_smp_upperHalfPlane_to_realEdge hm x0 ys hδ hδρ hδsum
      hplus hw hw_real hx)

theorem tendsto_localEOWLowerBranch_smp_to_boundaryValue {m : ℕ}
    (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {E : Set (Fin m → ℝ)}
    (Fminus : (Fin m → ℂ) → ℂ) (bv : (Fin m → ℝ) → ℂ)
    (hFminus_bv : ∀ y ∈ E,
      Filter.Tendsto Fminus (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    {x : ℝ} (hx : |x| < 2)
    (hE_mem : localEOWRealChart x0 ys
      (fun j => (localEOWSmp δ w (x : ℂ) j).re) ∈ E) :
    Filter.Tendsto
      (fun l : ℂ => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)))
      (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
      (nhds (bv (localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re)))) := by
  exact (hFminus_bv _ hE_mem).comp
    (tendsto_localEOWChart_smp_lowerHalfPlane_to_realEdge hm x0 ys hδ hδρ hδsum
      hminus hw hw_real hx)

set_option maxHeartbeats 800000 in
theorem local_rudin_mean_value_real {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    {E : Set (Fin m → ℝ)} (hE_open : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hFplus_bv : ∀ y ∈ E,
      Filter.Tendsto Fplus (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    (hFminus_bv : ∀ y ∈ E,
      Filter.Tendsto Fminus (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    (hE_mem : ∀ s : ℝ, |s| < 2 →
      localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (s : ℂ) j).re) ∈ E) :
    let G : ℝ → ℂ := fun θ =>
      if 0 < Real.sin θ then
        Fplus (localEOWChart x0 ys
          (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
      else if Real.sin θ < 0 then
        Fminus (localEOWChart x0 ys
          (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
      else 0
    (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G θ =
      bv (localEOWRealChart x0 ys (fun j => (w j).re)) := by
  intro G
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  let bv_smp : ℝ → ℂ := fun t =>
    bv (localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (t : ℂ) j).re))
  let gp : ℂ → ℂ := fun l =>
    if l.im > 0 then Fplus (localEOWChart x0 ys (localEOWSmp δ w l))
    else bv_smp l.re
  let gm : ℂ → ℂ := fun l =>
    if l.im < 0 then Fminus (localEOWChart x0 ys (localEOWSmp δ w l))
    else bv_smp l.re
  have hmem_upper : ∀ l ∈ Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane,
      localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus := by
    intro l hl
    have hl_norm_lt : ‖l‖ < 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hl.1
    exact localEOWChart_smp_upper_mem_of_delta hm Ωplus x0 ys hδ hδρ hδsum hplus
      hw hw_real hl.2 (le_of_lt hl_norm_lt)
  have hmem_lower : ∀ l ∈ Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane,
      localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus := by
    intro l hl
    have hl_norm_lt : ‖l‖ < 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hl.1
    exact localEOWChart_smp_lower_mem_of_delta hm Ωminus x0 ys hδ hδρ hδsum hminus
      hw hw_real hl.2 (le_of_lt hl_norm_lt)
  have hgp_diff_comp : DifferentiableOn ℂ
      (fun l : ℂ => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)))
      (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) :=
    differentiableOn_localEOWUpperBranch_smp_of_real Ωplus hΩplus_open Fplus
      hFplus_diff x0 ys hw_real hmem_upper
  have hgm_diff_comp : DifferentiableOn ℂ
      (fun l : ℂ => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)))
      (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) :=
    differentiableOn_localEOWLowerBranch_smp_of_real Ωminus hΩminus_open Fminus
      hFminus_diff x0 ys hw_real hmem_lower
  have hgp_diff : DifferentiableOn ℂ gp
      (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) := by
    exact hgp_diff_comp.congr (fun l hl => by
      have hl' : 0 < l.im := by simpa [EOW.UpperHalfPlane] using hl.2
      show gp l = Fplus (localEOWChart x0 ys (localEOWSmp δ w l))
      simp [gp, hl'])
  have hgm_diff : DifferentiableOn ℂ gm
      (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) := by
    exact hgm_diff_comp.congr (fun l hl => by
      have hl' : l.im < 0 := by simpa [EOW.LowerHalfPlane] using hl.2
      show gm l = Fminus (localEOWChart x0 ys (localEOWSmp δ w l))
      simp [gm, hl'])
  have hgp_diff_disk : DifferentiableOn ℂ gp
      (Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) ∩
        EOW.UpperHalfPlane) := by
    simpa using hgp_diff
  have hgm_diff_disk : DifferentiableOn ℂ gm
      (Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) ∩
        EOW.LowerHalfPlane) := by
    simpa using hgm_diff
  have hgp_eq_real : ∀ l : ℂ, l.im = 0 → gp l = bv_smp l.re := by
    intro l hl
    simp [gp, hl]
  have hgm_eq_real : ∀ l : ℂ, l.im = 0 → gm l = bv_smp l.re := by
    intro l hl
    simp [gm, hl]
  have hmatch : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 → gp (x : ℂ) = gm (x : ℂ) := by
    intro x _ _
    rw [hgp_eq_real (x : ℂ) (Complex.ofReal_im x),
      hgm_eq_real (x : ℂ) (Complex.ofReal_im x)]
  have hgp_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gp (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (gp (x : ℂ))) := by
    intro x hx_lo hx_hi
    have hx_abs : |x| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx_mem : localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re) ∈ E := hE_mem x hx_abs
    have hgp_at : gp (x : ℂ) = bv_smp x := by
      rw [hgp_eq_real (x : ℂ) (Complex.ofReal_im x)]
      simp [bv_smp]
    rw [hgp_at]
    have hbranch := tendsto_localEOWUpperBranch_smp_to_boundaryValue hm Ωplus x0 ys
      Fplus bv hFplus_bv hδ hδρ hδsum hplus hw hw_real hx_abs hx_mem
    have heq : (fun l : ℂ => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)))
        =ᶠ[nhdsWithin (x : ℂ) EOW.UpperHalfPlane] gp := by
      filter_upwards [self_mem_nhdsWithin] with l hl
      have hl' : 0 < l.im := by simpa [EOW.UpperHalfPlane] using hl
      show Fplus (localEOWChart x0 ys (localEOWSmp δ w l)) = gp l
      simp [gp, hl']
    simpa [bv_smp] using Filter.Tendsto.congr' heq hbranch
  have hgm_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gm (nhdsWithin (x : ℂ) EOW.LowerHalfPlane) (nhds (gm (x : ℂ))) := by
    intro x hx_lo hx_hi
    have hx_abs : |x| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx_mem : localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ w (x : ℂ) j).re) ∈ E := hE_mem x hx_abs
    have hgm_at : gm (x : ℂ) = bv_smp x := by
      rw [hgm_eq_real (x : ℂ) (Complex.ofReal_im x)]
      simp [bv_smp]
    rw [hgm_at]
    have hbranch := tendsto_localEOWLowerBranch_smp_to_boundaryValue hm Ωminus x0 ys
      Fminus bv hFminus_bv hδ hδρ hδsum hminus hw hw_real hx_abs hx_mem
    have heq : (fun l : ℂ => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)))
        =ᶠ[nhdsWithin (x : ℂ) EOW.LowerHalfPlane] gm := by
      filter_upwards [self_mem_nhdsWithin] with l hl
      have hl' : l.im < 0 := by simpa [EOW.LowerHalfPlane] using hl
      show Fminus (localEOWChart x0 ys (localEOWSmp δ w l)) = gm l
      simp [gm, hl']
    simpa [bv_smp] using Filter.Tendsto.congr' heq hbranch
  have hbv_real : ∀ x₀ : ℝ, (-2 : ℝ) < x₀ → x₀ < 2 →
      Filter.Tendsto gp (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (gp (x₀ : ℂ))) := by
    intro t ht_lo ht_hi
    have ht_abs : |t| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hgp_at : gp (t : ℂ) = bv_smp t := by
      rw [hgp_eq_real (t : ℂ) (Complex.ofReal_im t)]
      simp [bv_smp]
    rw [hgp_at]
    have hbv_ca : ContinuousAt bv_smp t := by
      simpa [bv_smp] using
        continuousAt_localEOWBoundaryValue_smp hE_open bv hbv_cont x0 ys hw_norm ht_abs hE_mem
    have htend : Filter.Tendsto (fun l : ℂ => bv_smp l.re)
        (nhdsWithin (t : ℂ) {c : ℂ | c.im = 0}) (nhds (bv_smp t)) :=
      hbv_ca.tendsto.comp
        (Complex.continuous_re.continuousAt.mono_left nhdsWithin_le_nhds)
    have heq : (fun l : ℂ => bv_smp l.re)
        =ᶠ[nhdsWithin (t : ℂ) {c : ℂ | c.im = 0}] gp := by
      filter_upwards [self_mem_nhdsWithin] with l hl
      have hl' : l.im = 0 := by simpa using hl
      show bv_smp l.re = gp l
      rw [hgp_eq_real l hl']
    exact Filter.Tendsto.congr' heq htend
  obtain ⟨U, F_disc, hU_open, _, _, hU_int, hF_holo, hF_gp, hF_gm, hball⟩ :=
    local_edge_of_the_wedge_1d (-2) 2 (by norm_num) gp gm
      hgp_diff_disk hgm_diff_disk hgp_bv hgm_bv hmatch hbv_real
  have hcb_sub : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    calc Metric.closedBall (0 : ℂ) 1
        ⊆ Metric.ball (0 : ℂ) 2 := by
          intro z hz
          simp [Metric.mem_closedBall, Metric.mem_ball] at hz ⊢
          linarith
      _ = Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) := by
          congr 1 <;> simp
      _ ⊆ U := hball
  have hF_da : ∀ z ∈ Metric.closedBall (0 : ℂ) (|1|), DifferentiableAt ℂ F_disc z := by
    intro z hz
    rw [abs_one] at hz
    exact hF_holo.differentiableAt (hU_open.mem_nhds (hcb_sub hz))
  have hmv : Real.circleAverage F_disc 0 1 = F_disc 0 := by
    have : DiffContOnCl ℂ F_disc (Metric.ball 0 |1|) := by
      constructor
      · exact fun z hz => (hF_da z (Metric.ball_subset_closedBall hz)).differentiableWithinAt
      · simp only [abs_one]
        rw [closure_ball (0 : ℂ) one_ne_zero]
        exact fun z hz => (hF_da z (by rwa [abs_one])).continuousAt.continuousWithinAt
    exact this.circleAverage
  have hF0 : F_disc 0 = bv (localEOWRealChart x0 ys (fun j => (w j).re)) := by
    have hsmp_zero : localEOWSmp δ w (0 : ℂ) = w := localEOWSmp_zero hδ_ne w
    have hgp_zero_val : gp (0 : ℂ) = bv (localEOWRealChart x0 ys (fun j => (w j).re)) := by
      rw [hgp_eq_real (0 : ℂ) Complex.zero_im, Complex.zero_re]
      change bv (localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ w ((0 : ℝ) : ℂ) j).re)) =
        bv (localEOWRealChart x0 ys (fun j => (w j).re))
      rw [Complex.ofReal_zero, hsmp_zero]
    have h0_mem : (0 : ℂ) ∈ U := hU_int 0 (by norm_num) (by norm_num)
    have h_nebot : Filter.NeBot (nhdsWithin (0 : ℂ) EOW.UpperHalfPlane) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
      · show 0 < ((ε / 2 : ℝ) * Complex.I).im
        simp [Complex.mul_im, Complex.I_re, Complex.I_im]
        linarith
      · show dist 0 ((ε / 2 : ℝ) * Complex.I) < ε
        rw [dist_comm, dist_zero_right, norm_mul, Complex.norm_real, Complex.norm_I,
          mul_one, Real.norm_eq_abs, abs_of_pos (by linarith : ε / 2 > 0)]
        linarith
    have h1 : Filter.Tendsto F_disc (nhdsWithin 0 EOW.UpperHalfPlane) (nhds (F_disc 0)) :=
      (hF_holo.continuousOn.continuousAt (hU_open.mem_nhds h0_mem)).tendsto.mono_left
        nhdsWithin_le_nhds
    have h2 : Filter.Tendsto F_disc (nhdsWithin 0 EOW.UpperHalfPlane) (nhds (gp 0)) := by
      have h_agree : ∀ᶠ z in nhdsWithin (0 : ℂ) EOW.UpperHalfPlane, F_disc z = gp z := by
        filter_upwards [nhdsWithin_le_nhds (hU_open.mem_nhds h0_mem),
          self_mem_nhdsWithin] with z hz_U hz_UHP
        exact hF_gp z ⟨hz_U, hz_UHP⟩
      exact Filter.Tendsto.congr' (h_agree.mono fun _ h => h.symm)
        (hgp_bv 0 (by norm_num) (by norm_num))
    rw [tendsto_nhds_unique h1 h2, hgp_zero_val]
  have hresult : (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G θ =
      Real.circleAverage F_disc 0 1 := by
    rw [Real.circleAverage_def]
    congr 1
    have hcm_eq : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := fun θ => by
      simp [circleMap_zero]
    have hcm_U : ∀ θ : ℝ, circleMap 0 1 θ ∈ U := fun θ =>
      hcb_sub (Metric.mem_closedBall.mpr
        (by rw [dist_zero_right, norm_circleMap_zero]; norm_num))
    have hle_pi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    have hae : ∀ᵐ (θ : ℝ), θ ∈ Set.uIoc (-Real.pi) Real.pi →
        G θ = F_disc (circleMap 0 1 θ) := by
      have h_ae_compl : ({0, Real.pi}ᶜ : Set ℝ) ∈ ae volume := by
        rw [compl_mem_ae_iff]
        exact (Set.toFinite {(0 : ℝ), Real.pi}).measure_zero _
      filter_upwards [h_ae_compl] with θ hθ hθ_mem
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
      obtain ⟨hne0, hneπ⟩ := hθ
      have hθ_lo : -Real.pi < θ := by
        have := hθ_mem.1
        rwa [min_eq_left hle_pi] at this
      have hθ_hi : θ ≤ Real.pi := by
        have := hθ_mem.2
        rwa [max_eq_right hle_pi] at this
      have hθ_lt_pi : θ < Real.pi := lt_of_le_of_ne hθ_hi hneπ
      rw [hcm_eq θ]
      have hcm_U' : Complex.exp ((θ : ℂ) * Complex.I) ∈ U := by
        rw [← hcm_eq]
        exact hcm_U θ
      by_cases hθ_pos : (0 : ℝ) < θ
      · have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
        have him : 0 < (Complex.exp ((θ : ℂ) * Complex.I)).im := by
          rwa [Complex.exp_ofReal_mul_I_im]
        have hmem : Complex.exp ((θ : ℂ) * Complex.I) ∈ U ∩ EOW.UpperHalfPlane := ⟨hcm_U', him⟩
        simp only [G, if_pos hsin_pos]
        rw [hF_gp _ hmem]
        simp only [gp, if_pos him]
      · have hθ_neg : θ < 0 := lt_of_le_of_ne (not_lt.mp hθ_pos) hne0
        have hsin_neg : Real.sin θ < 0 := by
          have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hθ_neg) (by linarith)
          linarith [Real.sin_neg θ]
        have him : (Complex.exp ((θ : ℂ) * Complex.I)).im < 0 := by
          rwa [Complex.exp_ofReal_mul_I_im]
        have hmem : Complex.exp ((θ : ℂ) * Complex.I) ∈ U ∩ EOW.LowerHalfPlane := ⟨hcm_U', him⟩
        simp only [G, if_neg (not_lt.mpr (le_of_lt hsin_neg)), if_pos hsin_neg]
        rw [hF_gm _ hmem]
        simp only [gm, if_pos him]
    have hperiodic : Function.Periodic (fun θ => F_disc (circleMap 0 1 θ)) (2 * Real.pi) :=
      fun θ => congr_arg F_disc (periodic_circleMap 0 1 θ)
    have hshift := hperiodic.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi from by ring,
        show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi from by ring] at hshift
    rw [intervalIntegral.integral_congr_ae hae, hshift]
  rw [hresult, hmv, hF0]

theorem exists_localEOWChart_smp_delta {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ {w : Fin m → ℂ} {l : ℂ},
        w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) →
        (∀ j, (w j).im = 0) →
        0 < l.im →
        ‖l‖ ≤ 2 →
          localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus) ∧
      (∀ {w : Fin m → ℂ} {l : ℂ},
        w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) →
        (∀ j, (w j).im = 0) →
        l.im < 0 →
        ‖l‖ ≤ 2 →
          localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus) := by
  obtain ⟨δ, hδ, hδρ, hδsum⟩ := exists_localEOWSmp_delta hm hρ hr
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro w l hw hw_real hl_pos hl_norm
    exact localEOWChart_smp_upper_mem_of_delta hm Ωplus x0 ys hδ hδρ hδsum
      hplus hw hw_real hl_pos hl_norm
  · intro w l hw hw_real hl_neg hl_norm
    exact localEOWChart_smp_lower_mem_of_delta hm Ωminus x0 ys hδ hδρ hδsum
      hminus hw hw_real hl_neg hl_norm

theorem isCompact_localEOWRealChart_image {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {B : Set (Fin m → ℝ)}
    (hB_compact : IsCompact B) :
    IsCompact (localEOWRealChart x0 ys '' B) :=
  hB_compact.image (continuous_localEOWRealChart x0 ys)

theorem localEOWChart_real_imag {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (u v : Fin m → ℝ) :
    localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) =
      fun a => (localEOWRealChart x0 ys u a : ℂ) +
        (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
  ext a
  simp only [localEOWChart, localEOWRealChart]
  have hsum :
      (∑ j : Fin m, ((u j : ℂ) + (v j : ℂ) * Complex.I) * (ys j a : ℂ)) =
        (∑ j : Fin m, (u j : ℂ) * (ys j a : ℂ)) +
          (∑ j : Fin m, (v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
    calc
      (∑ j : Fin m, ((u j : ℂ) + (v j : ℂ) * Complex.I) * (ys j a : ℂ))
          = ∑ j : Fin m, ((u j : ℂ) * (ys j a : ℂ) +
              ((v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin m, (u j : ℂ) * (ys j a : ℂ)) +
            ∑ j : Fin m, ((v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
            rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin m, (u j : ℂ) * (ys j a : ℂ)) +
            (∑ j : Fin m, (v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
            rw [Finset.sum_mul]
  rw [hsum]
  rw [Complex.ofReal_add, Complex.ofReal_sum]
  simp [Complex.ofReal_mul]
  ring

theorem isCompact_localEOWCoefficientSimplex (m : ℕ) :
    IsCompact (localEOWCoefficientSimplex m) := by
  let box : Set (Fin m → ℝ) :=
    Set.Icc (0 : Fin m → ℝ) 1
  have hbox : IsCompact box :=
    isCompact_Icc
  have hsum_cont : Continuous fun a : Fin m → ℝ => ∑ j, a j := by
    fun_prop
  have hsum_closed : IsClosed {a : Fin m → ℝ | ∑ j, a j = 1} :=
    isClosed_eq hsum_cont continuous_const
  have hsimplex :
      localEOWCoefficientSimplex m =
        box ∩ {a : Fin m → ℝ | ∑ j, a j = 1} := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨hcoords, hsum⟩
      refine ⟨?_, hsum⟩
      simpa [box, Set.mem_Icc, Pi.le_def] using
        (show (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) from
          ⟨fun i => (hcoords i).1, fun i => (hcoords i).2⟩)
    · intro ha
      rcases ha with ⟨hboxa, hsum⟩
      have hcoords : (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) := by
        simpa [box, Set.mem_Icc, Pi.le_def] using hboxa
      exact ⟨fun i => ⟨hcoords.1 i, hcoords.2 i⟩, hsum⟩
  rw [hsimplex]
  exact hbox.inter_right hsum_closed

theorem isCompact_localEOWSimplexDirections {m : ℕ}
    (ys : Fin m → Fin m → ℝ) :
    IsCompact (localEOWSimplexDirections ys) := by
  have hcont : Continuous fun a : Fin m → ℝ => ∑ j, a j • ys j := by
    fun_prop
  exact (isCompact_localEOWCoefficientSimplex m).image hcont

theorem localEOWSimplexDirections_subset_cone {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C) :
    localEOWSimplexDirections ys ⊆ C := by
  rintro y ⟨a, ha, rfl⟩
  exact hC_conv.sum_mem
    (t := Finset.univ)
    (w := a)
    (z := ys)
    (by
      intro j _hj
      exact (ha.1 j).1)
    (by simpa using ha.2)
    (by
      intro j _hj
      exact hys j)

theorem localEOW_positive_imag_normalized_mem_simplex {m : ℕ}
    {ys : Fin m → Fin m → ℝ}
    {v : Fin m → ℝ}
    (hv_nonneg : ∀ j, 0 ≤ v j)
    (hv_sum_pos : 0 < ∑ j, v j) :
    ((∑ j, v j)⁻¹) • (∑ j, v j • ys j) ∈
      localEOWSimplexDirections ys := by
  let s : ℝ := ∑ j, v j
  let a : Fin m → ℝ := fun j => s⁻¹ * v j
  have hs_pos : 0 < s := by
    simpa [s] using hv_sum_pos
  have ha_nonneg : ∀ j, 0 ≤ a j := by
    intro j
    exact mul_nonneg (inv_nonneg.mpr hs_pos.le) (hv_nonneg j)
  have hv_le_sum : ∀ j, v j ≤ s := by
    intro j
    simpa [s] using
      Finset.single_le_sum (fun i _hi => hv_nonneg i) (Finset.mem_univ j)
  have ha_le_one : ∀ j, a j ≤ 1 := by
    intro j
    have hmul := mul_le_mul_of_nonneg_left (hv_le_sum j) (inv_nonneg.mpr hs_pos.le)
    have hcancel : s⁻¹ * s = 1 := inv_mul_cancel₀ (ne_of_gt hs_pos)
    simpa [a, hcancel] using hmul
  have ha_sum : ∑ j, a j = 1 := by
    calc
      ∑ j, a j = s⁻¹ * ∑ j, v j := by
        simp [a, Finset.mul_sum]
      _ = s⁻¹ * s := by simp [s]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hs_pos)
  refine ⟨a, ?_, ?_⟩
  · exact ⟨fun j => ⟨ha_nonneg j, ha_le_one j⟩, ha_sum⟩
  · simp [a, s, Finset.smul_sum, smul_smul, mul_comm]

theorem localEOW_chart_positive_polywedge_mem {m : ℕ}
    (Ωplus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus)
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωplus := by
  have hKη_compact : IsCompact (localEOWSimplexDirections ys) :=
    isCompact_localEOWSimplexDirections ys
  have hKη_C : localEOWSimplexDirections ys ⊆ C :=
    localEOWSimplexDirections_subset_cone C hC_conv ys hys
  obtain ⟨r, hrpos, hrmem⟩ :=
    hlocal_wedge B hB_compact hB_E (localEOWSimplexDirections ys) hKη_compact hKη_C
  refine ⟨r, hrpos, ?_⟩
  intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
  let s : ℝ := ∑ j, v j
  let η : Fin m → ℝ := s⁻¹ • (∑ j, v j • ys j)
  have hη : η ∈ localEOWSimplexDirections ys := by
    dsimp [η, s]
    exact localEOW_positive_imag_normalized_mem_simplex hv_nonneg hv_sum_pos
  have hmem :=
    hrmem u hu η hη s (by simpa [s] using hv_sum_pos) (by simpa [s] using hv_sum_lt)
  have hpoint_eq :
      (fun a => (u a : ℂ) + (s : ℂ) * (η a : ℂ) * Complex.I) =
        (fun a =>
          (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
    ext a
    have hs_ne : s ≠ 0 := by
      dsimp [s]
      exact ne_of_gt hv_sum_pos
    have hηa : η a = s⁻¹ * (∑ j, v j * ys j a) := by
      simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hscale_real : s * η a = ∑ j, v j * ys j a := by
      rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
    have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (v j : ℂ) * (ys j a : ℂ) := by
      rw [← Complex.ofReal_mul, hscale_real]
      simp
    simp [hscale]
  rwa [← hpoint_eq]

theorem localEOW_chart_negative_polywedge_mem {m : ℕ}
    (Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωminus := by
  have hKη_compact : IsCompact (localEOWSimplexDirections ys) :=
    isCompact_localEOWSimplexDirections ys
  have hKη_C : localEOWSimplexDirections ys ⊆ C :=
    localEOWSimplexDirections_subset_cone C hC_conv ys hys
  obtain ⟨r, hrpos, hrmem⟩ :=
    hlocal_wedge B hB_compact hB_E (localEOWSimplexDirections ys) hKη_compact hKη_C
  refine ⟨r, hrpos, ?_⟩
  intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
  let w : Fin m → ℝ := fun j => -v j
  let s : ℝ := ∑ j, w j
  let η : Fin m → ℝ := s⁻¹ • (∑ j, w j • ys j)
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    exact neg_nonneg.mpr (hv_nonpos j)
  have hw_sum_pos : 0 < ∑ j, w j := by
    simpa [w] using hv_sum_pos
  have hw_sum_lt : ∑ j, w j < r := by
    simpa [w] using hv_sum_lt
  have hη : η ∈ localEOWSimplexDirections ys := by
    dsimp [η, s]
    exact localEOW_positive_imag_normalized_mem_simplex hw_nonneg hw_sum_pos
  have hmem :=
    hrmem u hu η hη s (by simpa [s] using hw_sum_pos) (by simpa [s] using hw_sum_lt)
  have hpoint_eq :
      (fun a => (u a : ℂ) - (s : ℂ) * (η a : ℂ) * Complex.I) =
        (fun a =>
          (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
    ext a
    have hs_ne : s ≠ 0 := by
      dsimp [s]
      exact ne_of_gt hw_sum_pos
    have hηa : η a = s⁻¹ * (∑ j, w j * ys j a) := by
      simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hscale_real : s * η a = ∑ j, w j * ys j a := by
      rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
    have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (w j : ℂ) * (ys j a : ℂ) := by
      rw [← Complex.ofReal_mul, hscale_real]
      simp
    simp [hscale, w]
  rwa [← hpoint_eq]

theorem localEOW_chart_twoSided_polywedge_mem {m : ℕ}
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωplus) ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωminus) := by
  have hKη_compact : IsCompact (localEOWSimplexDirections ys) :=
    isCompact_localEOWSimplexDirections ys
  have hKη_C : localEOWSimplexDirections ys ⊆ C :=
    localEOWSimplexDirections_subset_cone C hC_conv ys hys
  obtain ⟨r, hrpos, hrmem⟩ :=
    hlocal_wedge B hB_compact hB_E (localEOWSimplexDirections ys) hKη_compact hKη_C
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
    let s : ℝ := ∑ j, v j
    let η : Fin m → ℝ := s⁻¹ • (∑ j, v j • ys j)
    have hη : η ∈ localEOWSimplexDirections ys := by
      dsimp [η, s]
      exact localEOW_positive_imag_normalized_mem_simplex hv_nonneg hv_sum_pos
    have hmem :=
      (hrmem u hu η hη s (by simpa [s] using hv_sum_pos)
        (by simpa [s] using hv_sum_lt)).1
    have hpoint_eq :
        (fun a => (u a : ℂ) + (s : ℂ) * (η a : ℂ) * Complex.I) =
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
      ext a
      have hs_ne : s ≠ 0 := by
        dsimp [s]
        exact ne_of_gt hv_sum_pos
      have hηa : η a = s⁻¹ * (∑ j, v j * ys j a) := by
        simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hscale_real : s * η a = ∑ j, v j * ys j a := by
        rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
      have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (v j : ℂ) * (ys j a : ℂ) := by
        rw [← Complex.ofReal_mul, hscale_real]
        simp
      simp [hscale]
    rwa [← hpoint_eq]
  · intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
    let w : Fin m → ℝ := fun j => -v j
    let s : ℝ := ∑ j, w j
    let η : Fin m → ℝ := s⁻¹ • (∑ j, w j • ys j)
    have hw_nonneg : ∀ j, 0 ≤ w j := by
      intro j
      exact neg_nonneg.mpr (hv_nonpos j)
    have hw_sum_pos : 0 < ∑ j, w j := by
      simpa [w] using hv_sum_pos
    have hw_sum_lt : ∑ j, w j < r := by
      simpa [w] using hv_sum_lt
    have hη : η ∈ localEOWSimplexDirections ys := by
      dsimp [η, s]
      exact localEOW_positive_imag_normalized_mem_simplex hw_nonneg hw_sum_pos
    have hmem :=
      (hrmem u hu η hη s (by simpa [s] using hw_sum_pos)
        (by simpa [s] using hw_sum_lt)).2
    have hpoint_eq :
        (fun a => (u a : ℂ) - (s : ℂ) * (η a : ℂ) * Complex.I) =
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
      ext a
      have hs_ne : s ≠ 0 := by
        dsimp [s]
        exact ne_of_gt hw_sum_pos
      have hηa : η a = s⁻¹ * (∑ j, w j * ys j a) := by
        simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hscale_real : s * η a = ∑ j, w j * ys j a := by
        rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
      have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (w j : ℂ) * (ys j a : ℂ) := by
        rw [← Complex.ofReal_mul, hscale_real]
        simp
      simp [hscale, w]
    rwa [← hpoint_eq]

theorem localEOWChart_twoSided_polywedge_mem {m : ℕ}
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (hC_conv : Convex ℝ C)
    (x0 : Fin m → ℝ)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : localEOWRealChart x0 ys '' B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus) ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) := by
  have hBimg_compact : IsCompact (localEOWRealChart x0 ys '' B) :=
    isCompact_localEOWRealChart_image x0 ys hB_compact
  obtain ⟨r, hrpos, hplus, hminus⟩ :=
    localEOW_chart_twoSided_polywedge_mem Ωplus Ωminus E C hlocal_wedge hC_conv ys hys
      (localEOWRealChart x0 ys '' B) hBimg_compact hB_E
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
    have hmem := hplus (localEOWRealChart x0 ys u) ⟨u, hu, rfl⟩ v
      hv_nonneg hv_sum_pos hv_sum_lt
    rwa [localEOWChart_real_imag]
  · intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
    have hmem := hminus (localEOWRealChart x0 ys u) ⟨u, hu, rfl⟩ v
      hv_nonpos hv_sum_pos hv_sum_lt
    rwa [localEOWChart_real_imag]

end SCV
