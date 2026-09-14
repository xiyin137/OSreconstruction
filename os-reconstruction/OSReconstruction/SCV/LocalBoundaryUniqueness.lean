import OSReconstruction.SCV.LocalDistributionalEOW
import OSReconstruction.SCV.LocalEOWChartEnvelope

/-!
# Local Distributional Boundary Uniqueness

Compact real mollification converts raywise weak boundary zero into continuous
zero traces on fixed complex lines. Local one-variable edge-of-the-wedge and
an approximate identity give uniqueness on a smaller tube neighborhood.
No global half-plane extension or uniform cone-direction limit is required.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace SCV

/-- Zero continuous boundary trace on a diameter determines a holomorphic
function on the upper half-disk. No global half-plane extension is assumed. -/
theorem local_uniqueness_of_boundary_zero {r : ℝ} (hr : 0 < r)
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r ∩ EOW.UpperHalfPlane))
    (hb : ∀ a : ℝ, |a| < r →
      Tendsto g (nhdsWithin (a : ℂ) EOW.UpperHalfPlane) (nhds 0)) :
    ∀ z ∈ Metric.ball (0 : ℂ) r ∩ EOW.UpperHalfPlane, g z = 0 := by
  let gPlus : ℂ → ℂ := fun z => if z.im = 0 then 0 else g z
  have hball :
      Metric.ball (((-r + r) / 2 : ℝ) : ℂ) ((r - -r) / 2) = Metric.ball 0 r := by
    congr 1 <;> push_cast <;> ring
  have hgPlus : DifferentiableOn ℂ gPlus
      (Metric.ball (((-r + r) / 2 : ℝ) : ℂ) ((r - -r) / 2) ∩ EOW.UpperHalfPlane) := by
    rw [hball]
    refine hg.congr ?_
    intro z hz
    simp [gPlus, ne_of_gt (show 0 < z.im from hz.2)]
  have htrace : ∀ a : ℝ, -r < a → a < r →
      Tendsto gPlus (nhdsWithin (a : ℂ) EOW.UpperHalfPlane) (nhds (gPlus a)) := by
    intro a ha ha'
    simp only [gPlus, Complex.ofReal_im, ite_true]
    refine (hb a (abs_lt.mpr ⟨ha, ha'⟩)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [ne_of_gt (show 0 < z.im from hz)]
  obtain ⟨U, F, hU, hUconv, _, _, hF, hFplus, hFminus, hsub⟩ :=
    local_edge_of_the_wedge_1d (-r) r (by linarith) gPlus 0 hgPlus
      (differentiableOn_const 0) htrace (fun _ _ _ => tendsto_const_nhds)
      (fun _ _ _ => by simp [gPlus]) (by
        intro a _ _
        simp only [gPlus, Complex.ofReal_im, ite_true]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp [hz])
  rw [hball] at hsub
  let w : ℂ := -((r / 2 : ℝ) : ℂ) * I
  have hwU : w ∈ U := by
    apply hsub
    simpa [Metric.mem_ball, dist_zero_right, w, norm_mul, abs_of_pos hr]
      using (half_lt_self hr)
  have hwlow : w ∈ EOW.LowerHalfPlane := by
    change w.im < 0
    simp [w]
    linarith
  have hfreq : ∃ᶠ z in nhdsWithin w {w}ᶜ, F z = (0 : ℂ → ℂ) z := by
    apply Filter.Eventually.frequently
    have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin w {w}ᶜ :=
      nhdsWithin_le_nhds ((hU.inter EOW.lowerHalfPlane_isOpen).mem_nhds ⟨hwU, hwlow⟩)
    filter_upwards [hmem] with z hz
    exact hFminus z hz
  intro z hz
  have hzU := hsub hz.1
  have hzero := identity_theorem_connected hU ⟨⟨w, hwU⟩, hUconv.isPreconnected⟩
    F 0 hF (differentiableOn_const 0) w hwU hfreq hzU
  have hmatch := hFplus z ⟨hzU, hz.2⟩
  simpa [gPlus, ne_of_gt (show 0 < z.im from hz.2)] using hmatch.symm.trans hzero

/-- Weak boundary zero on a fixed ray yields continuous zero boundary trace
after real mollification. The cutoff only needs to equal one on the kernels
appearing near the selected point of the complex line. -/
theorem tendsto_realMollifyLocal_line_zero_of_cutoff {m : ℕ}
    (F : (Fin m → ℂ) → ℂ) (Ω : Set (Fin m → ℂ))
    (χ ψ : SchwartzMap (Fin m → ℝ) ℂ) (x₀ η : Fin m → ℝ) (a : ℝ)
    (hΩ : IsOpen Ω) (hF : ContinuousOn F Ω)
    (hχ : HasCompactSupport (χ : (Fin m → ℝ) → ℂ))
    (hψ : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    {r : ℝ} (hr : 0 < r)
    (hmargin : ∀ ε ∈ Ioo (0 : ℝ) r,
      ∀ x ∈ tsupport (χ : (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((ε * η i : ℝ) : ℂ) * I) ∈ Ω)
    (hb : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
        F (fun i => (x i : ℂ) + ((ε * η i : ℝ) : ℂ) * I) * (χ x * φ x))
        (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hχ_one : ∀ᶠ w in nhdsWithin (a : ℂ) EOW.UpperHalfPlane,
      ∀ x ∈ tsupport ((translateSchwartz (-(x₀ + w.re • η)) ψ :
        SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ), χ x = 1) :
    Tendsto (fun w : ℂ => realMollifyLocal F ψ (fun i => (x₀ i : ℂ) + w * (η i : ℂ)))
      (nhdsWithin (a : ℂ) EOW.UpperHalfPlane) (nhds 0) := by
  classical
  have hex : ∀ ε ∈ Ioo (0 : ℝ) r,
      ∃ T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          T φ = ∫ x : Fin m → ℝ,
            (χ x * F (fun i => (x i : ℂ) + ((ε * η i : ℝ) : ℂ) * I)) * φ x := by
    intro ε hε
    exact exists_cutoffSliceIntegral_clm_of_continuousOn F χ Ω (ε • η)
      hΩ hF hχ (hmargin ε hε)
  let T : ℝ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ := fun ε =>
    if hε : ε ∈ Ioo (0 : ℝ) r then (hex ε hε).choose else 0
  have hT : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun ε => T ε φ) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    intro φ
    refine (hb φ).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hr)] with ε hε hεr
    have he : ε ∈ Ioo (0 : ℝ) r := ⟨hε, hεr⟩
    dsimp [T]
    rw [dif_pos he, (hex ε he).choose_spec]
    apply integral_congr_ae
    filter_upwards with x
    ring
  let l := nhdsWithin (a : ℂ) EOW.UpperHalfPlane
  have him : Tendsto (fun w : ℂ => w.im) l (nhdsWithin 0 (Ioi 0)) := by
    simpa [l] using
      Complex.continuous_im.continuousAt.continuousWithinAt.tendsto_nhdsWithin
        (show MapsTo Complex.im EOW.UpperHalfPlane (Ioi 0) from fun _ h => h)
  have hre : Tendsto (fun w : ℂ => -(x₀ + w.re • η)) l (nhds (-(x₀ + a • η))) := by
    have hc : Continuous (fun w : ℂ => -(x₀ + w.re • η)) :=
      (continuous_const.add (Complex.continuous_re.smul continuous_const)).neg
    simpa [l] using hc.continuousAt.tendsto.comp
      (tendsto_id'.2 nhdsWithin_le_nhds)
  have hz := SchwartzMap.tempered_apply_tendsto_zero_of_tendsto_filter
    (fun φ => (hT φ).comp him)
    ((tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ (-(x₀ + a • η))).comp hre)
  refine hz.congr' ?_
  have hsmall : ∀ᶠ w in l, w.im < r :=
    him.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hr))
  filter_upwards [self_mem_nhdsWithin, hsmall, hχ_one] with w hw hwr hχw
  have he : w.im ∈ Ioo (0 : ℝ) r := ⟨hw, hwr⟩
  let z : Fin m → ℂ := fun i => (x₀ i : ℂ) + w * (η i : ℂ)
  have hre_z : (fun i => -(z i).re) = -(x₀ + w.re • η) := by
    ext i
    simp [z]
  have hrepr : realMollifyLocal F ψ z =
      T w.im (translateSchwartz (fun i => -(z i).re) ψ) := by
    apply realMollifyLocal_eq_cutoffSliceCLM F χ ψ z (T w.im)
    · simpa [hre_z] using hχw
    · intro φ
      dsimp [T]
      rw [dif_pos he, (hex w.im he).choose_spec]
      simp [z, Complex.mul_im]
  simpa [hre_z, z] using hrepr.symm

set_option maxHeartbeats 1000000 in
/-- Local tube uniqueness from weak boundary zero on compact tests. Only
raywise boundary limits are required, with no uniform cone-direction bound. -/
theorem local_distributional_uniqueness_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C)
    (hcone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    (c : Fin m → ℝ) {R : ℝ} (hR : 0 < R)
    {F : (Fin m → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball (realEmbed c) R ∩ TubeDomain C))
    (hb : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
      tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ Metric.ball c R →
      ∀ η ∈ C,
        Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
          F (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ z ∈ Metric.ball (realEmbed c) (R / 8) ∩ TubeDomain C, F z = 0 := by
  let Ω := Metric.ball (realEmbed c) R ∩ TubeDomain C
  have hΩ : IsOpen Ω := Metric.isOpen_ball.inter (tubeDomain_isOpen hC)
  let β : ContDiffBump c := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  let χf : (Fin m → ℝ) → ℂ := fun x => (β x : ℂ)
  have hχc : HasCompactSupport χf := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let χ : SchwartzMap (Fin m → ℝ) ℂ := hχc.toSchwartzMap
    ((Complex.ofRealCLM.contDiff.of_le le_top).comp β.contDiff)
  have hχapply : ∀ x, χ x = (β x : ℂ) := fun _ => rfl
  have hχsupp : tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall c (3 * R / 4) := by
    have heq : Function.support (χ : (Fin m → ℝ) → ℂ) = Function.support β := by
      ext x
      simp [Function.mem_support, hχapply]
    change closure (Function.support (χ : (Fin m → ℝ) → ℂ)) ⊆ _
    rw [heq]
    change tsupport (β : (Fin m → ℝ) → ℝ) ⊆ _
    rw [β.tsupport_eq]
  have hχone : ∀ x, ‖x - c‖ ≤ R / 2 → χ x = 1 := by
    intro x hx
    rw [hχapply, β.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)]
    simp
  obtain ⟨ψn, hψnonneg, hψreal, hψnorm, hψsmall, hψsupp⟩ :=
    exists_shrinking_normalized_schwartz_bump_sequence (m := m) (by positivity : 0 < R / 8)
  have hψrate : ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)) := by
    intro n t ht
    exact Metric.closedBall_subset_closedBall (min_le_right _ _) (hψsmall n ht)
  intro z hz
  let x₀ : Fin m → ℝ := fun i => (z i).re
  let η : Fin m → ℝ := fun i => (z i).im
  have hx : ‖x₀ - c‖ < R / 8 := by
    have h := (norm_complexChart_re_le (z - realEmbed c)).trans_lt
      (by simpa [Metric.mem_ball, dist_eq_norm] using hz.1)
    simpa [x₀, realEmbed] using h
  have hη : ‖η‖ < R / 8 := by
    have h := (norm_complexChart_im_le (z - realEmbed c)).trans_lt
      (by simpa [Metric.mem_ball, dist_eq_norm] using hz.1)
    simpa [η, realEmbed] using h
  have hηC : η ∈ C := hz.2
  let line : ℂ → (Fin m → ℂ) := fun w i => (x₀ i : ℂ) + w * (η i : ℂ)
  have hlineI : line I = z := by
    ext i
    apply Complex.ext <;> simp [line, x₀, η]
  have hline_diff : Differentiable ℂ line := by
    intro w
    exact differentiableAt_pi.mpr fun i =>
      (differentiableAt_const _).add (differentiableAt_id.mul (differentiableAt_const _))
  have hline_norm : ∀ w, ‖line w - realEmbed c‖ ≤ ‖x₀ - c‖ + ‖w‖ * ‖η‖ := by
    intro w
    have heq : line w - realEmbed c = realEmbed (x₀ - c) + w • realEmbed η := by
      ext i
      simp [line, realEmbed]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (by simp [norm_smul, norm_realEmbed_eq])
  have hmollzero : ∀ n, realMollifyLocal F (ψn n) z = 0 := by
    intro n
    let D := Metric.ball (realEmbed c) (R / 2) ∩ TubeDomain C
    have hD : IsOpen D := Metric.isOpen_ball.inter (tubeDomain_isOpen hC)
    have hψc := KernelSupportWithin_hasCompactSupport (hψsupp n)
    have hM : DifferentiableOn ℂ (realMollifyLocal F (ψn n)) D := by
      apply localRealMollifySide_holomorphicOn_of_translate_margin F (ψn n) Ω D hΩ hD hF hψc
      intro w hw t ht
      constructor
      · have hn : ‖t‖ ≤ R / 8 := by simpa using hψsupp n ht
        rw [Metric.mem_ball, dist_eq_norm]
        calc
          ‖w + realEmbed t - realEmbed c‖ = ‖(w - realEmbed c) + realEmbed t‖ := by congr 1; abel
          _ ≤ ‖w - realEmbed c‖ + ‖t‖ := by simpa [norm_realEmbed_eq] using norm_add_le (w - realEmbed c) (realEmbed t)
          _ < R := by
            have hw' : ‖w - realEmbed c‖ < R / 2 := by
              simpa [Metric.mem_ball, dist_eq_norm] using hw.1
            linarith
      · simpa [TubeDomain, realEmbed] using hw.2
    have hlineD : MapsTo line (Metric.ball 0 2 ∩ EOW.UpperHalfPlane) D := by
      intro w hw
      constructor
      · have hw' : ‖w‖ < 2 := by simpa using hw.1
        have hp : ‖w‖ * ‖η‖ ≤ 2 * ‖η‖ := mul_le_mul_of_nonneg_right hw'.le (norm_nonneg _)
        rw [Metric.mem_ball, dist_eq_norm]
        exact (hline_norm w).trans_lt (by linarith)
      · change (fun i => (line w i).im) ∈ C
        have heq : (fun i => (line w i).im) = w.im • η := by ext i; simp [line]
        rw [heq]
        exact hcone w.im hw.2 η hηC
    have hg : DifferentiableOn ℂ (fun w => realMollifyLocal F (ψn n) (line w))
        (Metric.ball 0 2 ∩ EOW.UpperHalfPlane) := hM.comp hline_diff.differentiableOn hlineD
    have htrace : ∀ a : ℝ, |a| < 2 →
        Tendsto (fun w => realMollifyLocal F (ψn n) (line w))
          (nhdsWithin (a : ℂ) EOW.UpperHalfPlane) (nhds 0) := by
      intro a ha
      apply tendsto_realMollifyLocal_line_zero_of_cutoff F Ω χ (ψn n) x₀ η a
        hΩ hF.continuousOn hχc hψc (r := 1) zero_lt_one
      · intro ε hε x hxs
        constructor
        · have hxχ : ‖x - c‖ ≤ 3 * R / 4 := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hχsupp hxs
          have heq : (fun i => (x i : ℂ) + ((ε * η i : ℝ) : ℂ) * I) - realEmbed c =
              realEmbed (x - c) + (ε : ℂ) • I • realEmbed η := by
                ext i
                simp only [realEmbed, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
                  Complex.ofReal_mul, Complex.ofReal_sub, smul_eq_mul]
                ring
          rw [Metric.mem_ball, dist_eq_norm]
          rw [heq]
          calc
            ‖realEmbed (x - c) + (ε : ℂ) • I • realEmbed η‖
                ≤ ‖x - c‖ + ε * ‖η‖ := by
                  simpa [norm_smul, norm_realEmbed_eq, abs_of_pos hε.1] using
                    norm_add_le (realEmbed (x - c)) ((ε : ℂ) • I • realEmbed η)
            _ < R := by
              have := mul_le_mul_of_nonneg_right hε.2.le (norm_nonneg η)
              linarith
        · change (fun i => ((x i : ℂ) + ((ε * η i : ℝ) : ℂ) * I).im) ∈ C
          simpa using hcone ε hε.1 η hηC
      · intro φ
        let φχ := SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) φ
        have heq : (φχ : (Fin m → ℝ) → ℂ) = fun x => χ x * φ x := by
          ext x
          simp [φχ, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
        have hcomp : HasCompactSupport (φχ : (Fin m → ℝ) → ℂ) := by
          rw [heq]
          exact hχc.mul_right
        have hsupp : tsupport (φχ : (Fin m → ℝ) → ℂ) ⊆ Metric.ball c R := by
          rw [heq]
          intro x hx'
          have hbound := hχsupp (tsupport_mul_subset_left hx')
          exact lt_of_le_of_lt (Metric.mem_closedBall.mp hbound) (by linarith)
        simpa only [heq, Complex.ofReal_mul] using hb φχ hcomp hsupp η hηC
      · have hn : Metric.ball (0 : ℂ) 2 ∈ nhdsWithin (a : ℂ) EOW.UpperHalfPlane :=
          nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (by simpa using ha))
        filter_upwards [hn] with w hw
        intro x hxt
        have hpre : x - (x₀ + w.re • η) ∈ Metric.closedBall (0 : Fin m → ℝ) (R / 8) := by
          have hs : tsupport ((translateSchwartz (-(x₀ + w.re • η)) (ψn n) :
              SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) ⊆
              {x | x - (x₀ + w.re • η) ∈ Metric.closedBall 0 (R / 8)} := by
            apply closure_minimal
            · intro t ht
              exact hψsupp n (subset_tsupport _ ((mem_support_translateSchwartz_iff _ _ _).mp ht))
            · exact Metric.isClosed_closedBall.preimage (continuous_id.sub continuous_const)
          exact hs hxt
        apply hχone
        have hnorm : ‖x - (x₀ + w.re • η)‖ ≤ R / 8 := by simpa using hpre
        have hw' : |w.re| ≤ 2 := (Complex.abs_re_le_norm w).trans
          (le_of_lt (by simpa using hw))
        calc
          ‖x - c‖ = ‖(x - (x₀ + w.re • η)) + (x₀ - c) + w.re • η‖ := by congr 1; module
          _ ≤ ‖x - (x₀ + w.re • η)‖ + ‖x₀ - c‖ + ‖w.re • η‖ := by
            calc
              _ ≤ ‖x - (x₀ + w.re • η) + (x₀ - c)‖ + ‖w.re • η‖ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
          _ ≤ R / 2 := by
            rw [norm_smul, Real.norm_eq_abs]
            have := mul_le_mul_of_nonneg_right hw' (norm_nonneg η)
            linarith
    have hz0 := local_uniqueness_of_boundary_zero (by norm_num : (0 : ℝ) < 2) hg htrace
      I (by simp [EOW.UpperHalfPlane])
    simpa [hlineI] using hz0
  have ht := regularizedEnvelope_kernelLimit_from_representation Ω Ω F
    (realMollifyLocal F) ψn hΩ Subset.rfl hF.continuousOn
    (by intro n w hw; rfl) hψnonneg hψreal hψnorm hψrate z
    ⟨Metric.ball_subset_ball (by linarith) hz.1, hz.2⟩
  exact tendsto_nhds_unique ht (by simpa only [hmollzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)))

/-- Real mollification is continuous at the edge whenever the entire compact
real support lies in the open continuity domain. -/
theorem continuousAt_realMollifyLocal_of_real_support {m : ℕ}
    (G : (Fin m → ℂ) → ℂ) (Ω : Set (Fin m → ℂ))
    (hΩ : IsOpen Ω) (hG : ContinuousOn G Ω)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hs : ∀ x ∈ tsupport (ψ : (Fin m → ℝ) → ℂ), realEmbed x ∈ Ω) :
    ContinuousAt (realMollifyLocal G ψ) 0 := by
  let U : Set (Fin m → ℂ) := {z | ∀ x ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
    z + realEmbed x ∈ Ω}
  have hU : U ∈ nhds 0 := by
    apply hψ.isCompact.eventually_forall_of_forall_eventually
    intro x hx
    have hc : Continuous (fun p : (Fin m → ℂ) × (Fin m → ℝ) => p.1 + realEmbed p.2) :=
      continuous_fst.add (continuous_realEmbed.comp continuous_snd)
    exact hc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds (by simpa using hs x hx))
  exact (continuousOn_realMollifyLocal_of_translate_margin G ψ U Ω hΩ hG hψ
    (fun _ hz => hz) 0 (mem_of_mem_nhds hU)).continuousAt hU

set_option maxHeartbeats 1000000 in
/-- A tube-side branch with the boundary pairings of a branch holomorphic
across the edge equals that branch on a smaller tube neighborhood. -/
theorem local_eq_of_distributional_boundary_pairing {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C)
    (hcone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    (c : Fin m → ℝ) {R : ℝ} (hR : 0 < R)
    {F G : (Fin m → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball (realEmbed c) R ∩ TubeDomain C))
    (hG : DifferentiableOn ℂ G (Metric.ball (realEmbed c) R))
    (hb : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
      tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ Metric.ball c R →
      ∀ η ∈ C,
        Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
          F (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds (∫ x, G (realEmbed x) * φ x))) :
    ∀ z ∈ Metric.ball (realEmbed c) (R / 8) ∩ TubeDomain C, F z = G z := by
  have hzero := local_distributional_uniqueness_tube hC hcone c hR
    (hF.sub (hG.mono inter_subset_left))
  suffices hboundary : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
      tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ Metric.ball c R →
      ∀ η ∈ C,
        Tendsto (fun ε : ℝ => ∫ x : Fin m → ℝ,
          (F (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) -
            G (fun i => (x i : ℂ) + ε * (η i : ℂ) * I)) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) from
    fun z hz => sub_eq_zero.mp (hzero hboundary z hz)
  intro φ hφ hs η hη
  let shift : ℝ → (Fin m → ℂ) := fun ε i => (ε : ℂ) * (η i : ℂ) * I
  have hshift : Continuous shift := continuous_pi fun _ => by fun_prop
  have hshift0 : shift 0 = 0 := by ext i; simp [shift]
  have harg : ∀ ε x, shift ε + realEmbed x =
      (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) := by
    intro ε x
    ext i
    simp [shift, realEmbed, add_comm]
  have hsr : ∀ x ∈ tsupport (φ : (Fin m → ℝ) → ℂ),
      realEmbed x ∈ Metric.ball (realEmbed c) R := by
    intro x hx
    have heq : realEmbed x - realEmbed c = realEmbed (x - c) := by ext i; simp [realEmbed]
    simpa [Metric.mem_ball, dist_eq_norm, heq, norm_realEmbed_eq] using hs hx
  have hGc := continuousAt_realMollifyLocal_of_real_support G _ Metric.isOpen_ball
    hG.continuousOn φ hφ hsr
  have hGb : Tendsto (fun ε => ∫ x, G (shift ε + realEmbed x) * φ x)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ x, G (realEmbed x) * φ x)) := by
    have h := hGc.tendsto.comp
      ((by simpa [hshift0] using (hshift.continuousAt (x := 0)).tendsto) : Tendsto shift (nhds 0) (nhds 0))
    simpa [realMollifyLocal] using h.mono_left nhdsWithin_le_nhds
  have hFb : Tendsto (fun ε => ∫ x, F (shift ε + realEmbed x) * φ x)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ x, G (realEmbed x) * φ x)) := by
    simpa only [harg] using hb φ hφ hs η hη
  have hsmall : ∀ᶠ ε in nhds (0 : ℝ),
      ∀ x ∈ tsupport (φ : (Fin m → ℝ) → ℂ),
        shift ε + realEmbed x ∈ Metric.ball (realEmbed c) R := by
    apply hφ.isCompact.eventually_forall_of_forall_eventually
    intro x hx
    have hc : Continuous (fun p : ℝ × (Fin m → ℝ) => shift p.1 + realEmbed p.2) :=
      (hshift.comp continuous_fst).add (continuous_realEmbed.comp continuous_snd)
    exact hc.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [hshift0] using hsr x hx))
  have hlim := hFb.sub hGb
  simp only [sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hsmall] with ε hε hεs
  have hI_F := integrable_realMollifyLocal_integrand_of_translate_margin F φ
    (Metric.ball (realEmbed c) R ∩ TubeDomain C) (shift ε)
    (Metric.isOpen_ball.inter (tubeDomain_isOpen hC)) hF hφ (by
      intro x hx
      refine ⟨hεs x hx, ?_⟩
      change (fun i => (shift ε i + (x i : ℂ)).im) ∈ C
      simpa [shift] using hcone ε hε η hη)
  have hI_G := integrable_realMollifyLocal_integrand_of_translate_margin G φ
    (Metric.ball (realEmbed c) R) (shift ε) Metric.isOpen_ball hG hφ hεs
  rw [← integral_sub hI_F hI_G]
  apply integral_congr_ae
  filter_upwards with x
  rw [harg]
  ring

end SCV
