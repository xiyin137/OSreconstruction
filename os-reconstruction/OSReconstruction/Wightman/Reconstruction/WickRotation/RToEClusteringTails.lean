import OSReconstruction.GeneralResults.SchwartzWeightedFlatness
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerTemperedness

/-!
# Uniform Schwartz-tail control for R-to-E clustering

The translated-product witnesses are the literal ones in E4. Their flatness
controls translated cross-block coincidence sets, with a single integrable
envelope chosen before the translation. The actual Euclidean kernel growth
then gives uniform smallness of the far-tail integral. No compact support,
ordered-source hypothesis, or extra kernel-growth premise is imposed on the
actual-kernel results.

The coincidence-distance argument applies when the joint coincidence locus
is nonempty; the zero/one-point cases remain separate. Clustering on the
complementary relatively separated region is a distinct obligation.
-/

noncomputable section

namespace OSReconstruction

/-- E4 admissibility gives a fixed integrable envelope for a distance-weighted
polynomial kernel bound, independently of translation and witness choice. -/
theorem rToE_block_kernel_integrable_majorant
    {d n k : ℕ} (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d k)
    (m q : ℕ) (hcoin : (CoincidenceLocus d (n + k)).Nonempty) :
    ∃ B : NPointDomain d (n + k) → ℝ,
      MeasureTheory.Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ a : SpacetimeDim d,
        ∀ (g_a : ZeroDiagonalSchwartz d k),
          (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + k)),
            (∀ x, fg_a.1 x = f.1 (splitFirst n k x) * g_a.1 (splitLast n k x)) →
            ∀ x (b A : ℝ), 0 ≤ b →
              b * Metric.infDist
                (x + Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a))
                (CoincidenceLocus d (n + k)) ^ (m + 1) ≤ A * (1 + ‖x‖) ^ q →
              b * ‖(f.1.tensorProduct g.1) x‖ ≤ A * B x := by
  obtain ⟨B, hBi, hBpos, hB⟩ :=
    SchwartzFlatness.schwartz_polynomial_kernel_integrable_majorant_uniform_pi
      (f.1.tensorProduct g.1) m q
  refine ⟨B, hBi, hBpos, ?_⟩
  intro a g_a hga fg_a hfg
  let c : NPointDomain d (n + k) :=
    Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a)
  let S : Set (NPointDomain d (n + k)) :=
    {x | x + c ∈ CoincidenceLocus d (n + k)}
  have hSc : IsClosed S := isClosed_CoincidenceLocus.preimage
    (continuous_id.add continuous_const)
  have hSn : S.Nonempty := by
    obtain ⟨y, hy⟩ := hcoin
    exact ⟨y - c, by simpa [S] using hy⟩
  have hfun : (f.1.tensorProduct g.1 : NPointDomain d (n + k) → ℂ) =
      fun x => fg_a.1 (x + c) := by
    funext x
    rw [SchwartzMap.tensorProduct_apply, hfg, hga]
    congr 1
    · congr 1
      ext i j
      simp [splitFirst, c]
    · congr 1
      ext i j
      simp [splitLast, c]
  have hflat : ∀ l : ℕ, ∀ y ∈ S,
      iteratedFDeriv ℝ l (f.1.tensorProduct g.1 : NPointDomain d (n + k) → ℂ) y = 0 := by
    intro l y hy
    rw [hfun, iteratedFDeriv_comp_add_right]
    exact fg_a.property l (y + c) hy
  have himage : (fun x => x + c) '' S = CoincidenceLocus d (n + k) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨y - c, by simpa [S] using hy, sub_add_cancel _ _⟩
  have hdist (x : NPointDomain d (n + k)) :
      Metric.infDist x S = Metric.infDist (x + c) (CoincidenceLocus d (n + k)) := by
    have hiso : Isometry (fun x : NPointDomain d (n + k) => x + c) :=
      Isometry.of_dist_eq fun x y => dist_add_right x y c
    simpa only [himage] using (Metric.infDist_image (t := S) (x := x) hiso).symm
  intro x b A hb hgrowth
  exact hB S hSc hSn hflat x b A hb (by simpa only [hdist, c] using hgrowth)

/-- On the far tail, polynomial translation growth is absorbed by the original
Schwartz decay. The envelope remains independent of translation. -/
theorem rToE_block_kernel_tail_majorant
    {d n k : ℕ} (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d k)
    (m q : ℕ) (hcoin : (CoincidenceLocus d (n + k)).Nonempty)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ B : NPointDomain d (n + k) → ℝ,
      MeasureTheory.Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ a : SpacetimeDim d,
        ∀ (g_a : ZeroDiagonalSchwartz d k),
          (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + k)),
            (∀ x, fg_a.1 x = f.1 (splitFirst n k x) * g_a.1 (splitLast n k x)) →
            ∀ x (b A : ℝ), 0 ≤ b → 0 ≤ A → ‖a‖ ≤ L * (1 + ‖x‖) →
              b * Metric.infDist
                (x + Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a))
                (CoincidenceLocus d (n + k)) ^ (m + 1) ≤
                  A * (1 + ‖x‖ + ‖a‖) ^ q →
              b * ‖(f.1.tensorProduct g.1) x‖ ≤ A * B x := by
  obtain ⟨B, hBi, hBpos, hB⟩ := rToE_block_kernel_integrable_majorant f g m q hcoin
  refine ⟨fun x => (1 + L) ^ q * B x, hBi.const_mul _,
    fun x => mul_nonneg (by positivity) (hBpos x), ?_⟩
  intro a g_a hga fg_a hfg x b A hb hA htail hgrowth
  have hgrowth' : b * Metric.infDist
      (x + Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a))
      (CoincidenceLocus d (n + k)) ^ (m + 1) ≤ (A * (1 + L) ^ q) * (1 + ‖x‖) ^ q := by
    calc
      _ ≤ A * (1 + ‖x‖ + ‖a‖) ^ q := hgrowth
      _ ≤ A * ((1 + L) * (1 + ‖x‖)) ^ q := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
      _ = _ := by rw [mul_pow]; ring
  simpa only [mul_assoc] using hB a g_a hga fg_a hfg x b (A * (1 + L) ^ q) hb hgrowth'

/-- The actual Euclidean kernel has a translation-uniform integrable majorant
on the far tail, using only the original Wightman assumptions. -/
theorem rToE_wick_kernel_block_tail_majorant
    {d n k : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d k)
    (hcoin : (CoincidenceLocus d (n + k)).Nonempty) (L : ℝ) (hL : 0 ≤ L) :
    ∃ B : NPointDomain d (n + k) → ℝ,
      MeasureTheory.Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ a : SpacetimeDim d,
        ∀ (g_a : ZeroDiagonalSchwartz d k),
          (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + k)),
            (∀ x, fg_a.1 x = f.1 (splitFirst n k x) * g_a.1 (splitLast n k x)) →
            ∀ᵐ x ∂MeasureTheory.volume, ‖a‖ ≤ L * (1 + ‖x‖) →
              ‖F_ext_on_translatedPET_total Wfn
                  (fun i => wickRotatePoint
                    ((x + Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a)) i)) *
                (f.1.tensorProduct g.1) x‖ ≤ B x := by
  obtain ⟨C, N, m, hC, hK⟩ := wick_rotated_kernel_ae_polynomial_growth (n := n + k) Wfn
  obtain ⟨B, hBi, hBpos, hB⟩ := rToE_block_kernel_tail_majorant f g m N hcoin L hL
  refine ⟨fun x => C * B x, hBi.const_mul _,
    fun x => mul_nonneg hC.le (hBpos x), ?_⟩
  intro a g_a hga fg_a hfg
  let c : NPointDomain d (n + k) :=
    Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a)
  have hc : ‖c‖ ≤ ‖a‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [c]
    · simp [c]
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d (n + k))) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have hshift := (MeasureTheory.measurePreserving_add_right
    (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d (n + k))) c).quasiMeasurePreserving.ae hK
  filter_upwards [hshift] with x hx
  intro htail
  rw [norm_mul]
  apply hB a g_a hga fg_a hfg x _ C (norm_nonneg _) hC.le htail
  calc
    _ ≤ C * (1 + ‖x + c‖) ^ N := hx
    _ ≤ C * (1 + ‖x‖ + ‖a‖) ^ N := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply pow_le_pow_left₀ (by positivity)
      linarith [norm_add_le x c]

open scoped Topology in
open MeasureTheory Filter in
/-- The absolute integral of the actual translated block kernel over the far
tail tends uniformly to zero for all admissible E4 product witnesses. -/
theorem rToE_wick_kernel_block_tail_small
    {d n k : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d k)
    (hcoin : (CoincidenceLocus d (n + k)).Nonempty) (L : ℝ) (hL : 0 ≤ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : SpacetimeDim d, R < ‖a‖ →
      ∀ (g_a : ZeroDiagonalSchwartz d k),
        (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
        ∀ (fg_a : ZeroDiagonalSchwartz d (n + k)),
          (∀ x, fg_a.1 x = f.1 (splitFirst n k x) * g_a.1 (splitLast n k x)) →
          (∫ x in {x : NPointDomain d (n + k) | ‖a‖ ≤ L * (1 + ‖x‖)},
            ‖F_ext_on_translatedPET_total Wfn
                (fun i => wickRotatePoint
                  ((x + Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a)) i)) *
              (f.1.tensorProduct g.1) x‖) < ε := by
  obtain ⟨B, hBi, hBpos, hB⟩ := rToE_wick_kernel_block_tail_majorant Wfn f g hcoin L hL
  let s (r : ℝ) : Set (NPointDomain d (n + k)) := {x | r ≤ L * (1 + ‖x‖)}
  have hs (r : ℝ) : MeasurableSet (s r) :=
    (isClosed_le continuous_const
      (continuous_const.mul (continuous_const.add continuous_norm))).measurableSet
  have hinter : (⋂ r : ℝ, s r) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := Set.mem_iInter.mp hx (1 + L * (1 + ‖x‖))
    change 1 + L * (1 + ‖x‖) ≤ L * (1 + ‖x‖) at h
    linarith
  have hlim := tendsto_setIntegral_of_antitone hs
    (show Antitone s from fun r t h x hx => le_trans h hx)
    (show ∃ r, IntegrableOn B (s r) from ⟨0, hBi.integrableOn⟩)
  simp only [hinter, Measure.restrict_empty, integral_zero_measure] at hlim
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max 1 R₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro a ha g_a hga fg_a hfg
  let c : NPointDomain d (n + k) :=
    Fin.append (fun _ : Fin n => 0) (fun _ : Fin k => a)
  let J : NPointDomain d (n + k) → ℂ := fun x =>
    F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint ((x + c) i)) *
      (f.1.tensorProduct g.1) x
  haveI : Measure.IsAddHaarMeasure (volume : Measure (NPointDomain d (n + k))) :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have hJmeas : AEStronglyMeasurable J volume :=
    ((bhw_euclidean_kernel_measurable Wfn).comp_quasiMeasurePreserving
      (measurePreserving_add_right volume c).quasiMeasurePreserving).mul
      (f.1.tensorProduct g.1).continuous.aestronglyMeasurable
  have hJbound : ∀ᵐ x ∂volume.restrict (s ‖a‖), ‖J x‖ ≤ B x :=
    (ae_restrict_iff' (hs ‖a‖)).2 (hB a g_a hga fg_a hfg)
  have hJi : IntegrableOn J (s ‖a‖) :=
    hBi.integrableOn.mono' hJmeas.restrict hJbound
  exact lt_of_le_of_lt
    (integral_mono_ae hJi.norm hBi.integrableOn hJbound)
    (hR₀ ‖a‖ ((le_max_right _ _).trans ha.le))

end OSReconstruction
