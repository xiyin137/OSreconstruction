import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEPointBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToETimeClustering

/-!
# Reflected Point Clustering Uniform in Time

The reflected Cauchy property of shrinking normalized sources and the
time-space source bound make their point approximation uniform over all
nonnegative times and spatial translations. One sufficiently late pair of
sources then transfers the proved uniform-time cluster theorem to fixed
ordered point configurations. The same source estimate controls nearby point
configurations, so a finite compact cover gives compact-family uniformity.

Rotated separation and arbitrary-test E4 remain separate obligations.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace OSReconstruction
variable {d : ℕ} [NeZero d]

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

private def spaceShift {n : ℕ} (a : Fin d → ℝ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨translateSchwartzNPoint (Fin.cons 0 a) f.1,
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (Fin.cons 0 a) (by simp) f.1 f.2⟩

private def timeSpacePair (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (a : Fin d → ℝ) : ℂ :=
  rToEReflectedPairing Wfn (osiiOriginalOSNonnegativeTimeShiftSource f s)
    (spaceShift a (osiiOriginalOSNonnegativeTimeShiftSource g t))

private theorem timeSpacePair_apply (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (a : Fin d → ℝ) :
    timeSpacePair Wfn f g s t a = wickRotatedBoundaryPairing Wfn (n + m)
      ((timeShiftSchwartzNPoint s f.1).osConjTensorProduct
        (translateSchwartzNPoint (Fin.cons 0 a) (timeShiftSchwartzNPoint t g.1))) := rfl

attribute [local irreducible] rToEReflectedPairing

private theorem timeSpacePair_sub_left (Wfn : WightmanFunctions d) {n m : ℕ}
    (f f' : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (a : Fin d → ℝ) :
    timeSpacePair Wfn (f - f') g s t a =
      timeSpacePair Wfn f g s t a - timeSpacePair Wfn f' g s t a := by
  have hsub : osiiOriginalOSNonnegativeTimeShiftSource (f - f') s =
      osiiOriginalOSNonnegativeTimeShiftSource f s -
        osiiOriginalOSNonnegativeTimeShiftSource f' s := by
    apply Subtype.ext
    exact map_sub (timeShiftSchwartzNPoint (d := d) s) f.1 f'.1
  simp only [timeSpacePair, hsub, rToEReflectedPairing_sub_left]

private theorem timeSpacePair_sub_right (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g g' : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (a : Fin d → ℝ) :
    timeSpacePair Wfn f (g - g') s t a =
      timeSpacePair Wfn f g s t a - timeSpacePair Wfn f g' s t a := by
  have hsub : spaceShift a (osiiOriginalOSNonnegativeTimeShiftSource (g - g') t) =
      spaceShift a (osiiOriginalOSNonnegativeTimeShiftSource g t) -
        spaceShift a (osiiOriginalOSNonnegativeTimeShiftSource g' t) := by
    apply Subtype.ext
    change translateSchwartzNPoint (Fin.cons 0 a) (timeShiftSchwartzNPoint t (g.1 - g'.1)) = _
    rw [map_sub, map_sub]
    rfl
  simp only [timeSpacePair, hsub, rToEReflectedPairing_sub_right]

private theorem timeSpacePair_bound (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (a : Fin d → ℝ) :
    ‖timeSpacePair Wfn f g s t a‖ ^ 2 ≤
      ‖rToEReflectedPairing Wfn f f‖ * ‖rToEReflectedPairing Wfn g g‖ := by
  rw [timeSpacePair_apply]
  exact rToE_reflected_timeSpaceShift_pairing_bound Wfn f g s t s.2 t.2 a

private theorem timeSpacePair_uniform_error (Wfn : WightmanFunctions d) (n m : ℕ)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (f f' : euclideanPositiveTimeSubmodule (d := d) n)
        (g g' : euclideanPositiveTimeSubmodule (d := d) m),
        ‖rToEReflectedPairing Wfn g g‖ ≤ C →
        ‖rToEReflectedPairing Wfn f' f'‖ ≤ C →
        ‖rToEReflectedPairing Wfn (f - f') (f - f')‖ < δ →
        ‖rToEReflectedPairing Wfn (g - g') (g - g')‖ < δ →
        ∀ (s t : ℝ≥0) (a : Fin d → ℝ),
          ‖timeSpacePair Wfn f g s t a - timeSpacePair Wfn f' g' s t a‖ < ε := by
  let δ := (ε / 2) ^ 2 / C
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (by linarith)) hC
  have hδC : δ * C = (ε / 2) ^ 2 := div_mul_cancel₀ _ (ne_of_gt hC)
  refine ⟨δ, hδ, fun f f' g g' hg hf' hdf hdg s t a => ?_⟩
  let L := timeSpacePair Wfn (f - f') g s t a
  let H := timeSpacePair Wfn f' (g - g') s t a
  have hL := timeSpacePair_bound Wfn (f - f') g s t a
  have hH := timeSpacePair_bound Wfn f' (g - g') s t a
  have hsmall (x b : ℝ) (hx0 : 0 ≤ x) (hx : x < δ) (hb : b ≤ C) :
      x * b < (ε / 2) ^ 2 := by
    calc
      x * b ≤ x * C := mul_le_mul_of_nonneg_left hb hx0
      _ < δ * C := mul_lt_mul_of_pos_right hx hC
      _ = _ := hδC
  have hLp := hsmall _ _ (norm_nonneg _) hdf hg
  have hHp := hsmall _ _ (norm_nonneg _) hdg hf'
  have hLn : ‖L‖ < ε / 2 := by
    change ‖L‖ ^ 2 ≤ _ at hL
    nlinarith [norm_nonneg L]
  have hHn : ‖H‖ < ε / 2 := by
    change ‖H‖ ^ 2 ≤ _ at hH
    nlinarith [norm_nonneg H]
  have heq : timeSpacePair Wfn f g s t a - timeSpacePair Wfn f' g' s t a = L + H := by
    dsimp only [L, H]
    rw [timeSpacePair_sub_left, timeSpacePair_sub_right]
    ring
  rw [heq]
  exact (norm_add_le L H).trans_lt (by linarith)

/-- One approximation index works for every nonnegative time and spatial shift. -/
theorem rToE_translated_reflected_pairing_uniform_point_approximation
    {n m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m)
    (f : ℕ → euclideanPositiveTimeSubmodule (d := d) n)
    (g : ℕ → euclideanPositiveTimeSubmodule (d := d) m)
    (hfn : ∀ i z, 0 ≤ ((f i).1 z).re) (hgn : ∀ i z, 0 ≤ ((g i).1 z).re)
    (hfr : ∀ i z, ((f i).1 z).im = 0) (hgr : ∀ i z, ((g i).1 z).im = 0)
    (hfi : ∀ i, ∫ z, (f i).1 z = 1) (hgi : ∀ i, ∫ z, (g i).1 z = 1)
    (hfs : ∀ δ > 0, ∀ᶠ i in atTop,
      Function.support ((f i).1 : NPointDomain d n → ℂ) ⊆ Metric.ball x δ)
    (hgs : ∀ δ > 0, ∀ᶠ i in atTop,
      Function.support ((g i).1 : NPointDomain d m → ℂ) ⊆ Metric.ball y δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i ≥ N, ∀ (s t : ℝ≥0) (a : Fin d → ℝ),
      ‖wickRotatedBoundaryPairing Wfn (n + m)
        ((timeShiftSchwartzNPoint s (f i).1).osConjTensorProduct
          (translateSchwartzNPoint (Fin.cons 0 a) (timeShiftSchwartzNPoint t (g i).1))) -
        F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (Fin.append
          (timeReflectionN d (x + fun _ => timeShiftVec d s))
          ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) j))‖ < ε := by
  let X := F_ext_on_translatedPET_total Wfn
    (fun j => wickRotatePoint (Fin.append (timeReflectionN d x) x j))
  let Y := F_ext_on_translatedPET_total Wfn
    (fun j => wickRotatePoint (Fin.append (timeReflectionN d y) y j))
  let C := ‖X‖ + ‖Y‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨δ, hδ, herr⟩ := timeSpacePair_uniform_error Wfn n m C hC (ε / 2) (by positivity)
  have hff := rToE_reflected_pairing_point_limit atTop Wfn x x hx hx f f
    hfn hfn hfr hfr hfi hfi hfs hfs
  have hgg := rToE_reflected_pairing_point_limit atTop Wfn y y hy hy g g
    hgn hgn hgr hgr hgi hgi hgs hgs
  have hbf : ∀ᶠ i in atTop, ‖rToEReflectedPairing Wfn (f i) (f i)‖ < C :=
    hff.norm.eventually (gt_mem_nhds (by dsimp [C, X]; linarith [norm_nonneg Y]))
  have hbg : ∀ᶠ i in atTop, ‖rToEReflectedPairing Wfn (g i) (g i)‖ < C :=
    hgg.norm.eventually (gt_mem_nhds (by dsimp [C, Y]; linarith [norm_nonneg X]))
  have hdf := (rToE_reflected_point_sources_cauchy Wfn x hx f hfn hfr hfi hfs).eventually
    (gt_mem_nhds hδ)
  have hdg := (rToE_reflected_point_sources_cauchy Wfn y hy g hgn hgr hgi hgs).eventually
    (gt_mem_nhds hδ)
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have htail : ∀ᶠ p : ℕ × ℕ in atTop, ∀ (s t : ℝ≥0) (a : Fin d → ℝ),
      ‖timeSpacePair Wfn (f p.1) (g p.1) s t a -
        timeSpacePair Wfn (f p.2) (g p.2) s t a‖ < ε / 2 := by
    filter_upwards [hdf, hdg, hfst.eventually hbg, hsnd.eventually hbf] with p hf hg hg0 hf0
    exact herr (f p.1) (f p.2) (g p.1) (g p.2) hg0.le hf0.le hf hg
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  refine ⟨max N.1 N.2, fun i hi s t a => ?_⟩
  have hlim := rToE_translated_reflected_pairing_point_limit atTop Wfn x y hx hy f g
    hfn hgn hfr hgr hfi hgi hfs hgs s t s.2 t.2 a
  have hdist := ((tendsto_const_nhds (x := timeSpacePair Wfn (f i) (g i) s t a)).sub hlim).norm
  have hle := le_of_tendsto hdist (show ∀ᶠ j : ℕ in atTop,
      ‖timeSpacePair Wfn (f i) (g i) s t a - wickRotatedBoundaryPairing Wfn (n + m)
        ((timeShiftSchwartzNPoint s (f j).1).osConjTensorProduct
          (translateSchwartzNPoint (Fin.cons 0 a) (timeShiftSchwartzNPoint t (g j).1)))‖ ≤ ε / 2 from by
    filter_upwards [eventually_ge_atTop (max N.1 N.2)] with j hj
    simpa only [timeSpacePair_apply] using
      (hN (i,j) ⟨(le_max_left _ _).trans hi, (le_max_right _ _).trans hj⟩ s t a).le)
  rw [timeSpacePair_apply] at hle
  exact hle.trans_lt (by linarith)

/-- Fixed ordered point kernels cluster with one radius for every nonnegative time pair. -/
theorem rToE_reflected_point_kernel_cluster_uniform_time
    {n m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ∀ a : Fin d → ℝ, (∑ j, (a j)^2) > R^2 →
        ‖F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (Fin.append
          (timeReflectionN d (x + fun _ => timeShiftVec d s))
          ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) j)) -
          starRingEnd ℂ (F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (x j))) *
            F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (y j))‖ < ε := by
  obtain ⟨f, hfn, hfr, hfi, _, hfs⟩ := exists_normalized_ordered_point_sequence x hx
  obtain ⟨g, hgn, hgr, hgi, _, hgs⟩ := exists_normalized_ordered_point_sequence y hy
  obtain ⟨N, hN⟩ := rToE_translated_reflected_pairing_uniform_point_approximation
    Wfn x y hx hy f g hfn hgn hfr hgr hfi hgi hfs hgs (ε / 3) (by positivity)
  have hf := rToE_ordered_wick_pairing_point_limit atTop Wfn x hx f hfn hfr hfi hfs
  have hg := rToE_ordered_wick_pairing_point_limit atTop Wfn y hy g hgn hgr hgi hgs
  have hp := (Complex.continuous_conj.continuousAt.tendsto.comp hf).mul hg
  have hpclose := (Metric.tendsto_nhds.mp hp) (ε / 3) (by positivity)
  obtain ⟨i, hi, hpi⟩ := ((eventually_ge_atTop N).and hpclose).exists
  rw [dist_eq_norm] at hpi
  obtain ⟨R, hR, hcluster⟩ := rToE_reflected_cluster_uniform_time Wfn (f i) (g i)
    (ε / 3) (by positivity)
  refine ⟨R, hR, fun s t hs ht a ha => ?_⟩
  have happrox := hN i hi ⟨s, hs⟩ ⟨t, ht⟩ a
  have hfar := hcluster s t hs ht a ha
  let A := F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (Fin.append
    (timeReflectionN d (x + fun _ => timeShiftVec d s))
    ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) j))
  let B := wickRotatedBoundaryPairing Wfn (n + m)
    ((timeShiftSchwartzNPoint s (f i).1).osConjTensorProduct
      (translateSchwartzNPoint (Fin.cons 0 a) (timeShiftSchwartzNPoint t (g i).1)))
  let C := starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n (f i).1) *
    wickRotatedBoundaryPairing Wfn m (g i).1
  let D := starRingEnd ℂ (F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (x j))) *
    F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (y j))
  change ‖B - A‖ < ε / 3 at happrox
  change ‖B - C‖ < ε / 3 at hfar
  change ‖C - D‖ < ε / 3 at hpi
  change ‖A - D‖ < ε
  have hsum : A - D = (A - B) + (B - C) + (C - D) := by ring
  rw [hsum]
  have hnorm := (norm_add_le ((A - B) + (B - C)) (C - D)).trans
    (add_le_add (norm_add_le (A - B) (B - C)) le_rfl)
  rw [norm_sub_rev A B] at hnorm
  exact hnorm.trans_lt (by linarith)

private def pointPair {n m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m) : ℂ :=
  F_ext_on_translatedPET_total Wfn
    (fun j => wickRotatePoint (Fin.append (timeReflectionN d x) y j))

private def pointDifference {n : ℕ} (Wfn : WightmanFunctions d)
    (x x' : NPointDomain d n) : ℂ :=
  pointPair Wfn x x - pointPair Wfn x' x -
    (pointPair Wfn x x' - pointPair Wfn x' x')

private def pointTimePair {n m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m) (s t : ℝ≥0) (a : Fin d → ℝ) : ℂ :=
  pointPair Wfn (x + fun _ => timeShiftVec d s)
    ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a)

private theorem pointTimePair_uniform_error (Wfn : WightmanFunctions d) (n m : ℕ)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x x' : NPointDomain d n) (y y' : NPointDomain d m),
      x ∈ OrderedPositiveTimeRegion d n → x' ∈ OrderedPositiveTimeRegion d n →
      y ∈ OrderedPositiveTimeRegion d m → y' ∈ OrderedPositiveTimeRegion d m →
      ‖pointPair Wfn y y‖ < C → ‖pointPair Wfn x' x'‖ < C →
      ‖pointDifference Wfn x x'‖ < δ → ‖pointDifference Wfn y y'‖ < δ →
      ∀ (s t : ℝ≥0) (a : Fin d → ℝ),
        ‖pointTimePair Wfn x y s t a - pointTimePair Wfn x' y' s t a‖ < ε := by
  obtain ⟨δ, hδ, herr⟩ := timeSpacePair_uniform_error Wfn n m C hC (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun x x' y y' hx hx' hy hy' hyC hxC hdx hdy s t a => ?_⟩
  obtain ⟨u, hun, hur, hui, _, hus⟩ := exists_normalized_ordered_point_sequence x hx
  obtain ⟨v, hvn, hvr, hvi, _, hvs⟩ := exists_normalized_ordered_point_sequence x' hx'
  obtain ⟨w, hwn, hwr, hwi, _, hws⟩ := exists_normalized_ordered_point_sequence y hy
  obtain ⟨z, hzn, hzr, hzi, _, hzs⟩ := exists_normalized_ordered_point_sequence y' hy'
  have huu := rToE_reflected_pairing_point_limit atTop Wfn x x hx hx u u
    hun hun hur hur hui hui hus hus
  have hvu := rToE_reflected_pairing_point_limit atTop Wfn x' x hx' hx v u
    hvn hun hvr hur hvi hui hvs hus
  have huv := rToE_reflected_pairing_point_limit atTop Wfn x x' hx hx' u v
    hun hvn hur hvr hui hvi hus hvs
  have hvv := rToE_reflected_pairing_point_limit atTop Wfn x' x' hx' hx' v v
    hvn hvn hvr hvr hvi hvi hvs hvs
  have hww := rToE_reflected_pairing_point_limit atTop Wfn y y hy hy w w
    hwn hwn hwr hwr hwi hwi hws hws
  have hzw := rToE_reflected_pairing_point_limit atTop Wfn y' y hy' hy z w
    hzn hwn hzr hwr hzi hwi hzs hws
  have hwz := rToE_reflected_pairing_point_limit atTop Wfn y y' hy hy' w z
    hwn hzn hwr hzr hwi hzi hws hzs
  have hzz := rToE_reflected_pairing_point_limit atTop Wfn y' y' hy' hy' z z
    hzn hzn hzr hzr hzi hzi hzs hzs
  have hdu : Tendsto (fun i => rToEReflectedPairing Wfn (u i - v i) (u i - v i)) atTop
      (𝓝 (pointDifference Wfn x x')) := by
    simpa only [pointDifference, pointPair, rToEReflectedPairing_sub_right,
      rToEReflectedPairing_sub_left] using (huu.sub hvu).sub (huv.sub hvv)
  have hdw : Tendsto (fun i => rToEReflectedPairing Wfn (w i - z i) (w i - z i)) atTop
      (𝓝 (pointDifference Wfn y y')) := by
    simpa only [pointDifference, pointPair, rToEReflectedPairing_sub_right,
      rToEReflectedPairing_sub_left] using (hww.sub hzw).sub (hwz.sub hzz)
  have htail : ∀ᶠ i in atTop,
      ‖timeSpacePair Wfn (u i) (w i) s t a - timeSpacePair Wfn (v i) (z i) s t a‖ < ε / 2 := by
    filter_upwards [hdu.norm.eventually (gt_mem_nhds hdx),
      hdw.norm.eventually (gt_mem_nhds hdy),
      hww.norm.eventually (gt_mem_nhds hyC), hvv.norm.eventually (gt_mem_nhds hxC)]
      with i hi hj hw hv
    exact herr (u i) (v i) (w i) (z i) hw.le hv.le hi hj s t a
  have huw := rToE_translated_reflected_pairing_point_limit atTop Wfn x y hx hy u w
    hun hwn hur hwr hui hwi hus hws s t s.2 t.2 a
  have hvz := rToE_translated_reflected_pairing_point_limit atTop Wfn x' y' hx' hy' v z
    hvn hzn hvr hzr hvi hzi hvs hzs s t s.2 t.2 a
  have hle := le_of_tendsto ((huw.sub hvz).norm)
    (htail.mono fun i hi => by simpa only [timeSpacePair_apply] using hi.le)
  exact hle.trans_lt (by linarith)

private def pointProduct {n m : ℕ} (Wfn : WightmanFunctions d)
    (p : NPointDomain d n × NPointDomain d m) : ℂ :=
  starRingEnd ℂ (F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (p.1 j))) *
    F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (p.2 j))

private theorem continuousAt_pointPair {n m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m) :
    ContinuousAt (fun p : NPointDomain d n × NPointDomain d m => pointPair Wfn p.1 p.2) (x,y) := by
  have hmap : Continuous (fun p : NPointDomain d n × NPointDomain d m =>
      Fin.append (timeReflectionN d p.1) p.2) := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left]
      apply continuous_pi
      intro μ
      simp only [timeReflectionN, timeReflection]
      split_ifs <;> fun_prop
    · simp only [Fin.append_right]
      set_option backward.isDefEq.respectTransparency false in
        exact (continuous_apply j).comp continuous_snd
  exact (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
    (reflected_ordered_points_mem_translatedPET x y hx hy)).comp
      (f := fun p : NPointDomain d n × NPointDomain d m =>
        Fin.append (timeReflectionN d p.1) p.2) (x := (x,y)) hmap.continuousAt

private theorem continuousAt_pointDifference {n : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (hx : x ∈ OrderedPositiveTimeRegion d n) :
    ContinuousAt (fun y => pointDifference Wfn y x) x := by
  have hp := continuousAt_pointPair Wfn x x hx hx
  have hd : Continuous (fun y : NPointDomain d n => (y,y)) := continuous_id.prodMk continuous_id
  have hl : Continuous (fun y : NPointDomain d n => (x,y)) := continuous_const.prodMk continuous_id
  have hr : Continuous (fun y : NPointDomain d n => (y,x)) := continuous_id.prodMk continuous_const
  exact ((hp.comp (f := fun y => (y,y)) hd.continuousAt).sub
    (hp.comp (f := fun y => (x,y)) hl.continuousAt)).sub
    ((hp.comp (f := fun y => (y,x)) hr.continuousAt).sub continuousAt_const)

private theorem continuousAt_pointProduct {n m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m) :
    ContinuousAt (pointProduct Wfn) (x,y) := by
  have hxi : Function.Injective (fun i => x i 0) :=
    (show StrictMono (fun i => x i 0) from fun i j hij => (hx i).2 j hij).injective
  have hyi : Function.Injective (fun i => y i 0) :=
    (show StrictMono (fun i => y i 0) from fun i j hij => (hy i).2 j hij).injective
  have hxc := (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
    (wick_mem_translatedPET_of_time_injective x hxi)).comp
      (f := fun p : NPointDomain d n × NPointDomain d m => p.1)
      (x := (x,y)) continuous_fst.continuousAt
  have hyc := (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
    (wick_mem_translatedPET_of_time_injective y hyi)).comp
      (f := fun p : NPointDomain d n × NPointDomain d m => p.2)
      (x := (x,y)) continuous_snd.continuousAt
  exact (Complex.continuous_conj.continuousAt.comp hxc).mul hyc

private theorem point_cluster_neighborhood {n m : ℕ} (Wfn : WightmanFunctions d)
    (p : NPointDomain d n × NPointDomain d m)
    (hp : p.1 ∈ OrderedPositiveTimeRegion d n ∧ p.2 ∈ OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 0 < R ∧
      ∀ q : NPointDomain d n × NPointDomain d m,
        q.1 ∈ OrderedPositiveTimeRegion d n → q.2 ∈ OrderedPositiveTimeRegion d m →
        dist q p < η → ∀ (s t : ℝ≥0) (a : Fin d → ℝ),
          (∑ j, (a j)^2) > R^2 →
          ‖pointTimePair Wfn q.1 q.2 s t a - pointProduct Wfn q‖ < ε := by
  let C := ‖pointPair Wfn p.1 p.1‖ + ‖pointPair Wfn p.2 p.2‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hxC : ‖pointPair Wfn p.1 p.1‖ < C := by
    dsimp [C]; linarith [norm_nonneg (pointPair Wfn p.2 p.2)]
  have hyC : ‖pointPair Wfn p.2 p.2‖ < C := by
    dsimp [C]; linarith [norm_nonneg (pointPair Wfn p.1 p.1)]
  obtain ⟨δ, hδ, herror⟩ := pointTimePair_uniform_error Wfn n m C hC (ε / 3) (by positivity)
  have hdx := (continuousAt_pointDifference Wfn p.1 hp.1).comp
    (f := fun q : NPointDomain d n × NPointDomain d m => q.1)
    (x := p) continuous_fst.continuousAt
  have hdy := (continuousAt_pointDifference Wfn p.2 hp.2).comp
    (f := fun q : NPointDomain d n × NPointDomain d m => q.2)
    (x := p) continuous_snd.continuousAt
  have hyy := (continuousAt_pointPair Wfn p.2 p.2 hp.2 hp.2).comp
    (f := fun q : NPointDomain d n × NPointDomain d m => (q.2,q.2)) (x := p)
    ((show Continuous (fun q : NPointDomain d n × NPointDomain d m => (q.2,q.2)) from
      continuous_snd.prodMk continuous_snd).continuousAt (x := p))
  have hdxlt : ∀ᶠ q in 𝓝 p, ‖pointDifference Wfn q.1 p.1‖ < δ :=
    hdx.norm.tendsto.eventually (gt_mem_nhds (by simpa [pointDifference] using hδ))
  have hdylt : ∀ᶠ q in 𝓝 p, ‖pointDifference Wfn q.2 p.2‖ < δ :=
    hdy.norm.tendsto.eventually (gt_mem_nhds (by simpa [pointDifference] using hδ))
  have hprod := Metric.tendsto_nhds.mp
    (continuousAt_pointProduct Wfn p.1 p.2 hp.1 hp.2).tendsto (ε / 3) (by positivity)
  have hgood := hdxlt.and (hdylt.and ((hyy.norm.tendsto.eventually (gt_mem_nhds hyC)).and hprod))
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hgood
  obtain ⟨R, hR, hcluster⟩ := rToE_reflected_point_kernel_cluster_uniform_time Wfn p.1 p.2
    hp.1 hp.2 (ε / 3) (by positivity)
  refine ⟨η, hη, R, hR, fun q hqx hqy hqp s t a ha => ?_⟩
  obtain ⟨hqxδ, hqyδ, hqyC, hP⟩ := hball hqp
  have hnear := herror q.1 p.1 q.2 p.2 hqx hp.1 hqy hp.2 hqyC hxC hqxδ hqyδ s t a
  have hfar := hcluster s t s.2 t.2 a ha
  change ‖pointTimePair Wfn p.1 p.2 s t a - pointProduct Wfn p‖ < ε / 3 at hfar
  rw [dist_eq_norm, norm_sub_rev] at hP
  have heq : pointTimePair Wfn q.1 q.2 s t a - pointProduct Wfn q =
      (pointTimePair Wfn q.1 q.2 s t a - pointTimePair Wfn p.1 p.2 s t a) +
      (pointTimePair Wfn p.1 p.2 s t a - pointProduct Wfn p) +
      (pointProduct Wfn p - pointProduct Wfn q) := by ring
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans_lt (by linarith)

/-- One cluster radius works on a joint compact family, uniformly in time and direction. -/
theorem rToE_reflected_point_kernel_cluster_uniform_on_isCompact
    {n m : ℕ} (Wfn : WightmanFunctions d)
    (K : Set (NPointDomain d n × NPointDomain d m)) (hK : IsCompact K)
    (hord : ∀ p ∈ K,
      p.1 ∈ OrderedPositiveTimeRegion d n ∧ p.2 ∈ OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ p ∈ K, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ∀ a : Fin d → ℝ, (∑ j, (a j)^2) > R^2 →
        ‖F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (Fin.append
          (timeReflectionN d (p.1 + fun _ => timeShiftVec d s))
          ((p.2 + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) j)) -
          starRingEnd ℂ (F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (p.1 j))) *
            F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (p.2 j))‖ < ε := by
  classical
  choose η hη r hr hlocal using fun p : K =>
    point_cluster_neighborhood Wfn p.1 (hord p.1 p.2) ε hε
  let U (p : K) := Metric.ball (p : NPointDomain d n × NPointDomain d m) (η p)
  have hU (p : K) : IsOpen (U p) := Metric.isOpen_ball
  have hcover : K ⊆ ⋃ p : K, U p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, Metric.mem_ball_self (hη ⟨p,hp⟩)⟩
  obtain ⟨L, hL⟩ := hK.elim_finite_subcover U hU hcover
  let radius (p : K) : ℝ≥0 := ⟨r p, (hr p).le⟩
  let M := L.sup radius
  let R : ℝ := M + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun p hp s t hs ht a ha => ?_⟩
  have hpL := hL hp
  simp only [mem_iUnion] at hpL
  obtain ⟨q, hqL, hpq⟩ := hpL
  have hrM : r q ≤ (M : ℝ) :=
    show (radius q : ℝ) ≤ (M : ℝ) from Finset.le_sup (f := radius) hqL
  have hrR : r q ≤ R := by dsimp [R]; linarith
  have hsep : (∑ j, (a j)^2) > (r q)^2 := by
    have hsq : (r q)^2 ≤ R^2 := by
      simpa only [pow_two] using mul_self_le_mul_self (hr q).le hrR
    exact hsq.trans_lt ha
  exact hlocal q p (hord p hp).1 (hord p hp).2 hpq ⟨s,hs⟩ ⟨t,ht⟩ a hsep

end OSReconstruction
