import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEPointKernels
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToETimeShiftBounds

/-!
# Translated Euclidean Point Bounds

Normalized point recovery commutes with nonnegative time shifts and spatial
translations. The reflected source estimate therefore gives a point-kernel
bound uniform in all these parameters. Continuity also upgrades the a.e.
Euclidean growth estimate to every point of the translated-PET domain.

Uniform approximation and clustering are separate obligations.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace OSReconstruction

set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false

/-- The actual Euclidean growth bound holds pointwise throughout the analytic domain. -/
theorem wick_rotated_kernel_polynomial_growth_on_translatedPET
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) :
    ∃ (C : ℝ) (N q : ℕ), 0 < C ∧ ∀ x : NPointDomain d n,
      (fun j => wickRotatePoint (x j)) ∈ TranslatedPET d n →
      ‖F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (x j))‖ *
        Metric.infDist x (CoincidenceLocus d n) ^ (q + 1) ≤ C * (1 + ‖x‖) ^ N := by
  obtain ⟨C, N, q, hC, hgrowth⟩ := wick_rotated_kernel_ae_polynomial_growth (n := n) Wfn
  refine ⟨C, N, q, hC, fun x hx => ?_⟩
  let S : Set (NPointDomain d n) := {y |
    ‖F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (y j))‖ *
      Metric.infDist y (CoincidenceLocus d n) ^ (q + 1) ≤ C * (1 + ‖y‖) ^ N}
  have hS : x ∈ closure S := (Measure.dense_of_ae (μ := volume) hgrowth) x
  haveI : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hS
  have hl := (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn hx).norm.mul
    ((Metric.continuous_infDist_pt (s := CoincidenceLocus d n)).continuousAt.pow (q + 1))
  have hr : ContinuousAt (fun y : NPointDomain d n => C * (1 + ‖y‖) ^ N) x := by
    fun_prop
  exact le_of_tendsto_of_tendsto (hl.tendsto.mono_left nhdsWithin_le_nhds)
    (hr.tendsto.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin

private theorem integral_translateSchwartzNPoint
    {d n : ℕ} [NeZero d] (a : SpacetimeDim d) (f : SchwartzNPoint d n) :
    (∫ z, translateSchwartzNPoint a f z) = ∫ z, f z := by
  change (∫ z : NPointDomain d n, f (z - fun _ => a)) = _
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self (fun z : NPointDomain d n => f z) (-(fun _ => a)))

private theorem support_translateSchwartzNPoint_subset_ball
    {d n : ℕ} [NeZero d] (a : SpacetimeDim d) (f : SchwartzNPoint d n)
    (x : NPointDomain d n) (δ : ℝ)
    (hf : Function.support (f : NPointDomain d n → ℂ) ⊆ Metric.ball x δ) :
    Function.support (translateSchwartzNPoint a f : NPointDomain d n → ℂ) ⊆
      Metric.ball (x + fun _ => a) δ := by
  intro z hz
  have hz' : f (z - fun _ => a) ≠ 0 := hz
  have hdist := hf hz'
  change dist (z - fun _ => a) x < δ at hdist
  change dist z (x + fun _ => a) < δ
  rw [dist_eq_norm] at hdist ⊢
  convert hdist using 1
  congr 1
  abel

private theorem ordered_points_add_nonnegative_time
    {d n : ℕ} (x : NPointDomain d n) (hx : x ∈ OrderedPositiveTimeRegion d n)
    (a : SpacetimeDim d) (ha : 0 ≤ a 0) :
    (x + fun _ => a) ∈ OrderedPositiveTimeRegion d n := by
  intro i
  constructor
  · exact add_pos_of_pos_of_nonneg (hx i).1 ha
  · intro j hij
    change x i 0 + a 0 < x j 0 + a 0
    linarith [(hx i).2 j hij]

/-- Normalized reflected point recovery respects each nonnegative time and spatial shift. -/
theorem rToE_translated_reflected_pairing_point_limit
    {d n m : ℕ} [NeZero d] {I : Type*} (l : Filter I) (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m)
    (f : I → euclideanPositiveTimeSubmodule (d := d) n)
    (g : I → euclideanPositiveTimeSubmodule (d := d) m)
    (hfn : ∀ i z, 0 ≤ ((f i).1 z).re) (hgn : ∀ i z, 0 ≤ ((g i).1 z).re)
    (hfr : ∀ i z, ((f i).1 z).im = 0) (hgr : ∀ i z, ((g i).1 z).im = 0)
    (hfi : ∀ i, ∫ z, (f i).1 z = 1) (hgi : ∀ i, ∫ z, (g i).1 z = 1)
    (hfs : ∀ δ > 0, ∀ᶠ i in l,
      Function.support ((f i).1 : NPointDomain d n → ℂ) ⊆ Metric.ball x δ)
    (hgs : ∀ δ > 0, ∀ᶠ i in l,
      Function.support ((g i).1 : NPointDomain d m → ℂ) ⊆ Metric.ball y δ)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (a : Fin d → ℝ) :
    Tendsto (fun i => wickRotatedBoundaryPairing Wfn (n + m)
      ((timeShiftSchwartzNPoint s (f i).1).osConjTensorProduct
        (translateSchwartzNPoint (Fin.cons 0 a) (timeShiftSchwartzNPoint t (g i).1)))) l
      (𝓝 (F_ext_on_translatedPET_total Wfn
        (fun j => wickRotatePoint (Fin.append
          (timeReflectionN d (x + fun _ => timeShiftVec d s))
          ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) j)))) := by
  let fs (i : I) := osiiOriginalOSNonnegativeTimeShiftSource (f i) ⟨s, hs⟩
  let gt (i : I) := osiiOriginalOSNonnegativeTimeShiftSource (g i) ⟨t, ht⟩
  let ga (i : I) : euclideanPositiveTimeSubmodule (d := d) m :=
    ⟨translateSchwartzNPoint (Fin.cons 0 a) (gt i).1,
      translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (Fin.cons 0 a) (by simp) (gt i).1 (gt i).2⟩
  have hxs := ordered_points_add_nonnegative_time x hx (timeShiftVec d s) (by simpa [timeShiftVec] using hs)
  have hyt := ordered_points_add_nonnegative_time y hy (timeShiftVec d t) (by simpa [timeShiftVec] using ht)
  have hya := ordered_points_add_nonnegative_time _ hyt (Fin.cons 0 a) (by simp)
  have hfsi (i : I) : ∫ z, (fs i).1 z = 1 := by
    change (∫ z, translateSchwartzNPoint (timeShiftVec d s) (f i).1 z) = 1
    rw [integral_translateSchwartzNPoint, hfi]
  have hgai (i : I) : ∫ z, (ga i).1 z = 1 := by
    change (∫ z, translateSchwartzNPoint (Fin.cons 0 a)
      (translateSchwartzNPoint (timeShiftVec d t) (g i).1) z) = 1
    rw [integral_translateSchwartzNPoint, integral_translateSchwartzNPoint, hgi]
  have hfss : ∀ δ > 0, ∀ᶠ i in l,
      Function.support ((fs i).1 : NPointDomain d n → ℂ) ⊆
        Metric.ball (x + fun _ => timeShiftVec d s) δ := by
    intro δ hδ
    filter_upwards [hfs δ hδ] with i hi
    exact support_translateSchwartzNPoint_subset_ball _ _ _ _ hi
  have hgas : ∀ δ > 0, ∀ᶠ i in l,
      Function.support ((ga i).1 : NPointDomain d m → ℂ) ⊆
        Metric.ball ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) δ := by
    intro δ hδ
    filter_upwards [hgs δ hδ] with i hi
    exact support_translateSchwartzNPoint_subset_ball _ _ _ _
      (support_translateSchwartzNPoint_subset_ball _ _ _ _ hi)
  exact rToE_reflected_pairing_point_limit l Wfn _ _ hxs hya fs ga
    (fun i z => hfn i _) (fun i z => hgn i _)
    (fun i z => hfr i _) (fun i z => hgr i _) hfsi hgai hfss hgas

/-- Unshifted reflected self-kernels bound every translated reflected point pairing. -/
theorem rToE_reflected_point_kernel_uniform_timeSpace_bound
    {d n m : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (a : Fin d → ℝ) :
    ‖F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (Fin.append
      (timeReflectionN d (x + fun _ => timeShiftVec d s))
      ((y + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 a) j))‖ ^ 2 ≤
      ‖F_ext_on_translatedPET_total Wfn
        (fun j => wickRotatePoint (Fin.append (timeReflectionN d x) x j))‖ *
      ‖F_ext_on_translatedPET_total Wfn
        (fun j => wickRotatePoint (Fin.append (timeReflectionN d y) y j))‖ := by
  obtain ⟨f, hfn, hfr, hfi, _, hfs⟩ := exists_normalized_ordered_point_sequence x hx
  obtain ⟨g, hgn, hgr, hgi, _, hgs⟩ := exists_normalized_ordered_point_sequence y hy
  have hfg := rToE_translated_reflected_pairing_point_limit atTop Wfn x y hx hy f g
    hfn hgn hfr hgr hfi hgi hfs hgs s t hs ht a
  have hff := rToE_reflected_pairing_point_limit atTop Wfn x x hx hx f f
    hfn hfn hfr hfr hfi hfi hfs hfs
  have hgg := rToE_reflected_pairing_point_limit atTop Wfn y y hy hy g g
    hgn hgn hgr hgr hgi hgi hgs hgs
  exact le_of_tendsto_of_tendsto (hfg.norm.pow 2) (hff.norm.mul hgg.norm)
    (Eventually.of_forall fun i =>
      rToE_reflected_timeSpaceShift_pairing_bound Wfn (f i) (g i) s t hs ht a)

end OSReconstruction
