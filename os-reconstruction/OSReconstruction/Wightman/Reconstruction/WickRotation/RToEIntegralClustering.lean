import OSReconstruction.Wightman.Reconstruction.WickRotation.RToESpatialPointClustering
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEClusteringTails
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Full R-to-E Clustering

The almost-everywhere point limit passes through the relatively separated bulk
by dominated convergence. The admissible translated-test witnesses control the
complementary tails. Empty blocks factorize exactly. The final theorem retains
the full original E4 quantifiers and the Euclidean spatial radius.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace OSReconstruction
variable {d n m : ℕ} [NeZero d]
set_option maxHeartbeats 800000

private def kernel (Wfn : WightmanFunctions d) (x : NPointDomain d n) : ℂ :=
  F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (x i))

private def blockShift (n m : ℕ) (a : SpacetimeDim d) : NPointDomain d (n+m) :=
  Fin.append (fun _ : Fin n => 0) (fun _ : Fin m => a)

omit [NeZero d] in
private theorem append_split (z : NPointDomain d (n+m)) :
    Fin.append (splitFirst n m z) (splitLast n m z) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [splitFirst]
  · simp [splitLast]

omit [NeZero d] in
private theorem add_blockShift (z : NPointDomain d (n+m)) (a : SpacetimeDim d) :
    z + blockShift n m a =
      Fin.append (splitFirst n m z) (fun j => splitLast n m z j + a) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [blockShift,splitFirst]
  · simp [blockShift,splitLast]

omit [NeZero d] in
private theorem norm_spatialLift (a : Fin d → ℝ) :
    ‖(Fin.cons 0 a : SpacetimeDim d)‖ = ‖a‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro μ
    refine Fin.cases ?_ (fun j => ?_) μ
    · simpa only [Fin.cons_zero,norm_zero] using norm_nonneg a
    · simpa only [Fin.cons_succ] using norm_le_pi_norm a j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro j
    simpa only [Fin.cons_succ] using
      norm_le_pi_norm (Fin.cons 0 a : SpacetimeDim d) j.succ

omit [NeZero d] in
private theorem finAddProd_apply_split (z : NPointDomain d (n+m)) :
    MeasurableEquiv.finAddProd n m (SpacetimeDim d) z =
      (splitFirst n m z,splitLast n m z) := by
  let e := MeasurableEquiv.finAddProd n m (SpacetimeDim d)
  have hs : e.symm (splitFirst n m z,splitLast n m z) = z := by
    rw [MeasurableEquiv.finAddProd_symm_apply,append_split]
  calc
    e z = e (e.symm (splitFirst n m z,splitLast n m z)) := congrArg e hs.symm
    _ = (splitFirst n m z,splitLast n m z) := e.apply_symm_apply _

omit [NeZero d] in
private theorem integral_split_product (F : NPointDomain d n → ℂ)
    (G : NPointDomain d m → ℂ) :
    (∫ z : NPointDomain d (n+m), F (splitFirst n m z)*G (splitLast n m z)) =
      (∫ x, F x)*(∫ y, G y) := by
  calc
    _ = ∫ p : NPointDomain d n × NPointDomain d m, F p.1*G p.2 := by
      simpa only [finAddProd_apply_split] using
        (volume_preserving_finAddProd n m (SpacetimeDim d)).integral_comp'
          (fun p => F p.1*G p.2)
    _ = _ := integral_prod_mul F G

private theorem block_kernel_measurable (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m)
    (a : SpacetimeDim d) :
    AEStronglyMeasurable (fun z : NPointDomain d (n+m) =>
      kernel Wfn (z + blockShift n m a)*(f.1.tensorProduct g.1) z) volume := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (NPointDomain d (n+m))) :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  exact ((bhw_euclidean_kernel_measurable Wfn).comp_quasiMeasurePreserving
    (measurePreserving_add_right volume (blockShift n m a)).quasiMeasurePreserving).mul
      (f.1.tensorProduct g.1).continuous.aestronglyMeasurable

private theorem bulk_integral_tendsto (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun a : Fin d → ℝ =>
        ∫ z in {z : NPointDomain d (n+m) | L*(1+‖z‖) < ‖a‖},
          kernel Wfn (z + blockShift n m (Fin.cons 0 a))*(f.1.tensorProduct g.1) z)
        (cocompact (Fin d → ℝ))
        (𝓝 (constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g)) := by
  classical
  obtain ⟨L,B,hL,hBi,hBn,hB⟩ := rToE_spatial_bulk_kernel_test_majorant Wfn f g
  let J (a : Fin d → ℝ) (z : NPointDomain d (n+m)) :=
    kernel Wfn (z + blockShift n m (Fin.cons 0 a))*(f.1.tensorProduct g.1) z
  let H (z : NPointDomain d (n+m)) :=
    (kernel Wfn (splitFirst n m z)*f.1 (splitFirst n m z))*
      (kernel Wfn (splitLast n m z)*g.1 (splitLast n m z))
  let s (a : Fin d → ℝ) : Set (NPointDomain d (n+m)) := {z | L*(1+‖z‖) < ‖a‖}
  have hs (a : Fin d → ℝ) : MeasurableSet (s a) :=
    (isOpen_lt (continuous_const.mul (continuous_const.add continuous_norm)) continuous_const).measurableSet
  have hmeas (a : Fin d → ℝ) : AEStronglyMeasurable ((s a).indicator (J a)) volume :=
    (block_kernel_measurable Wfn f g (Fin.cons 0 a)).indicator (hs a)
  have hbound (a : Fin d → ℝ) : ∀ᵐ z : NPointDomain d (n+m),
      ‖(s a).indicator (J a) z‖ ≤ B z := by
    filter_upwards [ae_pairwise_distinct_timeCoords (d := d) (n := n+m)] with z hz
    by_cases hzs : z ∈ s a
    · rw [Set.indicator_of_mem hzs]
      have hzt : Function.Injective (fun i => z i 0) := by
        intro i j hij
        by_contra hne
        exact hz i j hne hij
      have hxy : Function.Injective (fun i =>
          Fin.append (splitFirst n m z) (splitLast n m z) i 0) := by
        simpa only [append_split] using hzt
      have ha : L*(1+‖Fin.append (splitFirst n m z) (splitLast n m z)‖) <
          ‖(Fin.cons 0 a : SpacetimeDim d)‖ := by
        simpa only [append_split,norm_spatialLift] using hzs
      have hb := hB (splitFirst n m z) (splitLast n m z) hxy
        (Fin.cons 0 a) (by simp) ha
      simpa only [J,kernel,add_blockShift,SchwartzMap.tensorProduct_apply,norm_mul,
        append_split,mul_assoc] using hb
    · rw [Set.indicator_of_notMem hzs,norm_zero]
      exact hBn z
  have hlim : ∀ᵐ z : NPointDomain d (n+m),
      Tendsto (fun a : Fin d → ℝ => (s a).indicator (J a) z)
        (cocompact (Fin d → ℝ)) (𝓝 (H z)) := by
    filter_upwards [rToE_point_kernel_tendsto_spatial_ae m Wfn] with z hz
    have hk : Tendsto (fun a : Fin d → ℝ => kernel Wfn (z + blockShift n m (Fin.cons 0 a)))
        (cocompact (Fin d → ℝ))
        (𝓝 (kernel Wfn (splitFirst n m z)*kernel Wfn (splitLast n m z))) := by
      simpa only [kernel,add_blockShift] using hz
    have hJ := hk.mul (tendsto_const_nhds (x := (f.1.tensorProduct g.1) z))
    have heq : (kernel Wfn (splitFirst n m z)*kernel Wfn (splitLast n m z))*
        (f.1.tensorProduct g.1) z = H z := by
      dsimp [H]
      ring
    rw [heq] at hJ
    have he : ∀ᶠ a : Fin d → ℝ in cocompact (Fin d → ℝ), z ∈ s a :=
      tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (L*(1+‖z‖)))
    exact hJ.congr' (he.mono fun a ha => (Set.indicator_of_mem ha (J a)).symm)
  haveI : (cocompact (Fin d → ℝ)).IsCountablyGenerated := by
    rw [← comap_dist_left_atTop_eq_cocompact (0 : Fin d → ℝ)]
    infer_instance
  have hDCT := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hBi hlim
  have hfactor : (∫ z, H z) =
      constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g :=
    integral_split_product (fun x => kernel Wfn x*f.1 x) (fun y => kernel Wfn y*g.1 y)
  rw [hfactor] at hDCT
  refine ⟨L,hL,?_⟩
  simpa only [integral_indicator (hs _)] using hDCT

private theorem kernel_add_const (Wfn : WightmanFunctions d)
    (z : NPointDomain d n) (hz : Function.Injective (fun i => z i 0))
    (a : SpacetimeDim d) : kernel Wfn (z + fun _ => a) = kernel Wfn z := by
  have hzt : Function.Injective (fun i : Fin n => z i 0 + a 0) := by
    intro i j hij
    exact hz (add_right_cancel hij)
  exact (F_ext_translation_invariant_translated Wfn n a z
    (wick_mem_translatedPET_of_time_injective z hz)
    (wick_mem_translatedPET_of_time_injective (z + fun _ => a) hzt)).symm

private theorem kernel_blockShift_of_empty (Wfn : WightmanFunctions d)
    (hzero : n = 0 ∨ m = 0) (z : NPointDomain d (n+m))
    (hz : Function.Injective (fun i => z i 0)) (a : SpacetimeDim d) :
    kernel Wfn (z + blockShift n m a) = kernel Wfn z := by
  rcases hzero with rfl | rfl
  · have hs : blockShift 0 m a = fun _ => a := by
      funext i
      refine Fin.addCases (fun j => Fin.elim0 j) (fun j => ?_) i
      simp only [blockShift,Fin.append_right]
    rw [hs]
    exact kernel_add_const Wfn z hz a
  · have hs : blockShift n 0 a = 0 := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => Fin.elim0 j) i
      simp only [blockShift,Fin.append_left,Pi.zero_apply]
    rw [hs]
    apply congrArg (kernel Wfn)
    funext i μ
    exact add_zero (z i μ)

private theorem block_integral_factorizes_of_empty (Wfn : WightmanFunctions d)
    (hzero : n = 0 ∨ m = 0) (f : ZeroDiagonalSchwartz d n)
    (g : ZeroDiagonalSchwartz d m) (a : SpacetimeDim d) :
    (∫ z : NPointDomain d (n+m),
      kernel Wfn (z + blockShift n m a)*(f.1.tensorProduct g.1) z) =
      constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g := by
  calc
    _ = ∫ z : NPointDomain d (n+m),
        (kernel Wfn (splitFirst n m z)*f.1 (splitFirst n m z))*
          (kernel Wfn (splitLast n m z)*g.1 (splitLast n m z)) := by
      apply integral_congr_ae
      filter_upwards [ae_pairwise_distinct_timeCoords (d := d) (n := n+m),
        rToE_point_kernel_tendsto_spatial_ae m Wfn] with z hz hlim
      have hzt : Function.Injective (fun i => z i 0) := by
        intro i j hij
        by_contra hne
        exact hz i j hne hij
      have hk : Tendsto (fun b : Fin d → ℝ => kernel Wfn (z + blockShift n m (Fin.cons 0 b)))
          (cocompact (Fin d → ℝ))
          (𝓝 (kernel Wfn (splitFirst n m z)*kernel Wfn (splitLast n m z))) := by
        simpa only [kernel,add_blockShift] using hlim
      have hconst : Tendsto (fun b : Fin d → ℝ => kernel Wfn (z + blockShift n m (Fin.cons 0 b)))
          (cocompact (Fin d → ℝ)) (𝓝 (kernel Wfn z)) :=
        tendsto_const_nhds.congr' (Eventually.of_forall fun b =>
          (kernel_blockShift_of_empty Wfn hzero z hzt (Fin.cons 0 b)).symm)
      have hfactor := tendsto_nhds_unique hconst hk
      rw [kernel_blockShift_of_empty Wfn hzero z hzt a,hfactor,SchwartzMap.tensorProduct_apply]
      ring
    _ = _ := integral_split_product
      (fun x => kernel Wfn x*f.1 x) (fun y => kernel Wfn y*g.1 y)

private theorem translated_block_pairing (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m)
    (a : SpacetimeDim d) (g_a : ZeroDiagonalSchwartz d m)
    (hga : ∀ x, g_a.1 x = g.1 (fun i => x i - a))
    (fg_a : ZeroDiagonalSchwartz d (n+m))
    (hfg : ∀ x, fg_a.1 x = f.1 (splitFirst n m x)*g_a.1 (splitLast n m x)) :
    Integrable (fun z : NPointDomain d (n+m) =>
      kernel Wfn (z + blockShift n m a)*(f.1.tensorProduct g.1) z) ∧
    constructSchwingerFunctions Wfn (n+m) fg_a =
      ∫ z : NPointDomain d (n+m),
        kernel Wfn (z + blockShift n m a)*(f.1.tensorProduct g.1) z := by
  have heq (z : NPointDomain d (n+m)) :
      fg_a.1 (z + blockShift n m a) = (f.1.tensorProduct g.1) z := by
    have hl : splitFirst n m (z + blockShift n m a) = splitFirst n m z := by
      funext i
      simp [splitFirst,blockShift]
    have hr : (fun i => splitLast n m (z + blockShift n m a) i - a) = splitLast n m z := by
      funext i
      simp [splitLast,blockShift]
    rw [hfg,hga,hl,hr,SchwartzMap.tensorProduct_apply]
  haveI : Measure.IsAddHaarMeasure (volume : Measure (NPointDomain d (n+m))) :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  refine ⟨?_,?_⟩
  · have hi := (measurePreserving_add_right volume (blockShift n m a)).integrable_comp_of_integrable
      (wick_rotated_kernel_mul_zeroDiagonal_integrable Wfn fg_a)
    simpa only [Function.comp_def,heq] using hi
  · change (∫ z, kernel Wfn z*fg_a.1 z) = _
    calc
      _ = ∫ z : NPointDomain d (n+m),
          kernel Wfn (z + blockShift n m a)*fg_a.1 (z + blockShift n m a) :=
        (integral_add_right_eq_self (fun z => kernel Wfn z*fg_a.1 z) (blockShift n m a)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun z =>
        congrArg (fun v => kernel Wfn (z + blockShift n m a)*v) (heq z))

private theorem constructed_cluster_norm (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : SpacetimeDim d, a 0 = 0 → R < ‖a‖ →
      ∀ (g_a : ZeroDiagonalSchwartz d m),
        (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
        ∀ (fg_a : ZeroDiagonalSchwartz d (n+m)),
          (∀ x, fg_a.1 x = f.1 (splitFirst n m x)*g_a.1 (splitLast n m x)) →
          ‖constructSchwingerFunctions Wfn (n+m) fg_a -
            constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g‖ < ε := by
  classical
  by_cases hzero : n = 0 ∨ m = 0
  · refine ⟨1,zero_lt_one,fun a _ _ g_a hga fg_a hfg => ?_⟩
    have heq := (translated_block_pairing Wfn f g a g_a hga fg_a hfg).2.trans
      (block_integral_factorizes_of_empty Wfn hzero f g a)
    rw [heq,sub_self,norm_zero]
    exact hε
  have hcoin : (CoincidenceLocus d (n+m)).Nonempty := by
    have hn : 0 < n := by omega
    have hm : 0 < m := by omega
    exact ⟨0,⟨0,by omega⟩,⟨1,by omega⟩,by simp [Fin.ext_iff],rfl⟩
  obtain ⟨L,hL,hbulk⟩ := bulk_integral_tendsto Wfn f g
  have he := (Metric.tendsto_nhds.mp hbulk) (ε/2) (by positivity)
  rw [← Metric.cobounded_eq_cocompact] at he
  obtain ⟨Rb,_,hRb⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : Fin d → ℝ)).eventually_iff.mp he
  obtain ⟨Rt,hRt,hTail⟩ := rToE_wick_kernel_block_tail_small Wfn f g hcoin L hL.le (ε/2) (by positivity)
  refine ⟨1+|Rb|+Rt,by positivity,fun a ha0 ha g_a hga fg_a hfg => ?_⟩
  have hbr : Rb < ‖a‖ := by linarith [le_abs_self Rb]
  have htr : Rt < ‖a‖ := by linarith [abs_nonneg Rb]
  let b : Fin d → ℝ := fun j => a j.succ
  have hcons : (Fin.cons 0 b : SpacetimeDim d) = a := by
    funext μ
    refine Fin.cases ?_ (fun j => rfl) μ
    simpa only [Fin.cons_zero] using ha0.symm
  have hbn : ‖b‖ = ‖a‖ := (norm_spatialLift b).symm.trans (congrArg norm hcons)
  have hb := hRb (x := b) (by simpa only [Set.mem_compl_iff,Metric.mem_closedBall,dist_zero_right,hbn] using not_le.mpr hbr)
  let J (z : NPointDomain d (n+m)) := kernel Wfn (z + blockShift n m a)*(f.1.tensorProduct g.1) z
  let s : Set (NPointDomain d (n+m)) := {z | L*(1+‖z‖) < ‖a‖}
  have hs : MeasurableSet s :=
    (isOpen_lt (continuous_const.mul (continuous_const.add continuous_norm)) continuous_const).measurableSet
  have hsc : sᶜ = {z : NPointDomain d (n+m) | ‖a‖ ≤ L*(1+‖z‖)} := by
    ext z
    simp only [s,Set.mem_compl_iff,Set.mem_setOf_eq,not_lt]
  have hb' : ‖(∫ z in s, J z) -
      constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g‖ < ε/2 := by
    simpa only [dist_eq_norm,hcons,hbn] using hb
  have ht : ‖∫ z in sᶜ, J z‖ < ε/2 := by
    apply (norm_integral_le_integral_norm _).trans_lt
    rw [hsc]
    exact hTail a htr g_a hga fg_a hfg
  obtain ⟨hJi,hPair⟩ := translated_block_pairing Wfn f g a g_a hga fg_a hfg
  rw [hPair]
  calc
    ‖(∫ z, J z) - constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g‖ =
        ‖((∫ z in s, J z) - constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g) +
          ∫ z in sᶜ, J z‖ := by
      rw [← integral_add_compl hs hJi]
      congr 1
      ring
    _ ≤ ‖(∫ z in s, J z) - constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g‖ +
        ‖∫ z in sᶜ, J z‖ := norm_add_le _ _
    _ < ε := by linarith

/-- Full E4 for the actual zero-diagonal Schwinger family, in every spatial direction. -/
theorem rToE_constructed_full_E4 (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : SpacetimeDim d, a 0 = 0 →
      (∑ i : Fin d, (a i.succ)^2) > R^2 →
      ∀ (g_a : ZeroDiagonalSchwartz d m),
        (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
        ∀ (fg_a : ZeroDiagonalSchwartz d (n+m)),
          (∀ x, fg_a.1 x = f.1 (splitFirst n m x)*g_a.1 (splitLast n m x)) →
          ‖constructSchwingerFunctions Wfn (n+m) fg_a -
            constructSchwingerFunctions Wfn n f * constructSchwingerFunctions Wfn m g‖ < ε := by
  obtain ⟨A,hA,hcluster⟩ := constructed_cluster_norm Wfn f g ε hε
  refine ⟨(d+1 : ℝ)*A,by positivity,fun a ha0 ha => hcluster a ha0 ?_⟩
  by_contra h
  have hn : ‖a‖ ≤ A := le_of_not_gt h
  have hsum : (∑ i : Fin d, (a i.succ)^2) ≤ (d : ℝ)*A^2 := by
    calc
      _ ≤ ∑ _i : Fin d, A^2 := Finset.sum_le_sum fun i _ => by
        have hi : |a i.succ| ≤ A := by
          simpa only [Real.norm_eq_abs] using (norm_le_pi_norm a i.succ).trans hn
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA.le).2 hi
      _ = _ := by simp
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  nlinarith [sq_nonneg ((d : ℝ)*A)]

end OSReconstruction
