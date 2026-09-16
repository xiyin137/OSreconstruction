/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEReflectedClusterClosure
import OSReconstruction.GeneralResults.FinProductIntegral
import Mathlib.Analysis.Calculus.BumpFunction.Normed












noncomputable section

open scoped Topology
open Set Filter MeasureTheory

namespace OSReconstruction

set_option synthInstance.maxSize 256

/-- The total extension is holomorphic wherever its translated-PET branch is defined. -/
theorem differentiableAt_F_ext_on_translatedPET_total
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {z : Fin n → Fin (d + 1) → ℂ} (hz : z ∈ TranslatedPET d n) :
    DifferentiableAt ℂ (F_ext_on_translatedPET_total Wfn) z := by
  obtain ⟨c, hc⟩ := hz
  let τ : (Fin n → Fin (d + 1) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
    fun w => w + fun _ => c
  have hPET : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hτ : Differentiable ℂ τ := differentiable_id.add_const _
  have hd : DifferentiableAt ℂ (fun w => (W_analytic_BHW Wfn n).val (τ w)) z :=
    (((W_analytic_BHW Wfn n).property.1 _ hc).differentiableAt (hPET.mem_nhds hc)).comp z
      (hτ z)
  have heq : F_ext_on_translatedPET_total Wfn =ᶠ[𝓝 z]
      (fun w => (W_analytic_BHW Wfn n).val (τ w)) := by
    have hU : {w | τ w ∈ PermutedExtendedTube d n} ∈ 𝓝 z :=
      (hPET.preimage hτ.continuous).mem_nhds hc
    filter_upwards [hU] with w hw
    exact (F_ext_on_translatedPET_total_translation_invariant Wfn w c ⟨c, hw⟩).trans
      (F_ext_on_translatedPET_total_eq_on_PET Wfn (τ w) hw)
  exact heq.differentiableAt_iff.mpr hd

/-- The actual Euclidean kernel is continuous at every point in its analytic domain. -/
theorem continuousAt_euclidean_kernel_of_mem_translatedPET
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {x : NPointDomain d n}
    (hx : (fun i => wickRotatePoint (x i)) ∈ TranslatedPET d n) :
    ContinuousAt
      (fun y : NPointDomain d n =>
        F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (y i))) x := by
  have hwick : Continuous (fun y : NPointDomain d n => fun i => wickRotatePoint (y i)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    simp only [wickRotatePoint]
    split_ifs <;> fun_prop
  exact (differentiableAt_F_ext_on_translatedPET_total Wfn hx).continuousAt.comp
    hwick.continuousAt

/-- Distinct Euclidean times give domain membership after a common positive time shift. -/
theorem wick_mem_translatedPET_of_time_injective
    {d n : ℕ} [NeZero d] (x : NPointDomain d n)
    (hx : Function.Injective (fun i => x i 0)) :
    (fun i => wickRotatePoint (x i)) ∈ TranslatedPET d n := by
  let A : ℝ := 1 + ∑ i : Fin n, |x i 0|
  let a : SpacetimeDim d := fun μ => if μ = 0 then A else 0
  let xs : NPointDomain d n := fun i => x i + a
  have hpos (i : Fin n) : 0 < xs i 0 := by
    have hi := Finset.single_le_sum (f := fun j : Fin n => |x j 0|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [xs, a, A]
    linarith [neg_abs_le (x i 0)]
  have hdistinct : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0 := by
    intro i j hij heq
    apply hij
    apply hx
    simpa [xs] using heq
  have hpet := euclidean_distinct_in_permutedTube xs hdistinct hpos
  refine ⟨wickRotatePoint a, ?_⟩
  convert hpet using 1
  ext i μ
  simp only [xs, Pi.add_apply, wickRotatePoint]
  split_ifs <;> push_cast <;> ring

/-- Two reflected ordered blocks have distinct joint times, also for empty blocks. -/
theorem reflected_ordered_points_mem_translatedPET
    {d n m : ℕ} [NeZero d] (x : NPointDomain d n) (y : NPointDomain d m)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (hy : y ∈ OrderedPositiveTimeRegion d m) :
    (fun i => wickRotatePoint ((Fin.append (timeReflectionN d x) y) i)) ∈
      TranslatedPET d (n + m) := by
  have hxinj : Function.Injective (fun i => x i 0) :=
    (show StrictMono (fun i => x i 0) from fun i j hij => (hx i).2 j hij).injective
  have hyinj : Function.Injective (fun i => y i 0) :=
    (show StrictMono (fun i => y i 0) from fun i j hij => (hy i).2 j hij).injective
  apply wick_mem_translatedPET_of_time_injective
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro h
      simp only [Fin.append_left, timeReflectionN, timeReflection, ite_true] at h
      exact congrArg (Fin.castAdd m) (hxinj (neg_inj.mp h))
    · intro h
      simp only [Fin.append_left, Fin.append_right, timeReflectionN, timeReflection, ite_true] at h
      linarith [(hx i).1, (hy j).1]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro h
      simp only [Fin.append_left, Fin.append_right, timeReflectionN, timeReflection, ite_true] at h
      linarith [(hy i).1, (hx j).1]
    · intro h
      simp only [Fin.append_right] at h
      exact congrArg (Fin.natAdd n) (hyinj h)

set_option synthInstance.maxSize 256 in
/-- A nonnegative unit-mass compact source can be localized at any ordered point. -/
theorem exists_normalized_ordered_point_bump
    {d n : ℕ} [NeZero d] (x : NPointDomain d n)
    (hx : x ∈ OrderedPositiveTimeRegion d n) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : euclideanPositiveTimeSubmodule (d := d) n,
      (∀ y, 0 ≤ (f.1 y).re) ∧ (∀ y, (f.1 y).im = 0) ∧
      (∫ y, f.1 y = 1) ∧ HasCompactSupport (f.1 : NPointDomain d n → ℂ) ∧
      tsupport (f.1 : NPointDomain d n → ℂ) ⊆ Metric.ball x ε := by
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp
    (BHW.isOpen_orderedPositiveTimeRegion (d := d) (n := n)) x hx
  have hmin : 0 < min ε r := lt_min hε hr
  let b : ContDiffBump x := ⟨min ε r / 4, min ε r / 2, by positivity, by linarith⟩
  let v : NPointDomain d n → ℂ := fun y => (b.normed volume y : ℂ)
  have hv_smooth : ContDiff ℝ (⊤ : ℕ∞) v :=
    Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hv_compact : HasCompactSupport v :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  let φ : SchwartzNPoint d n := hv_compact.toSchwartzMap hv_smooth
  have hsupp : tsupport (φ : NPointDomain d n → ℂ) ⊆ Metric.closedBall x (min ε r / 2) := by
    change tsupport v ⊆ _
    exact (tsupport_comp_subset Complex.ofReal_zero (b.normed volume)).trans
      (by rw [b.tsupport_normed_eq])
  have hball (t : ℝ) (ht : min ε r ≤ t) :
      tsupport (φ : NPointDomain d n → ℂ) ⊆ Metric.ball x t := by
    intro y hy
    have hy' := hsupp hy
    rw [Metric.mem_closedBall] at hy'
    rw [Metric.mem_ball]
    linarith
  refine ⟨⟨φ, (hball r (min_le_right _ _)).trans hrball⟩,
    fun y => b.nonneg_normed y, fun y => Complex.ofReal_im _, ?_, hv_compact,
    hball ε (min_le_left _ _)⟩
  change (∫ y, (b.normed volume y : ℂ)) = 1
  rw [integral_complex_ofReal, b.integral_normed]
  norm_num

private theorem integral_norm_one_of_nonnegative_real
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ)
    (hf : Integrable f μ) (hn : ∀ x, 0 ≤ (f x).re)
    (hr : ∀ x, (f x).im = 0) (hi : ∫ x, f x ∂μ = 1) :
    ∫ x, ‖f x‖ ∂μ = 1 := by
  have heq (x : X) : ‖f x‖ = (f x).re :=
    (Complex.re_eq_norm.mpr ⟨hn x, (hr x).symm⟩).symm
  simp_rw [heq]
  change (∫ x, RCLike.re (f x) ∂μ) = 1
  rw [integral_re hf]
  exact congrArg Complex.re hi

set_option backward.isDefEq.respectTransparency false in
private theorem tendsto_integral_mul_shrinking_support
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (l : Filter ι) (f : ι → X → ℂ) (K : X → ℂ) (x : X)
    (hf : ∀ i, Integrable (f i) μ)
    (hi : ∀ i, ∫ y, f i y ∂μ = 1)
    (hn : ∀ i, ∫ y, ‖f i y‖ ∂μ = 1)
    (hs : ∀ δ > 0, ∀ᶠ i in l, Function.support (f i) ⊆ Metric.ball x δ)
    (hK : ContinuousAt K x)
    (hprod : ∀ i, Integrable (fun y => K y * f i y) μ) :
    Tendsto (fun i => ∫ y, K y * f i y ∂μ) l (𝓝 (K x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hK (ε / 2) (by positivity)
  filter_upwards [hs δ hδ] with i hsi
  have hc : Integrable (fun y => K x * f i y) μ := (hf i).const_mul _
  have hci := MeasureTheory.integral_const_mul (μ := μ) (K x) (f i)
  rw [hi i, mul_one] at hci
  have heq : (∫ y, K y * f i y ∂μ) - K x =
      ∫ y, (K y - K x) * f i y ∂μ := by
    calc
      _ = (∫ y, K y * f i y ∂μ) - ∫ y, K x * f i y ∂μ := by
        rw [hci]
      _ = _ := by
        rw [← integral_sub (hprod i) hc]
        congr 1
        ext y
        ring
  have hb (y : X) : ‖(K y - K x) * f i y‖ ≤ ‖f i y‖ * (ε / 2) := by
    by_cases hy : f i y = 0
    · simp [hy]
    · have ht := hclose (hsi hy)
      rw [dist_eq_norm] at ht
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left ht.le (norm_nonneg _)
  rw [dist_eq_norm, heq]
  calc
    ‖∫ y, (K y - K x) * f i y ∂μ‖
        ≤ ∫ y, ‖f i y‖ * (ε / 2) ∂μ :=
      norm_integral_le_of_norm_le ((hf i).norm.mul_const _) (Eventually.of_forall hb)
    _ = ε / 2 := by rw [integral_mul_const, hn, one_mul]
    _ < ε := by linarith

set_option backward.isDefEq.respectTransparency false in
private theorem integral_osConjTensorProduct_one
    {d n m : ℕ} [NeZero d] (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf : ∫ x, f x = 1) (hg : ∫ y, g y = 1) :
    ∫ z, f.osConjTensorProduct g z = 1 := by
  rw [integral_fin_append_split n m _ (SchwartzMap.integrable (f.osConjTensorProduct g))]
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_fin_append_apply,
    SchwartzNPoint.osConj_apply]
  simp_rw [integral_const_mul, hg, mul_one]
  have hinv : Function.Involutive (timeReflectionN d (n := n)) := by
    intro x
    funext i
    exact timeReflection_timeReflection d (x i)
  have hmp := timeReflectionN_measurePreserving (d := d) (n := n)
  rw [hmp.integral_comp
    (MeasurableEquiv.ofInvolutive _ hinv hmp.measurable).measurableEmbedding
    (fun x => starRingEnd ℂ (f x))]
  rw [integral_conj, hf]
  simp

/-- Normalized reflected smearing converges to the literal point kernel over any filter. -/
theorem rToE_reflected_pairing_point_limit
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
      Function.support ((g i).1 : NPointDomain d m → ℂ) ⊆ Metric.ball y δ) :
    Tendsto (fun i => rToEReflectedPairing Wfn (f i) (g i)) l
      (𝓝 (F_ext_on_translatedPET_total Wfn
        (fun j => wickRotatePoint (Fin.append (timeReflectionN d x) y j)))) := by
  let ψ (i : I) := (f i).1.osConjTensorProduct (g i).1
  have hint (i : I) : ∫ z, ψ i z = 1 :=
    integral_osConjTensorProduct_one _ _ (hfi i) (hgi i)
  have hreal (i : I) (z : NPointDomain d (n + m)) : (ψ i z).im = 0 := by
    simp [ψ, SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
      SchwartzNPoint.osConj_apply, Complex.mul_im, hfr, hgr]
  have hnonneg (i : I) (z : NPointDomain d (n + m)) : 0 ≤ (ψ i z).re := by
    simp only [ψ, SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
      SchwartzNPoint.osConj_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      hfr, hgr, neg_zero, mul_zero, sub_zero]
    exact mul_nonneg (hfn _ _) (hgn _ _)
  have hnorm (i : I) : ∫ z, ‖ψ i z‖ = 1 :=
    integral_norm_one_of_nonnegative_real volume _ (SchwartzMap.integrable (ψ i))
      (hnonneg i) (hreal i) (hint i)
  have hsupport : ∀ δ > 0, ∀ᶠ i in l,
      Function.support (ψ i : NPointDomain d (n + m) → ℂ) ⊆
        Metric.ball (Fin.append (timeReflectionN d x) y) δ := by
    intro δ hδ
    have hcont : Continuous (fun p : NPointDomain d n × NPointDomain d m =>
        Fin.append (timeReflectionN d p.1) p.2) := by
      apply continuous_pi
      intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left]
        apply continuous_pi
        intro μ
        simp only [timeReflectionN, timeReflection]
        split_ifs <;> fun_prop
      · rw [show (fun a : NPointDomain d n × NPointDomain d m =>
            Fin.append (timeReflectionN d a.1) a.2 (Fin.natAdd n j)) =
            (fun a => a.2 j) by
          funext a
          exact Fin.append_right ..]
        apply continuous_pi
        intro μ
        fun_prop
    obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := (x,y))) δ hδ
    filter_upwards [hfs η hη, hgs η hη] with i hfi hgi
    intro z hz
    change (f i).1.osConj (splitFirst n m z) * (g i).1 (splitLast n m z) ≠ 0 at hz
    obtain ⟨hzf, hzg⟩ := mul_ne_zero_iff.mp hz
    have hzleft : (f i).1 (timeReflectionN d (splitFirst n m z)) ≠ 0 := by
      simpa only [SchwartzNPoint.osConj_apply, map_ne_zero] using hzf
    have hdist : dist (timeReflectionN d (splitFirst n m z), splitLast n m z) (x,y) < η := by
      exact max_lt (hfi hzleft) (hgi hzg)
    have hc := hclose hdist
    change dist z (Fin.append (timeReflectionN d x) y) < δ
    convert hc using 1
    congr 1
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [timeReflectionN, timeReflection_timeReflection, splitFirst]
    · simp [splitLast]
  have hprod (i : I) : Integrable (fun z : NPointDomain d (n + m) =>
      F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (z j)) * ψ i z) :=
    wick_rotated_kernel_mul_zeroDiagonal_integrable Wfn
      ⟨ψ i, VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (f := (f i).1) (g := (g i).1) (f i).2 (g i).2⟩
  exact tendsto_integral_mul_shrinking_support volume l (fun i => ψ i) _ _
    (fun i => SchwartzMap.integrable (ψ i)) hint hnorm hsupport
    (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
      (reflected_ordered_points_mem_translatedPET x y hx hy)) hprod

/-- The scalar Wick pairing of a normalized ordered point source recovers the kernel. -/
theorem rToE_ordered_wick_pairing_point_limit
    {d n : ℕ} [NeZero d] {I : Type*} (l : Filter I) (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (hx : x ∈ OrderedPositiveTimeRegion d n)
    (f : I → euclideanPositiveTimeSubmodule (d := d) n)
    (hfn : ∀ i z, 0 ≤ ((f i).1 z).re) (hfr : ∀ i z, ((f i).1 z).im = 0)
    (hfi : ∀ i, ∫ z, (f i).1 z = 1)
    (hfs : ∀ δ > 0, ∀ᶠ i in l,
      Function.support ((f i).1 : NPointDomain d n → ℂ) ⊆ Metric.ball x δ) :
    Tendsto (fun i => wickRotatedBoundaryPairing Wfn n (f i).1) l
      (𝓝 (F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (x j)))) := by
  have hnorm (i : I) : ∫ z, ‖(f i).1 z‖ = 1 :=
    integral_norm_one_of_nonnegative_real volume _ (SchwartzMap.integrable (f i).1)
      (hfn i) (hfr i) (hfi i)
  have hprod (i : I) : Integrable (fun z : NPointDomain d n =>
      F_ext_on_translatedPET_total Wfn (fun j => wickRotatePoint (z j)) * (f i).1 z) :=
    wick_rotated_kernel_mul_zeroDiagonal_integrable Wfn
      ⟨(f i).1, VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
        (f := (f i).1) (f i).2⟩
  have hxinj : Function.Injective (fun i => x i 0) :=
    (show StrictMono (fun i => x i 0) from fun i j hij => (hx i).2 j hij).injective
  exact tendsto_integral_mul_shrinking_support volume l (fun i => (f i).1) _ _
    (fun i => SchwartzMap.integrable (f i).1) hfi hnorm hfs
    (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
      (wick_mem_translatedPET_of_time_injective x hxinj)) hprod

/-- Choose compact ordered approximate identities whose supports shrink to the point. -/
theorem exists_normalized_ordered_point_sequence
    {d n : ℕ} [NeZero d] (x : NPointDomain d n)
    (hx : x ∈ OrderedPositiveTimeRegion d n) :
    ∃ f : ℕ → euclideanPositiveTimeSubmodule (d := d) n,
      (∀ i z, 0 ≤ ((f i).1 z).re) ∧ (∀ i z, ((f i).1 z).im = 0) ∧
      (∀ i, ∫ z, (f i).1 z = 1) ∧
      (∀ i, HasCompactSupport ((f i).1 : NPointDomain d n → ℂ)) ∧
      (∀ δ > 0, ∀ᶠ i in atTop,
        Function.support ((f i).1 : NPointDomain d n → ℂ) ⊆ Metric.ball x δ) := by
  choose f hn hr hi hc hs using fun i : ℕ =>
    exists_normalized_ordered_point_bump x hx (1 / ((i : ℝ) + 1)) (by positivity)
  refine ⟨f, hn, hr, hi, hc, ?_⟩
  intro δ hδ
  have ht : ∀ᶠ i : ℕ in atTop, 1 / ((i : ℝ) + 1) < δ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hδ)
  filter_upwards [ht] with i hi
  exact (subset_tsupport _).trans ((hs i).trans (Metric.ball_subset_ball hi.le))

attribute [local irreducible] rToEReflectedPairing

/-- Both approximation indices tend independently to infinity in the reflected seminorm. -/
theorem rToE_reflected_point_sources_cauchy
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (hx : x ∈ OrderedPositiveTimeRegion d n)
    (f : ℕ → euclideanPositiveTimeSubmodule (d := d) n)
    (hfn : ∀ i z, 0 ≤ ((f i).1 z).re) (hfr : ∀ i z, ((f i).1 z).im = 0)
    (hfi : ∀ i, ∫ z, (f i).1 z = 1)
    (hfs : ∀ δ > 0, ∀ᶠ i in atTop,
      Function.support ((f i).1 : NPointDomain d n → ℂ) ⊆ Metric.ball x δ) :
    Tendsto (fun p : ℕ × ℕ =>
      ‖rToEReflectedPairing Wfn (f p.1 - f p.2) (f p.1 - f p.2)‖) atTop (𝓝 0) := by
  have hlim (u v : ℕ × ℕ → ℕ) (hu : Tendsto u atTop atTop) (hv : Tendsto v atTop atTop) :=
    rToE_reflected_pairing_point_limit atTop Wfn x x hx hx
      (fun p => f (u p)) (fun p => f (v p))
      (fun p => hfn (u p)) (fun p => hfn (v p))
      (fun p => hfr (u p)) (fun p => hfr (v p))
      (fun p => hfi (u p)) (fun p => hfi (v p))
      (fun δ hδ => hu.eventually (hfs δ hδ))
      (fun δ hδ => hv.eventually (hfs δ hδ))
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have h := ((hlim Prod.fst Prod.fst hfst hfst).sub
    (hlim Prod.snd Prod.fst hsnd hfst)).sub
    ((hlim Prod.fst Prod.snd hfst hsnd).sub (hlim Prod.snd Prod.snd hsnd hsnd))
  simpa only [rToEReflectedPairing_sub_right, rToEReflectedPairing_sub_left,
    sub_self, norm_zero] using h.norm

end OSReconstruction
