import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIParametricFlatTubeBranch

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Total OS-II positive-time variable in flattened time-difference
coordinates.  The upper-half-plane flat coordinates are rotated into the
right-half-plane semigroup parameter by `w ↦ -i w`. -/
def osiiFlatTotalTimeSum {k d : ℕ}
    (u : Fin (k * (d + 1)) → ℂ) : ℂ :=
  ∑ i : Fin k,
    -Complex.I * u (finProdFinEquiv (i, (0 : Fin (d + 1))))

theorem osiiFlatTotalTimeSum_congr {k d : ℕ}
    {u v : Fin (k * (d + 1)) → ℂ}
    (h : ∀ i : Fin k,
      u (finProdFinEquiv (i, (0 : Fin (d + 1)))) =
        v (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiFlatTotalTimeSum (k := k) (d := d) u =
      osiiFlatTotalTimeSum (k := k) (d := d) v := by
  unfold osiiFlatTotalTimeSum
  exact Finset.sum_congr rfl (fun i _ => by rw [h i])

theorem differentiable_osiiFlatTotalTimeSum {k d : ℕ} :
    Differentiable ℂ
      (osiiFlatTotalTimeSum (k := k) (d := d)) := by
  change Differentiable ℂ
    (fun u : Fin (k * (d + 1)) → ℂ =>
      ∑ i : Fin k, -Complex.I *
        u (finProdFinEquiv (i, (0 : Fin (d + 1)))))
  have hterm : ∀ i : Fin k,
      Differentiable ℂ
        (fun u : Fin (k * (d + 1)) → ℂ =>
          -Complex.I * u (finProdFinEquiv (i, (0 : Fin (d + 1))))) := by
    intro i
    simpa only [Pi.mul_apply] using
      (differentiable_const (-Complex.I)).mul
        (differentiable_apply
          (finProdFinEquiv (i, (0 : Fin (d + 1)))) :
          Differentiable ℂ
            (fun u : Fin (k * (d + 1)) → ℂ =>
              u (finProdFinEquiv (i, (0 : Fin (d + 1))))))
  rw [show
      (fun u : Fin (k * (d + 1)) → ℂ =>
        ∑ i : Fin k, -Complex.I *
          u (finProdFinEquiv (i, (0 : Fin (d + 1))))) =
        (∑ i : Fin k,
          (fun u : Fin (k * (d + 1)) → ℂ =>
            -Complex.I *
              u (finProdFinEquiv (i, (0 : Fin (d + 1)))))) by
    funext u
    simp]
  exact Differentiable.sum (u := (Finset.univ : Finset (Fin k)))
    (fun i _ => hterm i)

theorem osiiFlatTotalTimeSum_mem_rightHalfPlane
    {k : ℕ} [Nonempty (Fin k)]
    {u : Fin (k * (d + 1)) → ℂ}
    (hu : u ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) :
    osiiFlatTotalTimeSum (k := k) (d := d) u ∈ {z : ℂ | 0 < z.re} := by
  have hpos : ∀ i : Fin k,
      0 <
        ((-Complex.I) *
          u (finProdFinEquiv (i, (0 : Fin (d + 1))))).re := by
    intro i
    have hi :
        0 < (u (finProdFinEquiv (i, (0 : Fin (d + 1))))).im :=
      (mem_tubeDomain_flatPositiveTimeDiffReal_iff (z := u)).mp hu i
    simpa [Complex.mul_re, Complex.mul_im] using hi
  have hsum :
      0 < ∑ i : Fin k,
        ((-Complex.I) *
          u (finProdFinEquiv (i, (0 : Fin (d + 1))))).re := by
    exact Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  simpa [osiiFlatTotalTimeSum] using hsum

/-- Explicit scalar semigroup candidate on the flattened positive-time
difference tube. -/
def osiiFlatTotalTimeBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} (F G : PositiveTimeBorchersSequence d) :
    (Fin (k * (d + 1)) → ℂ) → ℂ :=
  fun u =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
      (osiiFlatTotalTimeSum (k := k) (d := d) u)

/-- Exponential chart handoff between the OS-II log variables and flattened
time-difference variables.  On the chart `u_i = I * exp r_i`, the rotated
flat total time `∑ -I u_i` is the same semigroup parameter `∑ exp r_i` used
by the log-domain branch. -/
theorem osiiFlatTotalTimeBranch_of_log_time_eq_totalLog
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (u : Fin (k * (d + 1)) → ℂ)
    (r : Fin k → ℂ)
    (htime : ∀ i : Fin k,
      u (finProdFinEquiv (i, (0 : Fin (d + 1)))) =
        Complex.I * Complex.exp (r i)) :
    osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G u =
      osiiTotalLogSemigroupBranch (d := d) OS lgc F G r := by
  unfold osiiFlatTotalTimeBranch osiiTotalLogSemigroupBranch osiiFlatTotalTimeSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [htime i]
  rw [← mul_assoc, neg_mul, Complex.I_mul_I]
  ring

theorem osiiFlatTotalTimeBranch_congr_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} (F G : PositiveTimeBorchersSequence d)
    {u v : Fin (k * (d + 1)) → ℂ}
    (h : ∀ i : Fin k,
      u (finProdFinEquiv (i, (0 : Fin (d + 1)))) =
        v (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiFlatTotalTimeBranch (d := d) OS lgc F G u =
      osiiFlatTotalTimeBranch (d := d) OS lgc F G v := by
  simp [osiiFlatTotalTimeBranch, osiiFlatTotalTimeSum_congr (k := k) (d := d) h]

theorem differentiableOn_osiiFlatTotalTimeBranch_tube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ
      (osiiFlatTotalTimeBranch (d := d) OS lgc F G)
      (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) := by
  exact
    (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G).comp
      (differentiable_osiiFlatTotalTimeSum (k := k) (d := d)).differentiableOn
      (fun u hu => osiiFlatTotalTimeSum_mem_rightHalfPlane (d := d) hu)

theorem isTimeHolomorphicFlatPositiveTimeDiffWitness_osiiFlatTotalTimeBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    (F G : PositiveTimeBorchersSequence d) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness (k := k) (d := d)
      (osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G) := by
  have hdiff :
      DifferentiableOn ℂ
        (osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G)
        (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) :=
    differentiableOn_osiiFlatTotalTimeBranch_tube (d := d) (k := k) OS lgc F G
  refine ⟨hdiff.continuousOn, ?_⟩
  intro z hz i
  let idx : Fin (k * (d + 1)) := finProdFinEquiv (i, (0 : Fin (d + 1)))
  have hupdate_diff :
      Differentiable ℂ (fun w : ℂ => Function.update z idx w) := by
    rw [differentiable_pi]
    intro p
    by_cases hp : p = idx
    · subst hp
      simpa using differentiable_id
    · simpa [Function.update, hp] using differentiable_const (z p)
  have hline_maps :
      Set.MapsTo (fun w : ℂ => Function.update z idx w)
        {w : ℂ | 0 < w.im}
        (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) := by
    intro w hw
    rw [mem_tubeDomain_flatPositiveTimeDiffReal_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [idx, Function.update] using hw
    · have hzj :
          0 < (z (finProdFinEquiv (j, (0 : Fin (d + 1))))).im :=
        (mem_tubeDomain_flatPositiveTimeDiffReal_iff (z := z)).mp hz j
      have hidx_ne :
          finProdFinEquiv (j, (0 : Fin (d + 1))) ≠ idx := by
        intro hidx
        exact hji (congrArg Prod.fst (finProdFinEquiv.injective hidx))
      simpa [idx, Function.update, hidx_ne] using hzj
  simpa [idx] using hdiff.comp hupdate_diff.differentiableOn hline_maps

/-- Spatial slices of the explicit total-time branch are holomorphic because
the branch depends only on flattened time coordinates. -/
theorem differentiableOn_osiiFlatTotalTimeBranch_spatial_slice
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    (F G : PositiveTimeBorchersSequence d)
    (z : Fin (k * (d + 1)) → ℂ)
    (i : Fin k) (μ : Fin (d + 1)) (hμ : μ ≠ 0) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G
          (Function.update z (finProdFinEquiv (i, μ)) w))
      Set.univ := by
  have hconst :
      (fun w : ℂ =>
        osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G
          (Function.update z (finProdFinEquiv (i, μ)) w)) =
        fun _ : ℂ =>
          osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G z := by
    funext w
    apply osiiFlatTotalTimeBranch_congr_time (d := d) OS lgc F G
    intro j
    have hidx_ne :
        finProdFinEquiv (j, (0 : Fin (d + 1))) ≠ finProdFinEquiv (i, μ) := by
      intro hidx
      have hcoord := congrArg Prod.snd (finProdFinEquiv.injective hidx)
      exact hμ hcoord.symm
    simp [Function.update, hidx_ne]
  rw [hconst]
  exact differentiableOn_const _

theorem differentiableOn_acrOne_osiiFlatTotalTimeBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ
      (fun z : Fin k → Fin (d + 1) → ℂ =>
        osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G
          (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  exact
    (differentiableOn_osiiFlatTotalTimeBranch_tube
      (d := d) (k := k) OS lgc F G).comp
      (differentiable_toDiffFlat_local k d).differentiableOn
      (fun z hz => (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff z).mp hz)

/-- After passing to difference coordinates, the explicit total-time flat
branch is invariant under common translations whose time component is zero.

This records the spatial part of common-translation covariance already carried
by the flat semigroup branch.  The common time-translation direction is not
settled by this raw total-time carrier. -/
theorem osiiFlatTotalTimeBranch_toDiffFlat_spatial_translation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (z : Fin k → Fin (d + 1) → ℂ)
    (a : Fin (d + 1) → ℂ)
    (ha : a 0 = 0) :
    osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G
        (BHW.toDiffFlat k d (fun j μ => z j μ + a μ)) =
      osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G
        (BHW.toDiffFlat k d z) := by
  apply osiiFlatTotalTimeBranch_congr_time (d := d) OS lgc F G
  intro i
  unfold BHW.toDiffFlat BHW.flattenCfg
  rw [BHW.diffCoordEquiv_apply, BHW.diffCoordEquiv_apply]
  by_cases hi : i.val = 0
  · simp [hi, ha]
  · simp [hi, ha]

/-! ### Real-edge common time transport -/

/-- OS `E1` real-edge transport for a common positive Euclidean time shift.

The raw total-time flat carrier is not invariant in this direction.  Instead,
on the real Wick edge the common time shift is transferred to the left
positive-time vector by the OS semigroup algebra.  This is the real-edge
transport step that precedes the later source-current/delta lift in the
OS II Chapter V construction. -/
theorem OSInnerProduct_left_timeShift_real_edge_transport
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (τ : Fin m → ℝ) (hτ : ∀ p : Fin m, 0 < τ p)
    (a : ℝ) (ha : 0 ≤ a) :
    OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha F : BorchersSequence d)
        (timeShiftBorchers (d := d) (∑ p : Fin m, τ p) (G : BorchersSequence d)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (a + ∑ p : Fin m, τ p)
          (G : BorchersSequence d)) := by
  have hsum_pos : 0 < ∑ p : Fin m, τ p := by
    exact Finset.sum_pos (fun p _ => hτ p) Finset.univ_nonempty
  have htotal_nonneg : 0 ≤ a + ∑ p : Fin m, τ p := by
    exact add_nonneg ha (le_of_lt hsum_pos)
  have hleft :
      OSTensorAdmissible d
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha F : BorchersSequence d)
        (timeShiftBorchers (d := d) (∑ p : Fin m, τ p) (G : BorchersSequence d)) := by
    simpa [timeShiftNonnegPositiveTimeBorchers_toBorchersSequence] using
      PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha F)
        (timeShiftNonnegPositiveTimeBorchers
          (d := d) (∑ p : Fin m, τ p) (le_of_lt hsum_pos) G)
  have hright :
      OSTensorAdmissible d (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (a + ∑ p : Fin m, τ p)
          (G : BorchersSequence d)) := by
    simpa [timeShiftNonnegPositiveTimeBorchers_toBorchersSequence] using
      PositiveTimeBorchersSequence.ostensorAdmissible (d := d) F
        (timeShiftNonnegPositiveTimeBorchers
          (d := d) (a + ∑ p : Fin m, τ p) htotal_nonneg G)
  exact
    OSInnerProduct_timeShift_eq (d := d) OS
      (F : BorchersSequence d) (G : BorchersSequence d)
      (∑ p : Fin m, τ p) a hleft hright

/-- Common Euclidean time shift of all points in an ordered real edge. -/
def commonTimeShiftConfig {k : ℕ}
    (x : NPointDomain d k) (a : ℝ) : NPointDomain d k :=
  fun j => x j + timeShiftVec d a

theorem commonTimeShiftConfig_ordered
    {k : ℕ} {x : NPointDomain d k}
    (hx : x ∈ OrderedPositiveTimeRegion d k)
    {a : ℝ} (ha : 0 ≤ a) :
    commonTimeShiftConfig (d := d) x a ∈
      OrderedPositiveTimeRegion d k := by
  intro i
  constructor
  · have hxi : 0 < x i 0 := (hx i).1
    simp [commonTimeShiftConfig, timeShiftVec]
    linarith
  · intro j hij
    have hlt : x i 0 < x j 0 := (hx i).2 j hij
    simpa [commonTimeShiftConfig, timeShiftVec] using hlt

theorem commonTimeShiftConfig_last_time
    {k : ℕ} (x : NPointDomain d (k + 1)) (a : ℝ) :
    commonTimeShiftConfig (d := d) x a (Fin.last k) 0 =
      x (Fin.last k) 0 + a := by
  simp [commonTimeShiftConfig, timeShiftVec]

/-- On the positive imaginary time-difference edge, the flat branch recovers
the positive real-time OS semigroup matrix element at the total time. -/
theorem osiiFlatTotalTimeBranch_positive_imag_time_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (u : Fin (k * (d + 1)) → ℂ)
    (η : Fin k → ℝ)
    (hη_pos : ∀ i : Fin k, 0 < η i)
    (hu_time : ∀ i : Fin k,
      u (finProdFinEquiv (i, (0 : Fin (d + 1)))) =
        (η i : ℂ) * Complex.I) :
    osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G u =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (∑ i : Fin k, η i)
          (G : BorchersSequence d)) := by
  have hsum :
      osiiFlatTotalTimeSum (k := k) (d := d) u =
        ((∑ i : Fin k, η i) : ℂ) := by
    unfold osiiFlatTotalTimeSum
    calc
      (∑ i : Fin k,
        -Complex.I *
          u (finProdFinEquiv (i, (0 : Fin (d + 1))))) =
          ∑ i : Fin k, (η i : ℂ) := by
            exact Finset.sum_congr rfl (fun i _ => by
              rw [hu_time i]
              apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im])
      _ = ((∑ i : Fin k, η i) : ℂ) := by simp
  have hsum_pos : 0 < ∑ i : Fin k, η i := by
    exact Finset.sum_pos (fun i _ => hη_pos i) Finset.univ_nonempty
  rw [osiiFlatTotalTimeBranch, hsum]
  simpa using
    OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) OS lgc F G hG_compact (∑ i : Fin k, η i) hsum_pos

/-- Concentrated left/right Borchers scalarization of the positive imaginary
time-difference edge: the flat branch is the Schwinger functional of the
OS-conjugated simple tensor with the right factor shifted by the total
positive time. -/
theorem osiiFlatTotalTimeBranch_single_positive_imag_time_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (u : Fin (k * (d + 1)) → ℂ)
    (η : Fin k → ℝ)
    (hη_pos : ∀ i : Fin k, 0 < η i)
    (hu_time : ∀ i : Fin k,
      u (finProdFinEquiv (i, (0 : Fin (d + 1)))) =
        (η i : ℂ) * Complex.I) :
    osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) u =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ i : Fin k, η i) g))) := by
  have hG_compact :
      ∀ r,
        HasCompactSupport (((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ)) := by
    intro r
    by_cases hr : r = m
    · subst hr
      simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
    · have hzero :
        ((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hr]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d r → ℂ))
  calc
    osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) u =
      OSInnerProduct d OS.S
        ((PositiveTimeBorchersSequence.single n f hf_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d)
        (timeShiftBorchers (d := d) (∑ i : Fin k, η i)
          ((PositiveTimeBorchersSequence.single m g hg_ord :
            PositiveTimeBorchersSequence d) : BorchersSequence d)) := by
        exact
          osiiFlatTotalTimeBranch_positive_imag_time_edge_eq_total
            (d := d) (OS := OS) (lgc := lgc)
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single m g hg_ord)
            hG_compact u η hη_pos hu_time
    _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ i : Fin k, η i) g))) := by
        simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
          OSInnerProduct_single_right_timeShift
            (d := d) OS f g (∑ i : Fin k, η i)

/-- Successive Euclidean time differences, with the first point measured from
the OS vacuum time `0`. -/
def osiiOrderedPositiveTimeDiff {k d : ℕ}
    (x : NPointDomain d k) : Fin k → ℝ :=
  fun i =>
    if h : i.val = 0 then x i 0
    else x i 0 - x ⟨i.val - 1, by omega⟩ 0

theorem osiiOrderedPositiveTimeDiff_pos_of_mem_orderedPositive
    {k : ℕ} {x : NPointDomain d k}
    (hx : x ∈ OrderedPositiveTimeRegion d k) :
    ∀ i : Fin k, 0 < osiiOrderedPositiveTimeDiff (d := d) x i := by
  intro i
  unfold osiiOrderedPositiveTimeDiff
  by_cases hi : i.val = 0
  · simpa [hi] using (hx i).1
  · have hpred_lt : (⟨i.val - 1, by omega⟩ : Fin k) < i := by
      change i.val - 1 < i.val
      omega
    have hlt : x ⟨i.val - 1, by omega⟩ 0 < x i 0 :=
      (hx ⟨i.val - 1, by omega⟩).2 i hpred_lt
    simpa [hi, sub_pos] using hlt

/-- The successive positive-time differences telescope to the final Euclidean
time coordinate. -/
theorem osiiOrderedPositiveTimeDiff_sum_eq_last
    {k : ℕ} (x : NPointDomain d (k + 1)) :
    (∑ i : Fin (k + 1), osiiOrderedPositiveTimeDiff (d := d) x i) =
      x (Fin.last k) 0 := by
  induction k with
  | zero =>
      simp [osiiOrderedPositiveTimeDiff]
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      let x0 : NPointDomain d (k + 1) := fun i => x (Fin.castSucc i)
      have hprefix :
          (∑ i : Fin (k + 1),
              osiiOrderedPositiveTimeDiff (d := d) x (Fin.castSucc i)) =
            ∑ i : Fin (k + 1), osiiOrderedPositiveTimeDiff (d := d) x0 i := by
        apply Finset.sum_congr rfl
        intro i _
        unfold osiiOrderedPositiveTimeDiff
        by_cases hi : i.val = 0
        · simp [x0, hi]
        · simp [x0, hi]
      rw [hprefix, ih x0]
      have hlast_cast :
          x0 (Fin.last k) 0 = x (Fin.castSucc (Fin.last k)) 0 := rfl
      rw [hlast_cast]
      have hprev :
          (Fin.castSucc (Fin.last k) : Fin (k + 2)) = ⟨k, by omega⟩ := by
        ext
        simp
      simp [osiiOrderedPositiveTimeDiff, hprev]

theorem toDiffFlat_wickRotate_time_eq_I_mul_orderedTimeDiff
    {k : ℕ} (x : NPointDomain d k) (i : Fin k) :
    BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))
        (finProdFinEquiv (i, (0 : Fin (d + 1)))) =
      (osiiOrderedPositiveTimeDiff (d := d) x i : ℂ) * Complex.I := by
  unfold BHW.toDiffFlat BHW.flattenCfg
  rw [BHW.diffCoordEquiv_apply]
  unfold osiiOrderedPositiveTimeDiff
  by_cases hi : i.val = 0
  · simp [hi, wickRotatePoint, mul_comm]
  · simp [hi, wickRotatePoint]
    ring

theorem osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ} [Nonempty (Fin k)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : NPointDomain d k)
    (hx : x ∈ OrderedPositiveTimeRegion d k) :
    osiiFlatTotalTimeBranch (d := d) (k := k) OS lgc F G
        (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ i : Fin k, osiiOrderedPositiveTimeDiff (d := d) x i)
          (G : BorchersSequence d)) := by
  exact
    osiiFlatTotalTimeBranch_positive_imag_time_edge_eq_total
      (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G)
      hG_compact
      (u := BHW.toDiffFlat k d (fun j => wickRotatePoint (x j)))
      (η := osiiOrderedPositiveTimeDiff (d := d) x)
      (osiiOrderedPositiveTimeDiff_pos_of_mem_orderedPositive (d := d) hx)
      (toDiffFlat_wickRotate_time_eq_I_mul_orderedTimeDiff (d := d) x)

/-- Telescoped form of the ordered Wick-rotated real edge: for `k+1`
Euclidean points, the total positive-time shift is the last time coordinate. -/
theorem osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_last_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : NPointDomain d (k + 1))
    (hx : x ∈ OrderedPositiveTimeRegion d (k + 1)) :
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc F G
        (BHW.toDiffFlat (k + 1) d (fun j => wickRotatePoint (x j))) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (x (Fin.last k) 0)
          (G : BorchersSequence d)) := by
  simpa [osiiOrderedPositiveTimeDiff_sum_eq_last (d := d) x] using
    osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_total
      (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G)
      hG_compact x hx

/-- Real Wick-edge form of common-time transport for the flat OS-II branch.

Shifting every Euclidean time by a nonnegative `a` changes the raw total-time
branch exactly by moving that `a` onto the left OS vector.  This is the
book-faithful replacement for the false shortcut that the raw carrier is
already common-time-translation invariant. -/
theorem osiiFlatTotalTimeBranch_wickRotate_common_time_edge_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : NPointDomain d (k + 1))
    (hx : x ∈ OrderedPositiveTimeRegion d (k + 1))
    (a : ℝ) (ha : 0 ≤ a) :
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc F G
        (BHW.toDiffFlat (k + 1) d
          (fun j => wickRotatePoint
            (commonTimeShiftConfig (d := d) x a j))) =
      OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha F : BorchersSequence d)
        (timeShiftBorchers (d := d) (x (Fin.last k) 0)
          (G : BorchersSequence d)) := by
  have hxa :
      commonTimeShiftConfig (d := d) x a ∈
        OrderedPositiveTimeRegion d (k + 1) :=
    commonTimeShiftConfig_ordered (d := d) hx ha
  have hraw :
      osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc F G
          (BHW.toDiffFlat (k + 1) d
            (fun j => wickRotatePoint
              (commonTimeShiftConfig (d := d) x a j))) =
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (commonTimeShiftConfig (d := d) x a (Fin.last k) 0)
            (G : BorchersSequence d)) :=
    osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_last_time
      (d := d) (OS := OS) (lgc := lgc) F G hG_compact
      (commonTimeShiftConfig (d := d) x a) hxa
  have hxlast_pos : 0 < x (Fin.last k) 0 := (hx (Fin.last k)).1
  have htransport :=
    OSInnerProduct_left_timeShift_real_edge_transport
      (d := d) OS F G (fun _ : Fin 1 => x (Fin.last k) 0)
      (fun _ => hxlast_pos) a ha
  have hsum_one :
      (∑ p : Fin 1, (fun _ : Fin 1 => x (Fin.last k) 0) p) =
        x (Fin.last k) 0 := by
    simp
  calc
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc F G
        (BHW.toDiffFlat (k + 1) d
          (fun j => wickRotatePoint
            (commonTimeShiftConfig (d := d) x a j))) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (x (Fin.last k) 0 + a)
          (G : BorchersSequence d)) := by
        rw [hraw, commonTimeShiftConfig_last_time]
    _ =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (a + x (Fin.last k) 0)
          (G : BorchersSequence d)) := by
        congr 2
        ring
    _ =
      OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha F : BorchersSequence d)
        (timeShiftBorchers (d := d) (x (Fin.last k) 0)
          (G : BorchersSequence d)) := by
        simpa [hsum_one] using htransport.symm

/-- Concentrated scalarization of the common-time transported ordered real
edge.  After the OS `E1` transport, the common nonnegative time shift is
absorbed into the left tensor factor, while the right tensor retains the
telescoped final-time shift. -/
theorem osiiFlatTotalTimeBranch_single_wickRotate_common_time_edge_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (x : NPointDomain d (k + 1))
    (hx : x ∈ OrderedPositiveTimeRegion d (k + 1))
    (a : ℝ) (ha : 0 ≤ a) :
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d
          (fun j => wickRotatePoint (commonTimeShiftConfig (d := d) x a j))) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := by
  have hG_compact :
      ∀ r,
        HasCompactSupport (((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ)) := by
    intro r
    by_cases hr : r = m
    · subst hr
      simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
    · have hzero :
        ((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hr]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d r → ℂ))
  calc
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d
          (fun j => wickRotatePoint (commonTimeShiftConfig (d := d) x a j))) =
      OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
          (PositiveTimeBorchersSequence.single n f hf_ord) : BorchersSequence d)
        (timeShiftBorchers (d := d) (x (Fin.last k) 0)
          ((PositiveTimeBorchersSequence.single m g hg_ord :
            PositiveTimeBorchersSequence d) : BorchersSequence d)) := by
        exact
          osiiFlatTotalTimeBranch_wickRotate_common_time_edge_transport
            (d := d) (OS := OS) (lgc := lgc)
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single m g hg_ord)
            hG_compact x hx a ha
    _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := by
        have hleft_shift :
            ∀ r,
              (timeShiftBorchers (d := d) a (BorchersSequence.single n f)).funcs r =
                (BorchersSequence.single n
                  (timeShiftSchwartzNPoint (d := d) a f)).funcs r := by
          intro r
          by_cases hr : r = n
          · subst hr
            simp [BorchersSequence.single]
          · simp [BorchersSequence.single, hr]
        have hcongr :
            OSInnerProduct d OS.S
                (timeShiftBorchers (d := d) a (BorchersSequence.single n f))
                (timeShiftBorchers (d := d) (x (Fin.last k) 0)
                  (BorchersSequence.single m g)) =
              OSInnerProduct d OS.S
                (BorchersSequence.single n
                  (timeShiftSchwartzNPoint (d := d) a f))
                (timeShiftBorchers (d := d) (x (Fin.last k) 0)
                  (BorchersSequence.single m g)) := by
          exact OSInnerProduct_congr_left (d := d) OS.S OS.E0_linear
            (timeShiftBorchers (d := d) a (BorchersSequence.single n f))
            (BorchersSequence.single n (timeShiftSchwartzNPoint (d := d) a f))
            (timeShiftBorchers (d := d) (x (Fin.last k) 0)
              (BorchersSequence.single m g)) hleft_shift
        calc
          OSInnerProduct d OS.S
              (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
                (PositiveTimeBorchersSequence.single n f hf_ord) : BorchersSequence d)
              (timeShiftBorchers (d := d) (x (Fin.last k) 0)
                ((PositiveTimeBorchersSequence.single m g hg_ord :
                  PositiveTimeBorchersSequence d) : BorchersSequence d)) =
            OSInnerProduct d OS.S
                (timeShiftBorchers (d := d) a (BorchersSequence.single n f))
                (timeShiftBorchers (d := d) (x (Fin.last k) 0)
                  (BorchersSequence.single m g)) := by
              rfl
          _ =
            OSInnerProduct d OS.S
                (BorchersSequence.single n
                  (timeShiftSchwartzNPoint (d := d) a f))
                (timeShiftBorchers (d := d) (x (Fin.last k) 0)
                  (BorchersSequence.single m g)) := hcongr
          _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
              ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := by
              exact OSInnerProduct_single_right_timeShift
                (d := d) OS (timeShiftSchwartzNPoint (d := d) a f) g
                (x (Fin.last k) 0)

/-- Concentrated scalarization of the telescoped ordered real edge.  The
coordinate edge may have any positive number of time differences; the branch
only sees their total, which telescopes to the final Euclidean time. -/
theorem osiiFlatTotalTimeBranch_single_wickRotate_ordered_edge_eq_schwinger_last_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (x : NPointDomain d (k + 1))
    (hx : x ∈ OrderedPositiveTimeRegion d (k + 1)) :
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d (fun j => wickRotatePoint (x j))) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := by
  have hG_compact :
      ∀ r,
        HasCompactSupport (((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ)) := by
    intro r
    by_cases hr : r = m
    · subst hr
      simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
    · have hzero :
        ((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hr]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d r → ℂ))
  calc
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d (fun j => wickRotatePoint (x j))) =
      OSInnerProduct d OS.S
        ((PositiveTimeBorchersSequence.single n f hf_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d)
        (timeShiftBorchers (d := d) (x (Fin.last k) 0)
          ((PositiveTimeBorchersSequence.single m g hg_ord :
            PositiveTimeBorchersSequence d) : BorchersSequence d)) := by
        exact
          osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_last_time
            (d := d) (OS := OS) (lgc := lgc)
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single m g hg_ord)
            hG_compact x hx
    _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := by
        simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
          OSInnerProduct_single_right_timeShift
            (d := d) OS f g (x (Fin.last k) 0)

theorem timeShiftSchwartzNPoint_zero_eq
    (a : ℝ) (f : SchwartzNPoint d 0) :
    timeShiftSchwartzNPoint (d := d) a f = f := by
  ext y
  rw [timeShiftSchwartzNPoint_apply]
  congr 1
  ext i
  exact Fin.elim0 i

/-- On a vacuum-left real edge the common nonnegative time shift is invisible:
the OS `E1` transport moves it to the zero-point left factor, where time
translation acts trivially. -/
theorem osiiFlatTotalTimeBranch_vacuumLeft_wickRotate_common_time_edge_invariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k m : ℕ}
    (f0 : SchwartzNPoint d 0)
    (hf0_ord : tsupport (f0 : NPointDomain d 0 → ℂ) ⊆
      OrderedPositiveTimeRegion d 0)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (x : NPointDomain d (k + 1))
    (hx : x ∈ OrderedPositiveTimeRegion d (k + 1))
    (a : ℝ) (ha : 0 ≤ a) :
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single 0 f0 hf0_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d
          (fun j => wickRotatePoint (commonTimeShiftConfig (d := d) x a j))) =
      osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single 0 f0 hf0_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d (fun j => wickRotatePoint (x j))) := by
  have hshift0 :
      timeShiftSchwartzNPoint (d := d) a f0 = f0 :=
    timeShiftSchwartzNPoint_zero_eq (d := d) a f0
  have hleft :=
    osiiFlatTotalTimeBranch_single_wickRotate_common_time_edge_eq_schwinger
      (d := d) (OS := OS) (lgc := lgc)
      (k := k) (n := 0) (m := m)
      f0 hf0_ord g hg_ord hg_compact x hx a ha
  have hright :=
    osiiFlatTotalTimeBranch_single_wickRotate_ordered_edge_eq_schwinger_last_time
      (d := d) (OS := OS) (lgc := lgc)
      (k := k) (n := 0) (m := m)
      f0 hf0_ord g hg_ord hg_compact x hx
  calc
    osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single 0 f0 hf0_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d
          (fun j => wickRotatePoint (commonTimeShiftConfig (d := d) x a j))) =
      OS.S (0 + m) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f0).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := hleft
    _ = OS.S (0 + m) (ZeroDiagonalSchwartz.ofClassical
        (f0.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x (Fin.last k) 0) g))) := by
        rw [hshift0]
    _ =
      osiiFlatTotalTimeBranch (d := d) (k := k + 1) OS lgc
        (PositiveTimeBorchersSequence.single 0 f0 hf0_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (k + 1) d (fun j => wickRotatePoint (x j))) := hright.symm

/-- Concentrated left/right Borchers scalarization of the flat branch real edge:
on ordered Wick-rotated Euclidean configurations, the flat branch is the
Schwinger functional of the OS-conjugated simple tensor with the right factor
shifted by the total positive time. -/
theorem osiiFlatTotalTimeBranch_single_wickRotate_ordered_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} [Nonempty (Fin (n + m))]
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (x : NPointDomain d (n + m))
    (hx : x ∈ OrderedPositiveTimeRegion d (n + m)) :
    osiiFlatTotalTimeBranch (d := d) (k := n + m) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (n + m) d (fun j => wickRotatePoint (x j))) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ i : Fin (n + m), osiiOrderedPositiveTimeDiff (d := d) x i)
            g))) := by
  let T : ℝ := ∑ i : Fin (n + m), osiiOrderedPositiveTimeDiff (d := d) x i
  have hG_compact :
      ∀ r,
        HasCompactSupport (((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ)) := by
    intro r
    by_cases hr : r = m
    · subst hr
      simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
    · have hzero :
        ((((PositiveTimeBorchersSequence.single m g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs r :
          SchwartzNPoint d r) : NPointDomain d r → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hr]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d r → ℂ))
  calc
    osiiFlatTotalTimeBranch (d := d) (k := n + m) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (BHW.toDiffFlat (n + m) d (fun j => wickRotatePoint (x j))) =
      OSInnerProduct d OS.S
        ((PositiveTimeBorchersSequence.single n f hf_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d)
        (timeShiftBorchers (d := d) T
          ((PositiveTimeBorchersSequence.single m g hg_ord :
            PositiveTimeBorchersSequence d) : BorchersSequence d)) := by
        simpa [T] using
          osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_total
            (d := d) (OS := OS) (lgc := lgc)
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single m g hg_ord)
            hG_compact x hx
    _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) T g))) := by
        simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
          OSInnerProduct_single_right_timeShift (d := d) OS f g T

end OSReconstruction
