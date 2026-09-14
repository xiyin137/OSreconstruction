/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.Analyticity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedTaylor
















noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Put an increment in the right block and its conjugate in the
reflected-left block. -/
def reflectedCauchyIncrement
    {k : ℕ} (increment : Fin k → ℂ) :
    Fin (k + k) → ℂ :=
  Fin.addCases (fun i => starRingEnd ℂ (increment i)) increment

@[simp] theorem reflectedCauchyIncrement_left
    {k : ℕ} (increment : Fin k → ℂ)
    (i : Fin k) :
    reflectedCauchyIncrement increment (Fin.castAdd k i) =
      starRingEnd ℂ (increment i) := by
  simp [reflectedCauchyIncrement]

@[simp] theorem reflectedCauchyIncrement_right
    {k : ℕ} (increment : Fin k → ℂ)
    (i : Fin k) :
    reflectedCauchyIncrement increment (Fin.natAdd k i) =
      increment i := by
  change
    Fin.addCases (fun j => starRingEnd ℂ (increment j)) increment
        (Fin.natAdd k i) =
      increment i
  rw [Fin.addCases_right]

@[simp] theorem reflectedCauchyIncrement_zero
    {k : ℕ} :
    reflectedCauchyIncrement (0 : Fin k → ℂ) = 0 := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · rw [reflectedCauchyIncrement_left]
    simp
  · rw [reflectedCauchyIncrement_right]
    rfl

/-- Sum an absolutely summable family after collecting all terms with the same
grade. -/
def gradedTsum
    {ι γ E : Type*} [NormedAddCommGroup E]
    (grade : ι → γ) (f : ι → E) (g : γ) : E :=
  ∑' i : {i // grade i ∈ ({g} : Set γ)}, f i

/-- Absolute summability is preserved when terms are collected along the
fibers of an arbitrary grading map. -/
theorem summable_norm_gradedTsum
    {ι γ E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (grade : ι → γ) (f : ι → E)
    (hf : Summable (fun i => ‖f i‖)) :
    Summable (fun g => ‖gradedTsum grade f g‖) := by
  have hfiber :
      Summable (fun g =>
        ∑' i : {i // grade i ∈ ({g} : Set γ)}, ‖f i‖) :=
    (hf.hasSum.tsum_fiberwise grade).summable
  apply Summable.of_norm_bounded hfiber
  intro g
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_tsum_le_tsum_norm (hf.subtype _)

set_option maxHeartbeats 800000 in
/-- A finite product of scalar geometric series is summable over all
multi-indices. -/
private theorem summable_geometric_multiIndex :
    ∀ (n : ℕ) (q : Fin n → ℝ),
      (∀ i, 0 ≤ q i) → (∀ i, q i < 1) →
      Summable (fun α : Fin n → ℕ => ∏ i : Fin n, q i ^ α i) := by
  intro n
  induction n with
  | zero =>
      intro q _ _
      exact (hasSum_fintype _).summable
  | succ n ih =>
      intro q hq hq1
      let qLast := q (Fin.last n)
      let qInit : Fin n → ℝ := fun j => q (Fin.castSucc j)
      have hInit :
          Summable (fun α : Fin n → ℕ => ∏ j, qInit j ^ α j) :=
        ih qInit (fun j => hq _) (fun j => hq1 _)
      have hLast : Summable (fun k : ℕ => qLast ^ k) :=
        summable_geometric_of_lt_one (hq (Fin.last n)) (hq1 (Fin.last n))
      have hProd :
          Summable (fun p : ℕ × (Fin n → ℕ) =>
            qLast ^ p.1 * ∏ j, qInit j ^ p.2 j) :=
        @Summable.mul_of_nonneg ℕ (Fin n → ℕ)
          (fun k => qLast ^ k)
          (fun α => ∏ j, qInit j ^ α j)
          hLast hInit
          (fun k => pow_nonneg (hq _) _)
          (fun α => Finset.prod_nonneg (fun j _ => pow_nonneg (hq _) _))
      refine
        ((Equiv.summable_iff (Fin.snocEquiv (fun _ => ℕ)).symm).mpr hProd).congr
          (fun α => ?_)
      simp only [Function.comp_def, Fin.snocEquiv, Equiv.coe_fn_symm_mk,
        qLast, qInit, Fin.prod_univ_castSucc, mul_comm]
      rfl

/-- Cauchy data on a fixed reflected polydisc, before selecting the increment
at which the Taylor series is evaluated. -/
structure ReflectedCauchyPolydiscData (k : ℕ) where
  scalar : (Fin (k + k) → ℂ) → ℂ
  center : Fin (k + k) → ℂ
  radius : ℝ
  bound : ℝ
  radius_pos : 0 < radius
  bound_nonneg : 0 ≤ bound
  norm_scalar_le :
    ∀ w ∈ SCV.distinguishedBoundary center (fun _ => radius),
      ‖scalar w‖ ≤ bound

/-- Scalar Cauchy coefficient data on a uniform polydisc, evaluated at one
strictly interior increment. -/
structure ReflectedCauchyCoefficientData (k : ℕ) where
  scalar : (Fin (k + k) → ℂ) → ℂ
  center : Fin (k + k) → ℂ
  radius : ℝ
  increment : Fin (k + k) → ℂ
  bound : ℝ
  radius_pos : 0 < radius
  bound_nonneg : 0 ≤ bound
  norm_scalar_le :
    ∀ w ∈ SCV.distinguishedBoundary center (fun _ => radius),
      ‖scalar w‖ ≤ bound
  norm_increment_lt : ∀ i, ‖increment i‖ < radius

namespace ReflectedCauchyCoefficientData

/-- One weighted multi-index Cauchy coefficient at the selected increment. -/
def multiIndexTerm
    {k : ℕ} (D : ReflectedCauchyCoefficientData k)
    (α : Fin (k + k) → ℕ) : ℂ :=
  (∏ i, D.increment i ^ α i) *
    SCV.cauchyCoeffPolydisc D.scalar D.center (fun _ => D.radius) α

/-- The pair of total degrees in the reflected-left and right variable
blocks. -/
def blockDegree
    (k : ℕ) (α : Fin (k + k) → ℕ) : ℕ × ℕ :=
  (∑ i : Fin k, α (Fin.castAdd k i),
    ∑ i : Fin k, α (Fin.natAdd k i))

/-- A multi-index of reflected bidegree `(p,q)` is equivalently a pair of
left and right multi-indices of total degrees `p` and `q`. -/
def blockMultiIndexEquiv (k p q : ℕ) :
    (Finset.Nat.antidiagonalTuple k p) ×
        (Finset.Nat.antidiagonalTuple k q) ≃
      {α : Fin (k + k) → ℕ //
        blockDegree k α ∈ ({(p, q)} : Set (ℕ × ℕ))} where
  toFun ab := ⟨Fin.append ab.1.1 ab.2.1, by
    rw [Set.mem_singleton_iff]
    apply Prod.ext
    · simpa only [blockDegree, Fin.append_left] using
        Finset.Nat.mem_antidiagonalTuple.mp ab.1.2
    · simpa only [blockDegree, Fin.append_right] using
        Finset.Nat.mem_antidiagonalTuple.mp ab.2.2⟩
  invFun α :=
    (⟨fun i => α.1 (Fin.castAdd k i), by
        rw [Finset.Nat.mem_antidiagonalTuple]
        exact congrArg Prod.fst (Set.mem_singleton_iff.mp α.2)⟩,
      ⟨fun i => α.1 (Fin.natAdd k i), by
        rw [Finset.Nat.mem_antidiagonalTuple]
        exact congrArg Prod.snd (Set.mem_singleton_iff.mp α.2)⟩)
  left_inv ab := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  right_inv α := by
    apply Subtype.ext
    exact Fin.addCases_castAdd_natAdd α.1

/-- The scalar Cauchy expansion collected by reflected-left degree `p` and
right degree `q`. -/
def scalarGram
    {k : ℕ} (D : ReflectedCauchyCoefficientData k)
    (p q : ℕ) : ℂ :=
  gradedTsum (blockDegree k) D.multiIndexTerm (p, q)

/-- The abstract graded sum is the expected finite double sum over left and
right multi-indices of the prescribed total degrees. -/
theorem scalarGram_eq_sum_antidiagonalTuple
    {k : ℕ} (D : ReflectedCauchyCoefficientData k) (p q : ℕ) :
    D.scalarGram p q =
      ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
        ∑ β ∈ Finset.Nat.antidiagonalTuple k q,
          D.multiIndexTerm (Fin.append α β) := by
  rw [scalarGram, gradedTsum,
    ← (blockMultiIndexEquiv k p q).tsum_eq
      (fun α => D.multiIndexTerm α)]
  simp only [tsum_fintype, Fintype.sum_prod_type]
  calc
    (∑ α : Finset.Nat.antidiagonalTuple k p,
        ∑ β : Finset.Nat.antidiagonalTuple k q,
          D.multiIndexTerm
            ((blockMultiIndexEquiv k p q) (α, β)).1) =
        ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
          ∑ β : Finset.Nat.antidiagonalTuple k q,
            D.multiIndexTerm (Fin.append α β) := by
      simpa only [blockMultiIndexEquiv] using
        Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple k p)
          (fun α =>
            ∑ β : Finset.Nat.antidiagonalTuple k q,
              D.multiIndexTerm (Fin.append α β))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α hα
      exact
        Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple k q)
          (fun β => D.multiIndexTerm (Fin.append α β))

/-- The weighted scalar Cauchy coefficients are absolutely summable at every
strictly interior increment. -/
theorem summable_norm_multiIndexTerm
    {k : ℕ} (D : ReflectedCauchyCoefficientData k) :
    Summable (fun α : Fin (k + k) → ℕ => ‖D.multiIndexTerm α‖) := by
  let ratio : Fin (k + k) → ℝ :=
    fun i => ‖D.increment i‖ / D.radius
  have hratio_nonneg : ∀ i, 0 ≤ ratio i :=
    fun i => div_nonneg (norm_nonneg _) D.radius_pos.le
  have hratio_lt : ∀ i, ratio i < 1 :=
    fun i => (div_lt_one D.radius_pos).mpr (D.norm_increment_lt i)
  have hgeom :
      Summable (fun α : Fin (k + k) → ℕ =>
        ∏ i, ratio i ^ α i) :=
    summable_geometric_multiIndex _ ratio hratio_nonneg hratio_lt
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun α => ?_)
    (hgeom.mul_left D.bound)
  simp only [multiIndexTerm, norm_mul, norm_prod, norm_pow]
  have hcoeff :=
    SCV.norm_cauchyCoeffPolydisc_le
      D.scalar D.center (fun _ => D.radius)
      (fun _ => D.radius_pos) D.bound D.bound_nonneg D.norm_scalar_le α
  have hdenom_pos : 0 < ∏ i : Fin (k + k), D.radius ^ α i :=
    Finset.prod_pos (fun i _ => pow_pos D.radius_pos _)
  calc
    (∏ i, ‖D.increment i‖ ^ α i) *
          ‖SCV.cauchyCoeffPolydisc D.scalar D.center
            (fun _ => D.radius) α‖
        ≤ (∏ i, ‖D.increment i‖ ^ α i) *
            (D.bound / ∏ i, D.radius ^ α i) :=
      mul_le_mul_of_nonneg_left hcoeff
        (Finset.prod_nonneg (fun i _ => pow_nonneg (norm_nonneg _) _))
    _ = D.bound * ∏ i, ratio i ^ α i := by
      simp only [ratio, div_pow, Finset.prod_div_distrib]
      field_simp [hdenom_pos.ne']

/-- For a nonempty source-parameter block, convergence of the ordinary
total-degree Cauchy power series implies convergence of the corresponding
full multi-index series at the same value. -/
theorem hasSum_multiIndexTerm_of_cauchyPowerSeries
    {q : ℕ} (D : ReflectedCauchyCoefficientData (q + 1)) {value : ℂ}
    (hseries :
      HasSum
        (fun p =>
          SCV.cauchyPowerSeriesPolydisc D.scalar D.center
            (fun _ => D.radius) p (fun _ => D.increment))
        value) :
    HasSum D.multiIndexTerm value := by
  let e :=
    Finset.Nat.sigmaAntidiagonalTupleEquivTuple ((q + 1) + (q + 1))
  have hterms :
      (fun p =>
        SCV.cauchyPowerSeriesPolydisc D.scalar D.center
          (fun _ => D.radius) p (fun _ => D.increment)) =
      (fun p =>
        ∑ α :
            Finset.Nat.antidiagonalTuple ((q + 1) + (q + 1)) p,
          D.multiIndexTerm α.1) := by
    funext p
    calc
      SCV.cauchyPowerSeriesPolydisc D.scalar D.center
          (fun _ => D.radius) p (fun _ => D.increment) =
          ∑ α ∈
              Finset.Nat.antidiagonalTuple ((q + 1) + (q + 1)) p,
            D.multiIndexTerm α := by
        simpa only [multiIndexTerm, smul_eq_mul] using
          SCV.cauchyPowerSeriesPolydisc_apply_diag
            D.scalar D.center (fun _ => D.radius) D.increment p
      _ = ∑ α :
              Finset.Nat.antidiagonalTuple ((q + 1) + (q + 1)) p,
            D.multiIndexTerm α.1 :=
        (Finset.sum_coe_sort
          (Finset.Nat.antidiagonalTuple ((q + 1) + (q + 1)) p)
          D.multiIndexTerm).symm
  have hdegree :
      HasSum
        (fun p =>
          ∑ α :
              Finset.Nat.antidiagonalTuple ((q + 1) + (q + 1)) p,
            D.multiIndexTerm α.1)
        value := by
    rw [← hterms]
    exact hseries
  have hsigma :
      Summable
        (fun a :
            Σ p,
              Finset.Nat.antidiagonalTuple
                ((q + 1) + (q + 1)) p =>
          D.multiIndexTerm a.2.1) :=
    (Equiv.summable_iff e).mpr D.summable_norm_multiIndexTerm.of_norm
  have hsigmaSum :
      HasSum
        (fun a :
            Σ p,
              Finset.Nat.antidiagonalTuple
                ((q + 1) + (q + 1)) p =>
          D.multiIndexTerm a.2.1)
        value := by
    exact HasSum.sigma_of_hasSum hdegree (fun _ => hasSum_fintype _) hsigma
  exact (Equiv.hasSum_iff e).mp hsigmaSum

/-- Regrouping an absolutely convergent reflected Cauchy series by left and
right total degree preserves its sum. -/
theorem hasSum_scalarGram
    {q : ℕ} (D : ReflectedCauchyCoefficientData (q + 1)) {value : ℂ}
    (hseries : HasSum D.multiIndexTerm value) :
    HasSum (fun pq : ℕ × ℕ => D.scalarGram pq.1 pq.2) value := by
  simpa only [scalarGram, gradedTsum] using
    hseries.tsum_fiberwise (blockDegree (q + 1))

/-- Square partial sums of the reflected bidegree expansion converge to the
same value as the full absolutely convergent scalar Gram series. -/
theorem tendsto_square_sum_scalarGram
    {q : ℕ} (D : ReflectedCauchyCoefficientData (q + 1)) {value : ℂ}
    (hseries :
      HasSum (fun pq : ℕ × ℕ => D.scalarGram pq.1 pq.2) value) :
    Filter.Tendsto
      (fun N =>
        ∑ pq ∈ Finset.range N ×ˢ Finset.range N,
          D.scalarGram pq.1 pq.2)
      Filter.atTop (nhds value) := by
  have hsquare :
      Filter.Tendsto
        (fun N : ℕ => Finset.range N ×ˢ Finset.range N)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
    · intro N M hNM
      exact Finset.product_subset_product
        (Finset.range_mono hNM) (Finset.range_mono hNM)
    · intro pq
      refine ⟨max pq.1 pq.2 + 1, ?_⟩
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.lt_succ_iff.mpr (le_max_left _ _),
        Nat.lt_succ_iff.mpr (le_max_right _ _)⟩
  exact hseries.comp hsquare

end ReflectedCauchyCoefficientData

namespace ReflectedCauchyPolydiscData

/-- Package scalar Cauchy data from the minimal quantitative hypothesis: a
bound on the closed polydisc where the Cauchy integral is taken. -/
def ofClosedPolydiscBound
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (norm_scalar_le_on_closedPolydisc :
      ∀ w ∈ SCV.closedPolydisc center (fun _ => radius),
        ‖scalar w‖ ≤ bound) :
    ReflectedCauchyPolydiscData k where
  scalar := scalar
  center := center
  radius := radius
  bound := bound
  radius_pos := radius_pos
  bound_nonneg := bound_nonneg
  norm_scalar_le := by
    intro w hw
    exact norm_scalar_le_on_closedPolydisc w
      (SCV.distinguishedBoundary_subset_closedPolydisc hw)

@[simp] theorem ofClosedPolydiscBound_scalar
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (norm_scalar_le_on_closedPolydisc :
      ∀ w ∈ SCV.closedPolydisc center (fun _ => radius),
        ‖scalar w‖ ≤ bound) :
    (ofClosedPolydiscBound scalar center radius bound radius_pos
      bound_nonneg norm_scalar_le_on_closedPolydisc).scalar = scalar :=
  rfl

@[simp] theorem ofClosedPolydiscBound_center
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (norm_scalar_le_on_closedPolydisc :
      ∀ w ∈ SCV.closedPolydisc center (fun _ => radius),
        ‖scalar w‖ ≤ bound) :
    (ofClosedPolydiscBound scalar center radius bound radius_pos
      bound_nonneg norm_scalar_le_on_closedPolydisc).center = center :=
  rfl

@[simp] theorem ofClosedPolydiscBound_radius
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (norm_scalar_le_on_closedPolydisc :
      ∀ w ∈ SCV.closedPolydisc center (fun _ => radius),
        ‖scalar w‖ ≤ bound) :
    (ofClosedPolydiscBound scalar center radius bound radius_pos
      bound_nonneg norm_scalar_le_on_closedPolydisc).radius = radius :=
  rfl

@[simp] theorem ofClosedPolydiscBound_bound
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (norm_scalar_le_on_closedPolydisc :
      ∀ w ∈ SCV.closedPolydisc center (fun _ => radius),
        ‖scalar w‖ ≤ bound) :
    (ofClosedPolydiscBound scalar center radius bound radius_pos
      bound_nonneg norm_scalar_le_on_closedPolydisc).bound = bound :=
  rfl

/-- Package a scalar holomorphic chart with a bound already known on a
containing domain.  Unlike the compactness-based recentering constructor,
this keeps the caller's numerical bound unchanged, which is essential for
the exact-bound generated-rank induction. -/
def ofDomainBound
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (U : Set (Fin (k + k) → ℂ))
    (closedPolydisc_subset :
      SCV.closedPolydisc center (fun _ => radius) ⊆ U)
    (norm_scalar_le_on_domain :
      ∀ w ∈ U, ‖scalar w‖ ≤ bound) :
    ReflectedCauchyPolydiscData k :=
  ofClosedPolydiscBound scalar center radius bound radius_pos bound_nonneg
    (fun w hw => norm_scalar_le_on_domain w (closedPolydisc_subset hw))

@[simp] theorem ofDomainBound_scalar
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (U : Set (Fin (k + k) → ℂ))
    (closedPolydisc_subset :
      SCV.closedPolydisc center (fun _ => radius) ⊆ U)
    (norm_scalar_le_on_domain :
      ∀ w ∈ U, ‖scalar w‖ ≤ bound) :
    (ofDomainBound scalar center radius bound radius_pos bound_nonneg
      U closedPolydisc_subset norm_scalar_le_on_domain).scalar = scalar :=
  rfl

@[simp] theorem ofDomainBound_center
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (U : Set (Fin (k + k) → ℂ))
    (closedPolydisc_subset :
      SCV.closedPolydisc center (fun _ => radius) ⊆ U)
    (norm_scalar_le_on_domain :
      ∀ w ∈ U, ‖scalar w‖ ≤ bound) :
    (ofDomainBound scalar center radius bound radius_pos bound_nonneg
      U closedPolydisc_subset norm_scalar_le_on_domain).center = center :=
  rfl

@[simp] theorem ofDomainBound_radius
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (U : Set (Fin (k + k) → ℂ))
    (closedPolydisc_subset :
      SCV.closedPolydisc center (fun _ => radius) ⊆ U)
    (norm_scalar_le_on_domain :
      ∀ w ∈ U, ‖scalar w‖ ≤ bound) :
    (ofDomainBound scalar center radius bound radius_pos bound_nonneg
      U closedPolydisc_subset norm_scalar_le_on_domain).radius = radius :=
  rfl

@[simp] theorem ofDomainBound_bound
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (radius bound : ℝ)
    (radius_pos : 0 < radius)
    (bound_nonneg : 0 ≤ bound)
    (U : Set (Fin (k + k) → ℂ))
    (closedPolydisc_subset :
      SCV.closedPolydisc center (fun _ => radius) ⊆ U)
    (norm_scalar_le_on_domain :
      ∀ w ∈ U, ‖scalar w‖ ≤ bound) :
    (ofDomainBound scalar center radius bound radius_pos bound_nonneg
      U closedPolydisc_subset norm_scalar_le_on_domain).bound = bound :=
  rfl

/-- Evaluate fixed reflected-polydisc Cauchy data at one strictly interior
increment. -/
def atIncrement
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    (increment : Fin (k + k) → ℂ)
    (hincrement : ∀ i, ‖increment i‖ < D.radius) :
    ReflectedCauchyCoefficientData k where
  scalar := D.scalar
  center := D.center
  radius := D.radius
  increment := increment
  bound := D.bound
  radius_pos := D.radius_pos
  bound_nonneg := D.bound_nonneg
  norm_scalar_le := D.norm_scalar_le
  norm_increment_lt := hincrement

/-- Point-independent geometric majorant for all weighted Cauchy
multi-index terms whose increments have coordinate norm at most `r`. -/
def multiIndexMajorant
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    (r : ℝ) (α : Fin (k + k) → ℕ) : ℝ :=
  D.bound * ∏ i, (r / D.radius) ^ α i

theorem multiIndexMajorant_nonneg
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r)
    (α : Fin (k + k) → ℕ) :
    0 ≤ D.multiIndexMajorant r α := by
  exact mul_nonneg D.bound_nonneg
    (Finset.prod_nonneg fun i _ =>
      pow_nonneg (div_nonneg hr D.radius_pos.le) _)

/-- The point-independent geometric Cauchy majorant is summable on every
strictly smaller reflected polydisc. -/
theorem summable_multiIndexMajorant
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.radius) :
    Summable (D.multiIndexMajorant r) := by
  have hratio_nonneg : 0 ≤ r / D.radius :=
    div_nonneg hr D.radius_pos.le
  have hratio_lt : r / D.radius < 1 :=
    (div_lt_one D.radius_pos).mpr hrR
  exact
    (summable_geometric_multiIndex (k + k)
      (fun _ => r / D.radius)
      (fun _ => hratio_nonneg)
      (fun _ => hratio_lt)).mul_left D.bound

/-- The norm of every weighted Cauchy term is bounded by the same geometric
majorant throughout a smaller closed polydisc. -/
theorem norm_multiIndexTerm_atIncrement_le
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r)
    (increment : Fin (k + k) → ℂ)
    (hincrement_lt : ∀ i, ‖increment i‖ < D.radius)
    (hincrement_le : ∀ i, ‖increment i‖ ≤ r)
    (α : Fin (k + k) → ℕ) :
    ‖(D.atIncrement increment hincrement_lt).multiIndexTerm α‖ ≤
      D.multiIndexMajorant r α := by
  let E := D.atIncrement increment hincrement_lt
  have hcoeff :=
    SCV.norm_cauchyCoeffPolydisc_le
      D.scalar D.center (fun _ => D.radius)
      (fun _ => D.radius_pos) D.bound D.bound_nonneg D.norm_scalar_le α
  have hdenom_pos : 0 < ∏ i : Fin (k + k), D.radius ^ α i :=
    Finset.prod_pos fun i _ => pow_pos D.radius_pos _
  have hprod :
      (∏ i : Fin (k + k), ‖increment i‖ ^ α i) ≤
        ∏ i : Fin (k + k), r ^ α i := by
    apply Finset.prod_le_prod
    · intro i _
      exact pow_nonneg (norm_nonneg _) _
    · intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (hincrement_le i) _
  simp only [ReflectedCauchyCoefficientData.multiIndexTerm,
    multiIndexMajorant, E, atIncrement, norm_mul, norm_prod, norm_pow]
  calc
    (∏ i, ‖increment i‖ ^ α i) *
          ‖SCV.cauchyCoeffPolydisc D.scalar D.center
            (fun _ => D.radius) α‖
        ≤ (∏ i, ‖increment i‖ ^ α i) *
            (D.bound / ∏ i, D.radius ^ α i) :=
      mul_le_mul_of_nonneg_left hcoeff
        (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
    _ ≤ (∏ i, r ^ α i) *
            (D.bound / ∏ i, D.radius ^ α i) := by
      exact mul_le_mul_of_nonneg_right hprod
        (div_nonneg D.bound_nonneg hdenom_pos.le)
    _ = D.bound * ∏ i, (r / D.radius) ^ α i := by
      simp only [div_pow, Finset.prod_div_distrib]
      field_simp [hdenom_pos.ne']

/-- The geometric majorant collected by reflected left/right total degree. -/
def gradedMajorant
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    (r : ℝ) (pq : ℕ × ℕ) : ℝ :=
  gradedTsum (ReflectedCauchyCoefficientData.blockDegree k)
    (D.multiIndexMajorant r) pq

theorem gradedMajorant_nonneg
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r)
    (pq : ℕ × ℕ) :
    0 ≤ D.gradedMajorant r pq := by
  exact tsum_nonneg fun α => D.multiIndexMajorant_nonneg hr α.1

/-- The degree-collected point-independent majorant remains summable. -/
theorem summable_gradedMajorant
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.radius) :
    Summable (D.gradedMajorant r) := by
  have hmulti_norm :
      Summable (fun α : Fin (k + k) → ℕ =>
        ‖D.multiIndexMajorant r α‖) := by
    convert D.summable_multiIndexMajorant hr hrR using 1
    funext α
    rw [Real.norm_eq_abs, abs_of_nonneg (D.multiIndexMajorant_nonneg hr α)]
  have hgraded :=
    summable_norm_gradedTsum
      (ReflectedCauchyCoefficientData.blockDegree k)
      (D.multiIndexMajorant r) hmulti_norm
  exact hgraded.congr fun pq => by
    change |D.gradedMajorant r pq| = D.gradedMajorant r pq
    exact abs_of_nonneg (D.gradedMajorant_nonneg hr pq)

/-- On a smaller closed polydisc, every reflected scalar Gram coefficient is
bounded by one summable point-independent degree majorant. -/
theorem norm_scalarGram_atIncrement_le_gradedMajorant
    {k : ℕ} (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.radius)
    (increment : Fin (k + k) → ℂ)
    (hincrement_lt : ∀ i, ‖increment i‖ < D.radius)
    (hincrement_le : ∀ i, ‖increment i‖ ≤ r)
    (p q : ℕ) :
    ‖(D.atIncrement increment hincrement_lt).scalarGram p q‖ ≤
      D.gradedMajorant r (p, q) := by
  let E := D.atIncrement increment hincrement_lt
  let fiber :=
    {α : Fin (k + k) → ℕ //
      ReflectedCauchyCoefficientData.blockDegree k α ∈
        ({(p, q)} : Set (ℕ × ℕ))}
  have hterm :
      Summable (fun α : fiber => ‖E.multiIndexTerm α.1‖) :=
    E.summable_norm_multiIndexTerm.subtype _
  have hmajorant :
      Summable (fun α : fiber => D.multiIndexMajorant r α.1) :=
    (D.summable_multiIndexMajorant hr hrR).subtype _
  rw [ReflectedCauchyCoefficientData.scalarGram, gradedMajorant, gradedTsum]
  calc
    ‖∑' α : fiber, E.multiIndexTerm α.1‖ ≤
        ∑' α : fiber, ‖E.multiIndexTerm α.1‖ :=
      norm_tsum_le_tsum_norm hterm
    _ ≤ ∑' α : fiber, D.multiIndexMajorant r α.1 :=
      hterm.tsum_le_tsum
        (fun α =>
          D.norm_multiIndexTerm_atIncrement_le
            hr increment hincrement_lt hincrement_le α.1)
        hmajorant

end ReflectedCauchyPolydiscData

variable {d : ℕ} [NeZero d]

end OSIIChapterV
end OSReconstruction
