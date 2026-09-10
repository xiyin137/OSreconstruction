/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RealEdgeSeed
















noncomputable section

open Complex Set
open scoped BoundedContinuousFunction Classical

namespace OSReconstruction

/-- Spatial polynomial weight in the OS II Banach norm `(6.19)`. -/
def osiiSpatialPolynomialWeight
    {d k : Nat} (p : Nat) (x : Fin (k * d) -> Real) : Real :=
  (1 + ‖x‖) ^ p

theorem osiiSpatialPolynomialWeight_pos
    {d k p : Nat} (x : Fin (k * d) -> Real) :
    0 < osiiSpatialPolynomialWeight p x := by
  unfold osiiSpatialPolynomialWeight
  positivity

theorem continuous_osiiSpatialPolynomialWeight
    {d k p : Nat} :
    Continuous (osiiSpatialPolynomialWeight (d := d) (k := k) p) := by
  exact (continuous_const.add continuous_norm).pow p

/-- The weighted spatial-function space `B_{k,p}` from OS II `(6.19)`.

An element stores the density after division by its polynomial weight.  The
ambient bounded-continuous-function type supplies the complete normed complex
vector space needed by the later Banach-valued maximum principle. -/
abbrev OSIISpatialPolynomialGrowthFunction
    (d k : Nat) (_p : Nat) :=
  BoundedContinuousFunction (Fin (k * d) -> Real) Complex

namespace OSIISpatialPolynomialGrowthFunction

/-- Reconstruct the polynomially growing spatial function from its weighted
bounded representative. -/
def value
    {d k p : Nat}
    (F : OSIISpatialPolynomialGrowthFunction d k p)
    (x : Fin (k * d) -> Real) : Complex :=
  (osiiSpatialPolynomialWeight p x : Complex) * F x

/-- Package a continuous polynomially bounded function in `B_{k,p}`. -/
def ofFunction
    {d k p : Nat}
    (F : (Fin (k * d) -> Real) -> Complex)
    (hF : Continuous F)
    (C : Real)
    (hbound : forall x,
      ‖F x‖ <= C * osiiSpatialPolynomialWeight p x) :
    OSIISpatialPolynomialGrowthFunction d k p := by
  let weighted : (Fin (k * d) -> Real) -> Complex := fun x =>
    F x / (osiiSpatialPolynomialWeight p x : Complex)
  have hweighted : Continuous weighted := by
    apply hF.div
      (Complex.continuous_ofReal.comp
        continuous_osiiSpatialPolynomialWeight)
    intro x
    exact Complex.ofReal_ne_zero.mpr
      (osiiSpatialPolynomialWeight_pos (p := p) x).ne'
  have hweighted_bound : forall x, ‖weighted x‖ <= C := by
    intro x
    rw [show weighted x =
        F x / (osiiSpatialPolynomialWeight p x : Complex) by rfl,
      norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (osiiSpatialPolynomialWeight_pos (p := p) x)]
    exact (div_le_iff₀ (osiiSpatialPolynomialWeight_pos (p := p) x)).2
      (hbound x)
  exact BoundedContinuousFunction.ofNormedAddCommGroup
    weighted hweighted C hweighted_bound

@[simp] theorem value_ofFunction
    {d k p : Nat}
    (F : (Fin (k * d) -> Real) -> Complex)
    (hF : Continuous F)
    (C : Real)
    (hbound : forall x,
      ‖F x‖ <= C * osiiSpatialPolynomialWeight p x)
    (x : Fin (k * d) -> Real) :
    value (ofFunction F hF C hbound) x = F x := by
  rw [value]
  change (osiiSpatialPolynomialWeight p x : Complex) *
      (F x / (osiiSpatialPolynomialWeight p x : Complex)) = F x
  have hweight :
      (osiiSpatialPolynomialWeight p x : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (osiiSpatialPolynomialWeight_pos (p := p) x).ne'
  field_simp [hweight]

theorem norm_ofFunction_le
    {d k p : Nat}
    (F : (Fin (k * d) -> Real) -> Complex)
    (hF : Continuous F)
    {C : Real} (hC : 0 <= C)
    (hbound : forall x,
      ‖F x‖ <= C * osiiSpatialPolynomialWeight p x) :
    ‖ofFunction F hF C hbound‖ <= C := by
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC
  intro x
  change ‖F x / (osiiSpatialPolynomialWeight p x : Complex)‖ <= C
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (osiiSpatialPolynomialWeight_pos (p := p) x)]
  exact (div_le_iff₀ (osiiSpatialPolynomialWeight_pos (p := p) x)).2
    (hbound x)

theorem norm_value_le
    {d k p : Nat}
    (F : OSIISpatialPolynomialGrowthFunction d k p)
    (x : Fin (k * d) -> Real) :
    ‖value F x‖ <=
      ‖F‖ * osiiSpatialPolynomialWeight p x := by
  rw [value, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (osiiSpatialPolynomialWeight_pos (p := p) x)]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.norm_coe_le_norm F x)
      (osiiSpatialPolynomialWeight_pos (p := p) x).le)

/-- The sharp equation-`(6.29)` spatial-degree comparison.

The geometric mean only needs the sum of the two lower degrees to be at most
twice the target degree.  Requiring each lower degree separately to be at
most the target degree loses the exact arity balance at endpoint splits. -/
theorem sqrt_mul_spatialPolynomialWeight_le_of_norm_le_add_le_two_mul
    {d k a b pLeft pRight pTarget : Nat}
    (xLeft : Fin (a * d) -> Real)
    (xRight : Fin (b * d) -> Real)
    (xTarget : Fin (k * d) -> Real)
    (hp : pLeft + pRight <= 2 * pTarget)
    (hxLeft : ‖xLeft‖ <= ‖xTarget‖)
    (hxRight : ‖xRight‖ <= ‖xTarget‖) :
    Real.sqrt
        (osiiSpatialPolynomialWeight pLeft xLeft *
          osiiSpatialPolynomialWeight pRight xRight) <=
      osiiSpatialPolynomialWeight pTarget xTarget := by
  let W : Real := 1 + ‖xTarget‖
  have hW : 1 <= W := by
    dsimp [W]
    exact le_add_of_nonneg_right (norm_nonneg xTarget)
  have hW_nonneg : 0 <= W := le_trans (by norm_num) hW
  have hleft :
      osiiSpatialPolynomialWeight pLeft xLeft <= W ^ pLeft := by
    unfold osiiSpatialPolynomialWeight
    exact pow_le_pow_left₀ (by positivity)
      (by dsimp [W]; linarith) pLeft
  have hright :
      osiiSpatialPolynomialWeight pRight xRight <= W ^ pRight := by
    unfold osiiSpatialPolynomialWeight
    exact pow_le_pow_left₀ (by positivity)
      (by dsimp [W]; linarith) pRight
  have hproduct :
      osiiSpatialPolynomialWeight pLeft xLeft *
          osiiSpatialPolynomialWeight pRight xRight <=
        (W ^ pTarget) * (W ^ pTarget) := by
    calc
      osiiSpatialPolynomialWeight pLeft xLeft *
          osiiSpatialPolynomialWeight pRight xRight <=
          W ^ pLeft * W ^ pRight :=
        mul_le_mul hleft hright
          (osiiSpatialPolynomialWeight_pos (p := pRight) xRight).le
          (pow_nonneg hW_nonneg _)
      _ = W ^ (pLeft + pRight) := by rw [pow_add]
      _ <= W ^ (2 * pTarget) := pow_le_pow_right₀ hW hp
      _ = (W ^ pTarget) * (W ^ pTarget) := by
        rw [two_mul, pow_add]
  calc
    Real.sqrt
        (osiiSpatialPolynomialWeight pLeft xLeft *
          osiiSpatialPolynomialWeight pRight xRight) <=
        Real.sqrt ((W ^ pTarget) * (W ^ pTarget)) :=
      Real.sqrt_le_sqrt hproduct
    _ = W ^ pTarget := Real.sqrt_mul_self (pow_nonneg hW_nonneg _)
    _ = osiiSpatialPolynomialWeight pTarget xTarget := rfl

/-- Cauchy--Schwarz bounds survive simultaneous recovery of the target and
the two lower pointwise densities.

This is the limit interface between the existing finite-shell/mollifier
estimates and the represented weighted-density successor. -/
theorem norm_le_sqrt_mul_of_tendsto
    {ι E F G : Type*}
    [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup G]
    {l : Filter ι} [l.NeBot]
    (targetApprox : ι -> E)
    (leftApprox : ι -> F)
    (rightApprox : ι -> G)
    (target : E) (left : F) (right : G)
    (htarget : Filter.Tendsto targetApprox l (nhds target))
    (hleft : Filter.Tendsto leftApprox l (nhds left))
    (hright : Filter.Tendsto rightApprox l (nhds right))
    (hbound : ∀ᶠ n in l,
      ‖targetApprox n‖ <=
        Real.sqrt (‖leftApprox n‖ * ‖rightApprox n‖)) :
    ‖target‖ <= Real.sqrt (‖left‖ * ‖right‖) := by
  let orderGraph : Set (Real × Real) := {p | p.1 <= p.2}
  have htargetNorm : Filter.Tendsto
      (fun n => ‖targetApprox n‖) l (nhds ‖target‖) :=
    tendsto_norm.comp htarget
  have hproduct : Filter.Tendsto
      (fun n => ‖leftApprox n‖ * ‖rightApprox n‖) l
      (nhds (‖left‖ * ‖right‖)) :=
    (tendsto_norm.comp hleft).mul (tendsto_norm.comp hright)
  have hsqrt : Filter.Tendsto
      (fun n => Real.sqrt (‖leftApprox n‖ * ‖rightApprox n‖)) l
      (nhds (Real.sqrt (‖left‖ * ‖right‖))) :=
    (Real.continuous_sqrt.tendsto (‖left‖ * ‖right‖)).comp hproduct
  have hpair : Filter.Tendsto
      (fun n =>
        (‖targetApprox n‖,
          Real.sqrt (‖leftApprox n‖ * ‖rightApprox n‖))) l
      (nhds (‖target‖, Real.sqrt (‖left‖ * ‖right‖))) :=
    Filter.Tendsto.prodMk_nhds htargetNorm hsqrt
  have hclosed : IsClosed orderGraph := by
    exact isClosed_le continuous_fst continuous_snd
  exact hclosed.mem_of_tendsto hpair (by
    simpa only [orderGraph, Set.mem_setOf_eq] using hbound)

namespace PointwisePolynomialBoundRecoveryData

end PointwisePolynomialBoundRecoveryData

namespace PointwiseFactorizationRecoveryData

end PointwiseFactorizationRecoveryData

end OSIISpatialPolynomialGrowthFunction

/-- Finite-dimensional spatial-coordinate data for one equation-`(6.29)`
split.

The two lower reflected self-pairings are evaluated on (possibly duplicated
and sign-changed) coordinates selected from the target spatial point.  In the
flat finite-coordinate sup norm, the required geometric fact is exactly that
both selections are contractions. -/
structure OSIIEquation621SpatialSplitData
    (d k a b : Nat) where
  leftPoint : (Fin (k * d) -> Real) -> Fin (a * d) -> Real
  rightPoint : (Fin (k * d) -> Real) -> Fin (b * d) -> Real
  norm_leftPoint_le : forall x, ‖leftPoint x‖ <= ‖x‖
  norm_rightPoint_le : forall x, ‖rightPoint x‖ <= ‖x‖

namespace OSIIEquation621SpatialSplitData

/-- A contractive split preserves the averaged spatial degree required by
equation `(6.29)`. -/
theorem sqrt_mul_weight_le_of_add_le_two_mul
    {d k a b pLeft pRight pTarget : Nat}
    (S : OSIIEquation621SpatialSplitData d k a b)
    (hp : pLeft + pRight <= 2 * pTarget)
    (x : Fin (k * d) -> Real) :
    Real.sqrt
        (osiiSpatialPolynomialWeight pLeft (S.leftPoint x) *
          osiiSpatialPolynomialWeight pRight (S.rightPoint x)) <=
      osiiSpatialPolynomialWeight pTarget x :=
  OSIISpatialPolynomialGrowthFunction.sqrt_mul_spatialPolynomialWeight_le_of_norm_le_add_le_two_mul
    (S.leftPoint x) (S.rightPoint x) x hp
    (S.norm_leftPoint_le x) (S.norm_rightPoint_le x)

end OSIIEquation621SpatialSplitData

namespace OSIITimeContinuationLadderRealEdgeDensityGrowthData

variable {d k : Nat}
variable {L : OSIITimeContinuationLadder d k}

/-- A positive-real weighted density representing a continuation stage.

Unlike `OSIIEquation621WeightedPositiveRealEdgeData`, this structure does not
postulate one bound uniform over the complete positive-real region.  It is the
right raw-stage interface for VI.1: polynomial growth supplies pointwise
bounds, and compactness of the particular cutoff orbit supplies the uniform
constant needed by a rank-zero moving slice. -/
structure OSIIEquation621WeightedPositiveRealRepresentationData
    (A : OSIITimeContinuationStage d k) (p : Nat) where
  density : {tau : Fin k -> Real //
    tau ∈ section43TimeStrictPositiveRegion k} ->
      OSIISpatialPolynomialGrowthFunction d k p
  represents : forall
    (tau : {tau : Fin k -> Real //
      tau ∈ section43TimeStrictPositiveRegion k})
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
    A.distribution (osiiPositiveRealTimeEmbed tau.1) chi =
      ∫ x : Fin (k * d) -> Real,
        OSIISpatialPolynomialGrowthFunction.value (density tau) x *
          (section43SpatialFlatSchwartzCLE d k chi) x

namespace OSIIEquation621WeightedPositiveRealRepresentationData

/-- Transport a represented weighted density across equality of the two
stage distributions on the strict positive-real edge. -/
def ofPositiveRealAgreement
    {A B : OSIITimeContinuationStage d k} {p : Nat}
    (E : OSIIEquation621WeightedPositiveRealRepresentationData A p)
    (agreement : forall
      (tau : {tau : Fin k -> Real //
        tau ∈ section43TimeStrictPositiveRegion k})
      (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
      B.distribution (osiiPositiveRealTimeEmbed tau.1) chi =
        A.distribution (osiiPositiveRealTimeEmbed tau.1) chi) :
    OSIIEquation621WeightedPositiveRealRepresentationData B p where
  density := E.density
  represents := fun tau chi => (agreement tau chi).trans (E.represents tau chi)

end OSIIEquation621WeightedPositiveRealRepresentationData

/-- The unnormalized VI.1 density as an element of the weighted spatial
function space at one strict positive-real time. -/
def positiveRealWeightedDensity
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (p : Nat) (hspatial : D.spatialDegree <= p)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    OSIISpatialPolynomialGrowthFunction d k p :=
  OSIISpatialPolynomialGrowthFunction.ofFunction
    (D.density tau)
    (D.density_continuous tau htau)
    (D.constant *
      (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^ D.timeDegree *
      (1 + (osiiTimeBoundaryDistance k
        (osiiPositiveRealTimeEmbed tau))⁻¹) ^ D.boundaryDegree)
    (fun x => by
      have hzeta :
          osiiPositiveRealTimeEmbed tau ∈ osiiTimeRightHalfPlane k :=
        (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau
      have hdist : 0 < osiiTimeBoundaryDistance k
          (osiiPositiveRealTimeEmbed tau) :=
        osiiTimeBoundaryDistance_pos D.arity_pos hzeta
      have htime :
          0 <= (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^ D.timeDegree := by
        positivity
      have hboundary :
          0 <= (1 + (osiiTimeBoundaryDistance k
            (osiiPositiveRealTimeEmbed tau))⁻¹) ^ D.boundaryDegree := by
        positivity
      have hraw := D.pointwise_bound tau htau x
      have hpow :
          (1 + ‖x‖) ^ D.spatialDegree <= (1 + ‖x‖) ^ p :=
        pow_le_pow_right₀ (by linarith [norm_nonneg x]) hspatial
      exact hraw.trans
        (mul_le_mul_of_nonneg_left hpow
          (mul_nonneg
            (mul_nonneg D.constant_pos.le htime) hboundary)))

@[simp] theorem positiveRealWeightedDensity_value
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (p : Nat) (hspatial : D.spatialDegree <= p)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real) :
    OSIISpatialPolynomialGrowthFunction.value
        (D.positiveRealWeightedDensity p hspatial tau htau) x =
      D.density tau x := by
  exact OSIISpatialPolynomialGrowthFunction.value_ofFunction _ _ _ _ x

/-- The VI.1 density represents the unnormalized exhausted continuation
stage on its complete strict positive-real edge. -/
def toWeightedPositiveRealRepresentationData
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (p : Nat) (hspatial : D.spatialDegree <= p) :
    OSIIEquation621WeightedPositiveRealRepresentationData
      L.toFullTimeContinuationStage p where
  density := fun tau =>
    D.positiveRealWeightedDensity p hspatial tau.1 tau.2
  represents := by
    intro tau chi
    change L.fullDistribution (osiiPositiveRealTimeEmbed tau.1) chi = _
    rw [D.represents tau.1 tau.2 chi]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [D.positiveRealWeightedDensity_value p hspatial tau.1 tau.2 x]

/-- A normalized continuation stage represented on its positive-real edge by
one bounded element of the OS II weighted spatial-function space at every
positive time point. -/
structure OSIIEquation621WeightedPositiveRealEdgeData
    (A : OSIITimeContinuationStage d k) (p : Nat) where
  density : {tau : Fin k -> Real //
    tau ∈ section43TimeStrictPositiveRegion k} ->
      OSIISpatialPolynomialGrowthFunction d k p
  represents : forall
    (tau : {tau : Fin k -> Real //
      tau ∈ section43TimeStrictPositiveRegion k})
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
    A.distribution (osiiPositiveRealTimeEmbed tau.1) chi =
      ∫ x : Fin (k * d) -> Real,
        OSIISpatialPolynomialGrowthFunction.value (density tau) x *
          (section43SpatialFlatSchwartzCLE d k chi) x
  constant : Real
  constant_nonneg : 0 <= constant
  bound : forall tau, ‖density tau‖ <= constant

namespace OSIIEquation621WeightedPositiveRealEdgeData

/-- Forget the global positive-real bound while retaining the represented
weighted density. -/
def toRepresentationData
    {A : OSIITimeContinuationStage d k} {p : Nat}
    (E : OSIIEquation621WeightedPositiveRealEdgeData A p) :
    OSIIEquation621WeightedPositiveRealRepresentationData A p where
  density := E.density
  represents := E.represents

end OSIIEquation621WeightedPositiveRealEdgeData

/-- Banach-valued positive-real equation-`(6.21)` density. -/
def vi2Equation621NormalizedPositiveRealWeightedDensity
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    (hpolynomial : D.timeDegree <= k * t)
    (hboundary : D.boundaryDegree <= k * t)
    (p : Nat) (hspatial : D.spatialDegree <= p)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    OSIISpatialPolynomialGrowthFunction d k p :=
  OSIISpatialPolynomialGrowthFunction.ofFunction
    (D.vi2Equation621NormalizedPositiveRealDensity t epsilon tau)
    (D.continuous_vi2Equation621NormalizedPositiveRealDensity
      t hepsilon tau htau)
    ((k : Real) ^ (2 * (k * t)) * D.constant)
    (fun x => by
      have hraw :=
        D.norm_vi2Equation621NormalizedPositiveRealDensity_le
          t hpolynomial hboundary hepsilon tau htau x
      have hpow :
          (1 + ‖x‖) ^ D.spatialDegree <= (1 + ‖x‖) ^ p :=
        pow_le_pow_right₀ (by linarith [norm_nonneg x]) hspatial
      calc
        ‖D.vi2Equation621NormalizedPositiveRealDensity
            t epsilon tau x‖ <=
          (k : Real) ^ (2 * (k * t)) * D.constant *
            (1 + ‖x‖) ^ D.spatialDegree := hraw
        _ <= (k : Real) ^ (2 * (k * t)) * D.constant *
            (1 + ‖x‖) ^ p :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (by positivity) D.constant_pos.le)
        _ = (k : Real) ^ (2 * (k * t)) * D.constant *
            osiiSpatialPolynomialWeight p x := by
          rfl)

@[simp] theorem vi2Equation621NormalizedPositiveRealWeightedDensity_value
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    (hpolynomial : D.timeDegree <= k * t)
    (hboundary : D.boundaryDegree <= k * t)
    (p : Nat) (hspatial : D.spatialDegree <= p)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real) :
    OSIISpatialPolynomialGrowthFunction.value
        (D.vi2Equation621NormalizedPositiveRealWeightedDensity
          t hpolynomial hboundary p hspatial hepsilon tau htau) x =
      D.vi2Equation621NormalizedPositiveRealDensity t epsilon tau x := by
  exact OSIISpatialPolynomialGrowthFunction.value_ofFunction _ _ _ _ x

theorem norm_vi2Equation621NormalizedPositiveRealWeightedDensity_le
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    (hpolynomial : D.timeDegree <= k * t)
    (hboundary : D.boundaryDegree <= k * t)
    (p : Nat) (hspatial : D.spatialDegree <= p)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    ‖D.vi2Equation621NormalizedPositiveRealWeightedDensity
        t hpolynomial hboundary p hspatial hepsilon tau htau‖ <=
      (k : Real) ^ (2 * (k * t)) * D.constant := by
  apply OSIISpatialPolynomialGrowthFunction.norm_ofFunction_le
  · exact mul_nonneg (by positivity) D.constant_pos.le

/-- The VI.1 pointwise density package supplies the complete weighted
positive-real edge of the normalized equation-`(6.21)` stage. -/
def toVI2Equation621WeightedPositiveRealEdgeData
    (D : OSIITimeContinuationLadderRealEdgeDensityGrowthData L)
    (t : Nat)
    (hpolynomial : D.timeDegree <= k * t)
    (hboundary : D.boundaryDegree <= k * t)
    (p : Nat) (hspatial : D.spatialDegree <= p)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    OSIIEquation621WeightedPositiveRealEdgeData
      (L.toFullTimeContinuationStage.vi2Equation621NormalizedStage
        t epsilon) p where
  density := fun tau =>
    D.vi2Equation621NormalizedPositiveRealWeightedDensity
      t hpolynomial hboundary p hspatial hepsilon tau.1 tau.2
  represents := by
    intro tau chi
    rw [D.vi2Equation621NormalizedPositiveRealDensity_represents
      t hepsilon tau.1 tau.2 chi]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [D.vi2Equation621NormalizedPositiveRealWeightedDensity_value
      t hpolynomial hboundary p hspatial hepsilon tau.1 tau.2 x]
  constant := (k : Real) ^ (2 * (k * t)) * D.constant
  constant_nonneg := mul_nonneg (by positivity) D.constant_pos.le
  bound := by
    intro tau
    exact D.norm_vi2Equation621NormalizedPositiveRealWeightedDensity_le
      t hpolynomial hboundary p hspatial hepsilon tau.1 tau.2

end OSIITimeContinuationLadderRealEdgeDensityGrowthData
end OSReconstruction
