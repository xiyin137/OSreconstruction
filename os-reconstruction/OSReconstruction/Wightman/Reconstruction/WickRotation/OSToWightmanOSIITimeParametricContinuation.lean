import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent

/-!
# OS-II Time-Parametric Continuation

OS II continues the time-difference variables while treating the spatial
variables distributionally.  This file records that analytic object directly,
without upgrading it to a scalar function on unrestricted complex spatial
coordinates.

The stage ladder below separates three obligations:

* each stage is an open time domain carrying a weakly holomorphic family of
  spatial distributions;
* consecutive stages agree on the earlier domain;
* the increasing domains exhaust the product right half-plane.

Once those obligations are proved, the stage families glue to one weakly
holomorphic continuation on the full time domain.
-/

noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

/-- The complexified finite family of Euclidean time gaps. -/
abbrev OSIITimeGapSpace (k : ℕ) := Fin k → ℂ

/-- The product right half-plane `C₊^k` used in OS II Chapter V. -/
def osiiTimeRightHalfPlane (k : ℕ) : Set (OSIITimeGapSpace k) :=
  {ζ | ∀ i : Fin k, 0 < (ζ i).re}

theorem isOpen_osiiTimeRightHalfPlane (k : ℕ) :
    IsOpen (osiiTimeRightHalfPlane k) := by
  simp only [osiiTimeRightHalfPlane, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i : Fin k =>
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_apply i))

/-- Positive real time gaps embedded in the OS-II complex time domain. -/
def osiiPositiveRealTimeEmbed {k : ℕ} (τ : Fin k → ℝ) :
    OSIITimeGapSpace k :=
  fun i => (τ i : ℂ)

theorem osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff
    {k : ℕ} (τ : Fin k → ℝ) :
    osiiPositiveRealTimeEmbed τ ∈ osiiTimeRightHalfPlane k ↔
      τ ∈ section43TimeStrictPositiveRegion k := by
  simp [osiiPositiveRealTimeEmbed, osiiTimeRightHalfPlane,
    section43TimeStrictPositiveRegion]

/-- Spatial Schwartz distributions parametrized by the finite family of
time gaps. -/
abbrev OSIISpatialDistribution (d k : ℕ) :=
  SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ] ℂ

/-- Weak holomorphy of a spatial-distribution family: every scalar pairing
with a spatial Schwartz test is holomorphic in the time variables. -/
def OSIIWeaklyHolomorphicOn
    {d k : ℕ}
    (F : OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k)) : Prop :=
  ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
    DifferentiableOn ℂ (fun ζ => F ζ χ) U

/-- One scalar-continuation stage `(A_N)` in the OS-II Chapter V ladder. -/
structure OSIITimeContinuationStage (d k : ℕ) where
  carrier : Set (OSIITimeGapSpace k)
  carrier_open : IsOpen carrier
  distribution : OSIITimeGapSpace k → OSIISpatialDistribution d k
  weaklyHolomorphic : OSIIWeaklyHolomorphicOn distribution carrier

/-- An increasing family of OS-II scalar-continuation stages.

`extends_succ` is the genuine analytic compatibility obligation.  It does not
assert that a later stage exists; it records exactly what must be proved after
the `(P_N) -> (A_{N+1})` construction.

Auxiliary stage carriers may extend outside the product right half-plane.
Only coverage of that half-plane is required; the glued continuation is
restricted to it at the endpoint. -/
structure OSIITimeContinuationLadder (d k : ℕ) where
  stage : ℕ → OSIITimeContinuationStage d k
  carrier_mono :
    Monotone fun N => (stage N).carrier
  extends_succ :
    ∀ N, Set.EqOn
      (stage (N + 1)).distribution
      (stage N).distribution
      (stage N).carrier
  exhausts :
    osiiTimeRightHalfPlane k ⊆ ⋃ N, (stage N).carrier

namespace OSIITimeContinuationLadder

variable {d k : ℕ}

/-- Later continuation stages agree with an earlier stage throughout the
earlier carrier. -/
theorem distribution_eq_of_le
    (L : OSIITimeContinuationLadder d k)
    {M N : ℕ} (hMN : M ≤ N)
    {ζ : OSIITimeGapSpace k}
    (hζ : ζ ∈ (L.stage M).carrier) :
    (L.stage N).distribution ζ = (L.stage M).distribution ζ := by
  induction N, hMN using Nat.le_induction with
  | base =>
      rfl
  | succ N hMN ih =>
      calc
        (L.stage (N + 1)).distribution ζ =
            (L.stage N).distribution ζ :=
          L.extends_succ N
            (L.carrier_mono hMN hζ)
        _ = (L.stage M).distribution ζ := ih

/-- The adjacent extension property and monotone carriers imply the pairwise
overlap compatibility required for gluing. -/
theorem pairwise_compatible
    (L : OSIITimeContinuationLadder d k) (M N : ℕ) :
    Set.EqOn
      (L.stage M).distribution
      (L.stage N).distribution
      ((L.stage M).carrier ∩ (L.stage N).carrier) := by
  intro ζ hζ
  rcases le_total M N with hMN | hNM
  · exact (L.distribution_eq_of_le hMN hζ.1).symm
  · exact L.distribution_eq_of_le hNM hζ.2

/-- The full distribution-valued continuation obtained by gluing all stages. -/
def fullDistribution
    (L : OSIITimeContinuationLadder d k) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  SCV.glued_iUnion
    (fun N => (L.stage N).carrier)
    (fun N => (L.stage N).distribution)

/-- The glued continuation agrees with every finite stage on its carrier. -/
theorem fullDistribution_eqOn_stage
    (L : OSIITimeContinuationLadder d k) (N : ℕ) :
    Set.EqOn L.fullDistribution (L.stage N).distribution
      (L.stage N).carrier := by
  exact SCV.glued_iUnion_eqOn L.pairwise_compatible N

/-- Compatible stages whose domains exhaust `C₊^k` give a weakly holomorphic
spatial distribution on the full OS-II time domain. -/
theorem fullDistribution_weaklyHolomorphic
    (L : OSIITimeContinuationLadder d k) :
    OSIIWeaklyHolomorphicOn L.fullDistribution
      (osiiTimeRightHalfPlane k) := by
  intro χ
  let D : ℕ → OSIITimeGapSpace k → ℂ :=
    fun N ζ => (L.stage N).distribution ζ χ
  have hEq :
      ∀ M N, Set.EqOn (D M) (D N)
        ((L.stage M).carrier ∩ (L.stage N).carrier) := by
    intro M N ζ hζ
    exact congrArg (fun T : OSIISpatialDistribution d k => T χ)
      (L.pairwise_compatible M N hζ)
  have hglue :
      (fun ζ => L.fullDistribution ζ χ) =
        SCV.glued_iUnion (fun N => (L.stage N).carrier) D := by
    funext ζ
    classical
    simp only [fullDistribution, SCV.glued_iUnion, D]
    split_ifs <;> rfl
  rw [hglue]
  exact
    SCV.differentiableOn_glued_iUnion
      L.exhausts
      (fun N => (L.stage N).carrier_open)
      (fun N => (L.stage N).weaklyHolomorphic χ)
      hEq

/-- The exhausted ladder, viewed as one continuation stage on the complete
product right half-plane. -/
noncomputable def toFullTimeContinuationStage
    (L : OSIITimeContinuationLadder d k) :
    OSIITimeContinuationStage d k where
  carrier := osiiTimeRightHalfPlane k
  carrier_open := isOpen_osiiTimeRightHalfPlane k
  distribution := L.fullDistribution
  weaklyHolomorphic := L.fullDistribution_weaklyHolomorphic

@[simp] theorem toFullTimeContinuationStage_carrier
    (L : OSIITimeContinuationLadder d k) :
    L.toFullTimeContinuationStage.carrier =
      osiiTimeRightHalfPlane k :=
  rfl

@[simp] theorem toFullTimeContinuationStage_distribution
    (L : OSIITimeContinuationLadder d k) :
    L.toFullTimeContinuationStage.distribution =
      L.fullDistribution :=
  rfl

/-- The full stage retains every finite continuation stage on its complete
carrier. -/
theorem toFullTimeContinuationStage_extends_stage
    (L : OSIITimeContinuationLadder d k)
    (N : ℕ) :
    Set.EqOn L.toFullTimeContinuationStage.distribution
      (L.stage N).distribution (L.stage N).carrier :=
  L.fullDistribution_eqOn_stage N

end OSIITimeContinuationLadder

end OSReconstruction
