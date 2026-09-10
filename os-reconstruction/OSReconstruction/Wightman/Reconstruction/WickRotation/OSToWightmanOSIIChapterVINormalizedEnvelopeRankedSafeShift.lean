/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Convex.Deriv
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneParticleTranslatedMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- Tangent is convex on every compact positive interval strictly below the
principal half-angle.

This local form avoids a global statement across the poles of tangent.  It
is exactly the interval needed to compare a dyadically contracted argument
with its expanded generator angle. -/
theorem real_tan_convexOn_Icc_of_lt_pi_div_two
    {u : Real}
    (hu0 : 0 <= u)
    (hu : u < Real.pi / 2) :
    ConvexOn Real (Set.Icc 0 u) Real.tan := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 u)
  · intro x hx
    have hxI : x ∈ Set.Icc (0 : Real) u := hx
    have hxmem :
        x ∈ Set.Ioo (-(Real.pi / 2) : Real) (Real.pi / 2) := by
      constructor
      · have hpi2 : 0 < Real.pi / 2 := by positivity
        linarith [hxI.1]
      · exact hxI.2.trans_lt hu
    exact
      (Real.hasDerivAt_tan_of_mem_Ioo hxmem).continuousAt.continuousWithinAt
  · intro x hx
    have hxI : x ∈ Set.Icc (0 : Real) u := interior_subset hx
    have hxmem :
        x ∈ Set.Ioo (-(Real.pi / 2) : Real) (Real.pi / 2) := by
      constructor
      · have hpi2 : 0 < Real.pi / 2 := by positivity
        linarith [hxI.1]
      · exact hxI.2.trans_lt hu
    exact
      (Real.differentiableAt_tan_of_mem_Ioo hxmem).differentiableWithinAt
  · intro x hx y hy hxy
    have hxI : x ∈ Set.Icc (0 : Real) u := interior_subset hx
    have hyI : y ∈ Set.Icc (0 : Real) u := interior_subset hy
    have hxmem :
        x ∈ Set.Ioo (-(Real.pi / 2) : Real) (Real.pi / 2) := by
      constructor
      · have hpi2 : 0 < Real.pi / 2 := by positivity
        linarith [hxI.1]
      · exact hxI.2.trans_lt hu
    have hymem :
        y ∈ Set.Ioo (-(Real.pi / 2) : Real) (Real.pi / 2) := by
      constructor
      · have hpi2 : 0 < Real.pi / 2 := by positivity
        linarith [hyI.1]
      · exact hyI.2.trans_lt hu
    have hcosx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxmem
    have hcosy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo hymem
    have hcos_le : Real.cos y <= Real.cos x := by
      have hupi : u <= Real.pi := by
        linarith [hu, Real.pi_pos]
      exact
        Real.cos_le_cos_of_nonneg_of_le_pi
          hxI.1 (hyI.2.trans hupi) hxy
    have hsq : Real.cos y ^ 2 <= Real.cos x ^ 2 := by
      nlinarith
    rw [Real.deriv_tan, Real.deriv_tan]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hcosy) hsq

/-- A contraction by a factor in the unit interval contracts tangent by at
least the same factor below the principal half-angle. -/
theorem real_tan_mul_le_mul_tan_of_unitInterval
    {r u : Real}
    (hr0 : 0 <= r)
    (hr1 : r <= 1)
    (hu0 : 0 <= u)
    (hu : u < Real.pi / 2) :
    Real.tan (r * u) <= r * Real.tan u := by
  have hconv := real_tan_convexOn_Icc_of_lt_pi_div_two hu0 hu
  have hzero : (0 : Real) ∈ Set.Icc 0 u := ⟨le_rfl, hu0⟩
  have huI : u ∈ Set.Icc (0 : Real) u := ⟨hu0, le_rfl⟩
  have hcombo :=
    hconv.2 hzero huI (show 0 <= 1 - r by linarith) hr0
      (show (1 - r) + r = (1 : Real) by ring)
  simpa using hcombo

/-- A backward real shift using at most the radial slack of a contracted
right-half-plane point stays inside the expanded principal-argument bound.

If the original argument is r * y, subtracting no more than
(1 - r) * Re z leaves positive real part and gives absolute argument at
most |y|.  This is the coordinatewise estimate needed for the explicit safe
normalization window. -/
theorem abs_arg_sub_ofReal_le_of_radial_contraction
    {z : Complex}
    {r epsilon y : Real}
    (hz : 0 < z.re)
    (hr0 : 0 < r)
    (hr1 : r <= 1)
    (hy : |y| < Real.pi / 2)
    (harg : Complex.arg z = r * y)
    (hepsilon : epsilon <= (1 - r) * z.re) :
    |Complex.arg (z - (epsilon : Complex))| <= |y| := by
  have hz' : 0 < (z - (epsilon : Complex)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    have hrz : 0 < r * z.re := mul_pos hr0 hz
    nlinarith
  have harg_abs : |Complex.arg z| = r * |y| := by
    rw [harg, abs_mul, abs_of_pos hr0]
  have hratio :
      |z.im / z.re| = Real.tan (r * |y|) := by
    calc
      |z.im / z.re| =
          Real.tan (Real.arctan |z.im / z.re|) := by
        rw [Real.tan_arctan]
      _ = Real.tan |Complex.arg z| := by
        rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hz]
      _ = Real.tan (r * |y|) := by
        rw [harg_abs]
  have hden : r * z.re <= z.re - epsilon := by
    linarith
  have hden_pos : 0 < z.re - epsilon := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using hz'
  have hratio' :
      |(z - (epsilon : Complex)).im /
          (z - (epsilon : Complex)).re| <=
        Real.tan |y| := by
    have htan :=
      real_tan_mul_le_mul_tan_of_unitInterval
        hr0.le hr1 (abs_nonneg y) hy
    calc
      |(z - (epsilon : Complex)).im /
          (z - (epsilon : Complex)).re| =
          |z.im| / (z.re - epsilon) := by
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
          Complex.sub_re, Complex.ofReal_re, abs_div,
          abs_of_pos hden_pos]
      _ <= |z.im| / (r * z.re) := by
        exact
          div_le_div_of_nonneg_left
            (abs_nonneg z.im) (mul_pos hr0 hz) hden
      _ = |z.im / z.re| / r := by
        rw [abs_div, abs_of_pos hz]
        field_simp [hr0.ne', hz.ne']
      _ = Real.tan (r * |y|) / r := by rw [hratio]
      _ <= Real.tan |y| := by
        exact
          (div_le_iff₀ hr0).2
            (by simpa [mul_comm] using htan)
  rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hz']
  calc
    Real.arctan
        |(z - (epsilon : Complex)).im /
            (z - (epsilon : Complex)).re| <=
        Real.arctan (Real.tan |y|) :=
      Real.arctan_mono hratio'
    _ = |y| := by
      apply Real.arctan_tan
      · have hpi2 : 0 < Real.pi / 2 := by positivity
        linarith [abs_nonneg y]
      · exact hy

/-- One positive lower bound for every coordinate of a fixed positive-real
hub.

The outer-depth induction keeps its hub fixed.  Recording one finite
coordinate floor separates that depth-independent margin from the
target-dependent boundary distance used by VI.2. -/
structure PositiveHubFloorData
    {k : Nat}
    (hub : Fin k -> Real) where
  floor : Real
  floor_pos : 0 < floor
  floor_le : forall i, floor <= hub i

/-- A strict-positive finite hub has a positive common coordinate floor. -/
theorem nonempty_positiveHubFloorData
    {k : Nat} [NeZero k]
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k) :
    Nonempty (PositiveHubFloorData hub) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  let i0 : Fin k := ⟨0, hk⟩
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨i0, Finset.mem_univ i0⟩
  let floor : Real :=
    (Finset.univ : Finset (Fin k)).inf' huniv hub
  have hfloor_pos : 0 < floor := by
    dsimp [floor]
    exact
      (Finset.lt_inf'_iff huniv).2
        (fun i _hi => hhub i)
  exact
    ⟨{
      floor := floor
      floor_pos := hfloor_pos
      floor_le := by
        intro i
        dsimp [floor]
        exact Finset.inf'_le hub (Finset.mem_univ i) }⟩

/-- The common radius available simultaneously from the fixed hub and the
canonical VI.2 target radius.

The factor one half matches the canonical target-hub anchor exactly.  This
radius is allowed to shrink at the target boundary, but its hub contribution
is independent of recursive depth. -/
def rootedTargetHubCanonicalRadius
    {k : Nat}
    {hub : Fin k -> Real}
    (H : PositiveHubFloorData hub)
    (z : OSIITimeGapSpace k) : Real :=
  min (H.floor / 2) (osiiVI2CanonicalEpsilon k z)

theorem rootedTargetHubCanonicalRadius_pos
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    0 < rootedTargetHubCanonicalRadius H z := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  exact
    lt_min
      (div_pos H.floor_pos (by norm_num))
      (osiiVI2CanonicalEpsilon_pos hk hz)

theorem rootedTargetHubCanonicalRadius_le_half_target
    {k : Nat}
    {hub : Fin k -> Real}
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k)
    (i : Fin k) :
    rootedTargetHubCanonicalRadius H z <= (z i).re / 2 := by
  calc
    rootedTargetHubCanonicalRadius H z <=
        osiiVI2CanonicalEpsilon k z :=
      min_le_right _ _
    _ <= (z i).re / 2 := by
      unfold osiiVI2CanonicalEpsilon
      exact
        div_le_div_of_nonneg_right
          (osiiChapterVIRegularizationRadius_le_re hz i)
          (by norm_num)

/-- The reciprocal of a positive minimum is bounded by the sum of the two
reciprocals. -/
theorem inv_min_le_add_inv_of_pos
    {a b : Real}
    (ha : 0 < a)
    (hb : 0 < b) :
    (min a b)⁻¹ <= a⁻¹ + b⁻¹ := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    linarith [inv_nonneg.mpr hb.le]
  · rw [min_eq_right hba]
    linarith [inv_nonneg.mpr ha.le]

/-- The reciprocal common hub/target radius has the standard VI.2 boundary
degree; the fixed hub only changes its numerical coefficient. -/
theorem rootedTargetHubCanonicalRadius_inv_le_boundary
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    (rootedTargetHubCanonicalRadius H z)⁻¹ <=
      (2 * H.floor⁻¹ + 2) *
        (1 + (osiiTimeBoundaryDistance k z)⁻¹) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  let B : Real := 1 + (osiiTimeBoundaryDistance k z)⁻¹
  have hB_one : 1 <= B := by
    dsimp [B]
    have hboundary_pos : 0 < osiiTimeBoundaryDistance k z :=
      osiiTimeBoundaryDistance_pos hk hz
    linarith [inv_nonneg.mpr hboundary_pos.le]
  have hhalf_pos : 0 < H.floor / 2 :=
    div_pos H.floor_pos (by norm_num)
  have hcanonical_pos : 0 < osiiVI2CanonicalEpsilon k z :=
    osiiVI2CanonicalEpsilon_pos hk hz
  have hmin_inv :
      (rootedTargetHubCanonicalRadius H z)⁻¹ <=
        (H.floor / 2)⁻¹ +
          (osiiVI2CanonicalEpsilon k z)⁻¹ := by
    simpa [rootedTargetHubCanonicalRadius] using
      inv_min_le_add_inv_of_pos hhalf_pos hcanonical_pos
  have hhalf_inv :
      (H.floor / 2)⁻¹ = 2 * H.floor⁻¹ := by
    field_simp [H.floor_pos.ne']
  have hcanonical_inv :
      (osiiVI2CanonicalEpsilon k z)⁻¹ <= 2 * B := by
    simpa [B] using osiiVI2CanonicalEpsilon_inv_le hk hz
  have hx_nonneg : 0 <= 2 * H.floor⁻¹ := by
    exact
      mul_nonneg (by norm_num)
        (inv_nonneg.mpr H.floor_pos.le)
  have hx_le :
      2 * H.floor⁻¹ <= (2 * H.floor⁻¹) * B := by
    have hmul :=
      mul_le_mul_of_nonneg_left hB_one hx_nonneg
    nlinarith
  calc
    (rootedTargetHubCanonicalRadius H z)⁻¹ <=
        (H.floor / 2)⁻¹ +
          (osiiVI2CanonicalEpsilon k z)⁻¹ :=
      hmin_inv
    _ = 2 * H.floor⁻¹ +
        (osiiVI2CanonicalEpsilon k z)⁻¹ := by
      rw [hhalf_inv]
    _ <= 2 * H.floor⁻¹ + 2 * B :=
      add_le_add (le_refl _) hcanonical_inv
    _ <= (2 * H.floor⁻¹ + 2) * B := by
      nlinarith

/-- The explicit dyadic angular slack at recursive depth. -/
def rootedRecursiveRadialSlack (depth : Nat) : Real :=
  1 / (2 : Real) ^ (depth + 1)

theorem rootedRecursiveRadialSlack_pos
    (depth : Nat) :
    0 < rootedRecursiveRadialSlack depth := by
  unfold rootedRecursiveRadialSlack
  positivity

theorem rootedRecursiveRadialSlack_le_one
    (depth : Nat) :
    rootedRecursiveRadialSlack depth <= 1 := by
  unfold rootedRecursiveRadialSlack
  exact
    div_le_self (by norm_num)
      (one_le_pow₀ (by norm_num))

/-- The explicit normalization shift obtained by spending one sixth of the
dyadic angular slack times the common hub/target radius.

The denominator six leaves room for the rooted bridge's one-third anchor
loss and keeps strict inequalities available at the cutoff-support edge. -/
def rootedRecursiveSafeEpsilon
    {k : Nat}
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    (z : OSIITimeGapSpace k) : Real :=
  rootedRecursiveRadialSlack depth *
      rootedTargetHubCanonicalRadius H z / 6

/-- The actual VI.2 normalization translation uses half of the radial budget.

The remaining half is spent when selecting an open cutoff support below the
closed source-anchor carrier.  After both shifts, the total target motion is
exactly `rootedRecursiveSafeEpsilon`. -/
def rootedRecursiveNormalizationEpsilon
    {k : Nat}
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    (z : OSIITimeGapSpace k) : Real :=
  rootedRecursiveSafeEpsilon depth H z / 2

theorem rootedRecursiveSafeEpsilon_pos
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    0 < rootedRecursiveSafeEpsilon depth H z := by
  unfold rootedRecursiveSafeEpsilon
  exact
    div_pos
      (mul_pos (rootedRecursiveRadialSlack_pos depth)
        (rootedTargetHubCanonicalRadius_pos H hz))
      (by norm_num)

theorem rootedRecursiveNormalizationEpsilon_pos
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    0 < rootedRecursiveNormalizationEpsilon depth H z := by
  unfold rootedRecursiveNormalizationEpsilon
  exact div_pos (rootedRecursiveSafeEpsilon_pos depth H hz) (by norm_num)

/-- The full radial budget is no larger than the canonical VI.2 unshift
radius, hence its unshift stays in the product right half-plane. -/
theorem rootedRecursiveSafeEpsilon_le_canonical
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    rootedRecursiveSafeEpsilon depth H z <=
      osiiVI2CanonicalEpsilon k z := by
  have hradius_pos : 0 < rootedTargetHubCanonicalRadius H z :=
    rootedTargetHubCanonicalRadius_pos H hz
  have hradius_le :
      rootedTargetHubCanonicalRadius H z <=
        osiiVI2CanonicalEpsilon k z :=
    min_le_right _ _
  calc
    rootedRecursiveSafeEpsilon depth H z =
        rootedRecursiveRadialSlack depth *
          (rootedTargetHubCanonicalRadius H z / 6) := by
      unfold rootedRecursiveSafeEpsilon
      ring
    _ <= 1 * (rootedTargetHubCanonicalRadius H z / 6) :=
      mul_le_mul_of_nonneg_right
        (rootedRecursiveRadialSlack_le_one depth)
        (by positivity)
    _ <= osiiVI2CanonicalEpsilon k z := by
      linarith

/-- The actual normalization half-shift is also below the canonical VI.2
radius. -/
theorem rootedRecursiveNormalizationEpsilon_le_canonical
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    rootedRecursiveNormalizationEpsilon depth H z <=
      osiiVI2CanonicalEpsilon k z := by
  calc
    rootedRecursiveNormalizationEpsilon depth H z =
        rootedRecursiveSafeEpsilon depth H z / 2 := rfl
    _ <= rootedRecursiveSafeEpsilon depth H z := by
      linarith [rootedRecursiveSafeEpsilon_pos depth H hz]
    _ <= osiiVI2CanonicalEpsilon k z :=
      rootedRecursiveSafeEpsilon_le_canonical depth H hz

/-- A global VI.2 unshift is the same constant real subtraction on the
physical reflected-left block target. -/
@[simp] theorem rootedLeftBlockTarget_osiiVI2Unshift
    {k : Nat}
    (i : GeneratorIndex k)
    (epsilon : Real)
    (z : OSIITimeGapSpace k) :
    rootedLeftBlockTarget i (osiiVI2Unshift k epsilon z) =
      fun a => rootedLeftBlockTarget i z a - epsilon := by
  ext a
  simp only [rootedLeftBlockTarget, Pi.star_apply,
    generatorChronological_split_left, osiiVI2Unshift_apply]
  simp

/-- A global VI.2 unshift is the same constant real subtraction on the
physical right block target. -/
@[simp] theorem rootedRightBlockTarget_osiiVI2Unshift
    {k : Nat}
    (i : GeneratorIndex k)
    (epsilon : Real)
    (z : OSIITimeGapSpace k) :
    rootedRightBlockTarget i (osiiVI2Unshift k epsilon z) =
      fun b => rootedRightBlockTarget i z b - epsilon := by
  ext b
  simp only [rootedRightBlockTarget, generatorChronological_split_right,
    osiiVI2Unshift_apply]

/-- The explicit safe shift has a depthwise boundary-controlled inverse.
The coefficient is fixed by the hub floor and grows only by the dyadic
recursive-depth factor. -/
theorem rootedRecursiveSafeEpsilon_inv_le_boundary
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    (rootedRecursiveSafeEpsilon depth H z)⁻¹ <=
      (6 * (2 : Real) ^ (depth + 1) *
        (2 * H.floor⁻¹ + 2)) *
        (1 + (osiiTimeBoundaryDistance k z)⁻¹) := by
  have hradius_pos : 0 < rootedTargetHubCanonicalRadius H z :=
    rootedTargetHubCanonicalRadius_pos H hz
  have heq :
      (rootedRecursiveSafeEpsilon depth H z)⁻¹ =
        6 * (2 : Real) ^ (depth + 1) *
          (rootedTargetHubCanonicalRadius H z)⁻¹ := by
    unfold rootedRecursiveSafeEpsilon rootedRecursiveRadialSlack
    field_simp [hradius_pos.ne']
  calc
    (rootedRecursiveSafeEpsilon depth H z)⁻¹ =
        6 * (2 : Real) ^ (depth + 1) *
          (rootedTargetHubCanonicalRadius H z)⁻¹ :=
      heq
    _ <= 6 * (2 : Real) ^ (depth + 1) *
        ((2 * H.floor⁻¹ + 2) *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (rootedTargetHubCanonicalRadius_inv_le_boundary H hz)
        (by positivity)
    _ = (6 * (2 : Real) ^ (depth + 1) *
        (2 * H.floor⁻¹ + 2)) *
        (1 + (osiiTimeBoundaryDistance k z)⁻¹) := by
      ring

/-- Halving the radial budget only doubles the boundary-recovery
coefficient. -/
theorem rootedRecursiveNormalizationEpsilon_inv_le_boundary
    {k : Nat} [NeZero k]
    {hub : Fin k -> Real}
    (depth : Nat)
    (H : PositiveHubFloorData hub)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeRightHalfPlane k) :
    (rootedRecursiveNormalizationEpsilon depth H z)⁻¹ <=
      (12 * (2 : Real) ^ (depth + 1) *
        (2 * H.floor⁻¹ + 2)) *
        (1 + (osiiTimeBoundaryDistance k z)⁻¹) := by
  have hsafe_pos : 0 < rootedRecursiveSafeEpsilon depth H z :=
    rootedRecursiveSafeEpsilon_pos depth H hz
  have hsafe :=
    rootedRecursiveSafeEpsilon_inv_le_boundary depth H hz
  have heq :
      (rootedRecursiveNormalizationEpsilon depth H z)⁻¹ =
        2 * (rootedRecursiveSafeEpsilon depth H z)⁻¹ := by
    unfold rootedRecursiveNormalizationEpsilon
    field_simp [hsafe_pos.ne']
  rw [heq]
  calc
    2 * (rootedRecursiveSafeEpsilon depth H z)⁻¹ <=
        2 * ((6 * (2 : Real) ^ (depth + 1) *
          (2 * H.floor⁻¹ + 2)) *
          (1 + (osiiTimeBoundaryDistance k z)⁻¹)) :=
      mul_le_mul_of_nonneg_left hsafe (by norm_num)
    _ = (12 * (2 : Real) ^ (depth + 1) *
        (2 * H.floor⁻¹ + 2)) *
        (1 + (osiiTimeBoundaryDistance k z)⁻¹) := by
      ring

/-- Left-block successor room and source-anchor margin for one adapted atlas.
Keeping this as a separate package prevents later proofs from repeatedly
elaborating the full rooted replacement record. -/
structure RootedRankSuccessorTargetHubMarginLeftData
    {d k depth rank : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (adapted : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (epsilon : Real) where
  atGenerator : forall
      (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
      (hnm : k = q + 2 + m - 1)
      (_hi : i = ⟨q + 2, m, hn, hm, hnm⟩),
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    { Q :
        TailAnchorTargetHubBoxReflectedArgumentRegionData
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
          (fun a => A.rootedLeftBlockAnchor j a - 2 * epsilon)
          (fun a => rootedLeftBlockHub j hub a - 2 * epsilon)
          (fun a => rootedLeftBlockTarget j z a - 2 * epsilon)
          (reflectedChronologicalGapCarrier (q + 1)
            (A.rootedLeftBlockSpatialSourceCarrier R j)) //
      tsupport
          (((adapted.forCarrier
            q
            (A.rootedLeftBlockSpatialSourceCarrier R j)
            (A.rootedLeftBlockSpatialSourceCarrier_compact R j)
            (A.rootedLeftBlockSpatialSourceCarrier_positive R j)
          ).atlas.sourceStage.germ.η :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)) ⊆
        Q.region ∧
      tsupport
          (((adapted.forCarrier
            q
            (A.rootedLeftBlockSpatialSourceCarrier R j)
            (A.rootedLeftBlockSpatialSourceCarrier_compact R j)
            (A.rootedLeftBlockSpatialSourceCarrier_positive R j)
          ).atlas.sourceStage.germ.η :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)) ⊆
        reflectedTimeAnchorMarginRegion
          (A.rootedLeftBlockAnchor j) epsilon }

/-- Right-block successor room and source-anchor margin for one adapted atlas. -/
structure RootedRankSuccessorTargetHubMarginRightData
    {d k depth rank : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (adapted : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (epsilon : Real) where
  atGenerator : forall
      (n q : Nat) (hn : 1 <= n) (hm : 1 <= q + 2)
      (hnm : k = n + (q + 2) - 1)
      (_hi : i = ⟨n, q + 2, hn, hm, hnm⟩),
    let j : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    { Q :
        TailAnchorTargetHubBoxReflectedArgumentRegionData
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) (depth + 1) (rank + 1))
          (fun a => A.rootedRightBlockAnchor j a - 2 * epsilon)
          (fun a => rootedRightBlockHub j hub a - 2 * epsilon)
          (fun a => rootedRightBlockTarget j z a - 2 * epsilon)
          (reflectedChronologicalGapCarrier (q + 1)
            (A.rootedRightBlockSpatialSourceCarrier R j)) //
      tsupport
          (((adapted.forCarrier
            q
            (A.rootedRightBlockSpatialSourceCarrier R j)
            (A.rootedRightBlockSpatialSourceCarrier_compact R j)
            (A.rootedRightBlockSpatialSourceCarrier_positive R j)
          ).atlas.sourceStage.germ.η :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)) ⊆
        Q.region ∧
      tsupport
          (((adapted.forCarrier
            q
            (A.rootedRightBlockSpatialSourceCarrier R j)
            (A.rootedRightBlockSpatialSourceCarrier_compact R j)
            (A.rootedRightBlockSpatialSourceCarrier_positive R j)
          ).atlas.sourceStage.germ.η :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex)) ⊆
        reflectedTimeAnchorMarginRegion
          (A.rootedRightBlockAnchor j) epsilon }

/-- A rooted target-hub replacement whose nontrivial cutoffs retain both
the post-normalization successor room and the open source-anchor margin used
to justify the translation.

The visible extension is built from the unshifted target and hub.  The
successor rooms are deliberately indexed by the copies shifted down by
`2 * epsilon`: one `epsilon` opens the cutoff margin and the second is the
actual VI.2 translation.  Keeping both facts on the same adapted atlas is
the quantitative provenance needed by the final selected-orbit bridge. -/
structure RootedRankSuccessorTargetHubMarginAdaptedReflectedGramData
    {d k depth rank : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {I : Section43ProductTimeApproximateIdentity k}
    {anchor : Fin k -> Real}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (epsilon : Real) where
  current :
    RootedTargetHubAdaptedReflectedGramData
      S depth P.toAtlasFamily A R H i hub z
  leftSuccessor :
    RootedRankSuccessorTargetHubMarginLeftData
      (depth := depth) (rank := rank)
      S A R current.adapted i hub z epsilon
  rightSuccessor :
    RootedRankSuccessorTargetHubMarginRightData
      (depth := depth) (rank := rank)
      S A R current.adapted i hub z epsilon

/-- A pointed rooted extension retaining the exact margin-aware replacement
from which its visible analytic chart was built.

The ordinary pointed extension hides its selected packet and atlas family
behind provenance fields.  The adaptive VI.2 route needs the stronger fact
that the same cutoff also carries the post-normalization successor room and
source-anchor margin, so those witnesses stay adjacent to the construction. -/
structure RootedRankSuccessorTargetHubMarginPointedDirectExtensionData
    {d k : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {iota : Type*}
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (z : OSIITimeGapSpace k)
    (atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota)
    (epsilon : Real) where
  anchorData : TargetHubHalfAnchorData hub z
  anchor_eq_half_min : forall j,
    anchorData.anchor j = min (hub j) (z j).re / 2
  producer :
    AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth P.toAtlasFamily lgc anchorData.anchor
  producer_approximateIdentity_eq_fixed :
    producer.approximateIdentity =
      fixedTripleConvolutionApproximateIdentity k
  producer_roots_heq_fixed :
    HEq producer.roots (fixedTripleConvolutionRootData k)
  producer_packet_tailStart_eq_zero :
    producer.packet.carrierData.tailStart = 0
  leftMargin : i.n ≠ 1 -> forall a,
    2 * epsilon < producer.packet.rootedLeftBlockAnchor i a
  rightMargin : i.m ≠ 1 -> forall a,
    2 * epsilon < producer.packet.rootedRightBlockAnchor i a
  leftSuccessorTarget : i.n ≠ 1 ->
    (fun a => rootedLeftBlockTarget i z a - 2 * epsilon) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((i.n - 1) + 1) (depth + 1) (rank + 1))
  rightSuccessorTarget : i.m ≠ 1 ->
    (fun a => rootedRightBlockTarget i z a - 2 * epsilon) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((i.m - 1) + 1) (depth + 1) (rank + 1))
  rooted :
    RootedRankSuccessorTargetHubMarginAdaptedReflectedGramData
      S P producer.packet producer.roots
        producer.holomorphic.toContinuousTranslationData i hub z epsilon
  construction :
    RootedTargetHubPointedDirectExtensionConstructionDataAtRank
      S depth rank P lgc i hub atlas z anchorData producer rooted.current

end OSIIChapterV
end OSReconstruction
