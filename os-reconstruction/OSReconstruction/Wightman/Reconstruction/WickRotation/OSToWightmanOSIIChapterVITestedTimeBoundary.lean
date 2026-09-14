import OSReconstruction.SCV.TubeBoundaryValueExistence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITestedTaylor
import Mathlib.Analysis.LocallyConvex.Barrelled

/-!
# Tested boundary values on the positive time tube

Positive imaginary translation gives the ordinary polynomial bound needed
by the proved Cauchy-Riemann slice identity. Taylor expansion is then applied
to the tested slices, with its remainder weighted at the singular endpoint.
No boundary-value or Fourier-support axiom is used in this construction.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Classical

namespace OSReconstruction
namespace OSIITestedTimeBoundary

private def tubePoint {k : Nat} (x y : Fin k -> Real) : Fin k -> Complex :=
  fun i => (x i : Complex) + (y i : Complex) * I

private def unitDirection (k : Nat) : Fin k -> Real := fun _ => 1

private def imaginaryTranslate {k : Nat}
    (F : (Fin k -> Complex) -> Complex) (a : Fin k -> Real) :
    (Fin k -> Complex) -> Complex :=
  fun z => F (z + fun i => (a i : Complex) * I)

private abbrev RegulatedGrowth {k : Nat}
    (F : (Fin k -> Complex) -> Complex) (C : Real) (N M : Nat) : Prop :=
  forall z, z ∈ SCV.TubeDomain (osiiTimePositiveCone k) ->
    ‖F z‖ <= C * (1 + ‖z‖) ^ N *
      (1 + (Metric.infDist (fun i => (z i).im)
        (osiiTimePositiveCone k)ᶜ)⁻¹) ^ M

private theorem unitDirection_mem (k : Nat) :
    unitDirection k ∈ osiiTimePositiveCone k := by
  intro i
  exact zero_lt_one

private theorem norm_unitDirection_le (k : Nat) :
    ‖unitDirection k‖ <= 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (by intro i; simp [unitDirection])

private theorem tubePoint_mem {k : Nat} (x : Fin k -> Real)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k) :
    tubePoint x y ∈ SCV.TubeDomain (osiiTimePositiveCone k) := by
  simpa [tubePoint, SCV.TubeDomain] using hy

private theorem norm_tubePoint_le {k : Nat} (x y : Fin k -> Real) :
    ‖tubePoint x y‖ <= ‖x‖ + ‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  calc
    ‖tubePoint x y i‖ <= ‖(x i : Complex)‖ + ‖(y i : Complex) * I‖ :=
      norm_add_le _ _
    _ = ‖x i‖ + ‖y i‖ := by simp
    _ <= ‖x‖ + ‖y‖ := add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm y i)

private theorem positiveCone_margin_pos {k : Nat} [NeZero k]
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k) :
    0 < Metric.infDist y (osiiTimePositiveCone k)ᶜ := by
  apply ((osiiTimePositiveCone_open k).isClosed_compl.notMem_iff_infDist_pos
    (osiiTimePositiveCone_compl_nonempty
      (Nat.pos_of_ne_zero (NeZero.ne k)))).1
  simpa using hy

private theorem positiveCone_margin_le_coordinate {k : Nat}
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k) (i : Fin k) :
    Metric.infDist y (osiiTimePositiveCone k)ᶜ <= y i := by
  simpa [osiiTimeBoundaryDistance, osiiPositiveRealTimeEmbed] using
    osiiTimeBoundaryDistance_le_re
      ((osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff y).2 hy) i

private theorem positiveCone_le_margin {k : Nat} [NeZero k]
    {y : Fin k -> Real} {r : Real} (hy : forall i, r <= y i) :
    r <= Metric.infDist y (osiiTimePositiveCone k)ᶜ := by
  refine (Metric.le_infDist (osiiTimePositiveCone_compl_nonempty
    (Nat.pos_of_ne_zero (NeZero.ne k)))).2 ?_
  intro v hv
  have hv' : v ∉ osiiTimePositiveCone k := hv
  simp only [osiiTimePositiveCone, section43TimeStrictPositiveRegion,
    Set.mem_setOf_eq, not_forall, not_lt] at hv'
  obtain ⟨i, hi⟩ := hv'
  calc
    r <= y i - v i := by linarith [hy i]
    _ <= |y i - v i| := le_abs_self _
    _ = dist (y i) (v i) := (Real.dist_eq _ _).symm
    _ <= dist y v := dist_le_pi_dist y v i

private theorem tubeSlice_imaginaryTranslate {k : Nat}
    (F : (Fin k -> Complex) -> Complex) (a y : Fin k -> Real)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    tubeSlice (imaginaryTranslate F a) y phi = tubeSlice F (y + a) phi := by
  apply integral_congr_ae
  filter_upwards with x
  change F ((fun i => (x i : Complex) + (y i : Complex) * I) +
      (fun i => (a i : Complex) * I)) * phi x =
    F (fun i => (x i : Complex) + ((y + a) i : Complex) * I) * phi x
  have hpoint :
      ((fun i => (x i : Complex) + (y i : Complex) * I) +
        (fun i => (a i : Complex) * I)) =
      fun i => (x i : Complex) + ((y + a) i : Complex) * I := by
    ext i
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring
  rw [hpoint]

private theorem imaginaryTranslate_holomorphic {k : Nat}
    {F : (Fin k -> Complex) -> Complex}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    {a : Fin k -> Real} (ha : a ∈ osiiTimePositiveCone k) :
    DifferentiableOn Complex (imaginaryTranslate F a)
      (SCV.TubeDomain (osiiTimePositiveCone k)) := by
  refine hF.comp (differentiable_id.add_const _).differentiableOn ?_
  intro z hz
  change (fun i => (z i + (a i : Complex) * I).im) ∈ osiiTimePositiveCone k
  intro i
  simpa using add_pos (hz i) (ha i)

private theorem norm_imaginaryEmbedding_le {k : Nat} (a : Fin k -> Real) :
    ‖(fun i => (a i : Complex) * I)‖ <= ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
  intro i
  simpa using norm_le_pi_norm a i

private theorem exists_imaginaryTranslate_polynomialGrowth
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {a : Fin k -> Real} (ha : a ∈ osiiTimePositiveCone k) :
    exists B : Real, 0 < B ∧
      forall z, z ∈ SCV.TubeDomain (osiiTimePositiveCone k) ->
        ‖imaginaryTranslate F a z‖ <= B * (1 + ‖z‖) ^ N := by
  let r := Metric.infDist a (osiiTimePositiveCone k)ᶜ
  have hr : 0 < r := positiveCone_margin_pos ha
  refine ⟨C * (1 + ‖a‖) ^ N * (1 + r⁻¹) ^ M, by positivity, ?_⟩
  intro z hz
  let w := z + fun i => (a i : Complex) * I
  have hw : w ∈ SCV.TubeDomain (osiiTimePositiveCone k) := by
    intro i
    change 0 < (z i + (a i : Complex) * I).im
    simpa using add_pos (hz i) (ha i)
  have hmargin : r <= Metric.infDist (fun i => (w i).im)
      (osiiTimePositiveCone k)ᶜ := by
    apply positiveCone_le_margin
    intro i
    have hi := positiveCone_margin_le_coordinate ha i
    change r <= (z i + (a i : Complex) * I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith [hz i]
  have hinv : (Metric.infDist (fun i => (w i).im)
      (osiiTimePositiveCone k)ᶜ)⁻¹ <= r⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hr hmargin
  have hdist : 0 <= Metric.infDist (fun i => (w i).im)
      (osiiTimePositiveCone k)ᶜ := Metric.infDist_nonneg
  have hnorm : 1 + ‖w‖ <= (1 + ‖a‖) * (1 + ‖z‖) := by
    have h := (norm_add_le z (fun i => (a i : Complex) * I)).trans
      (add_le_add (le_refl ‖z‖) (norm_imaginaryEmbedding_le a))
    change ‖w‖ <= ‖z‖ + ‖a‖ at h
    nlinarith [norm_nonneg z, norm_nonneg a]
  change ‖F w‖ <= _
  calc
    ‖F w‖ <= C * (1 + ‖w‖) ^ N *
        (1 + (Metric.infDist (fun i => (w i).im)
          (osiiTimePositiveCone k)ᶜ)⁻¹) ^ M := hgrowth w hw
    _ <= C * ((1 + ‖a‖) * (1 + ‖z‖)) ^ N * (1 + r⁻¹) ^ M := by
      gcongr
    _ = (C * (1 + ‖a‖) ^ N * (1 + r⁻¹) ^ M) * (1 + ‖z‖) ^ N := by
      rw [mul_pow]
      ring

private theorem hasDerivAt_shiftedTubeSlice
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    {s : Real} (hs : 0 <= s)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    HasDerivAt
      (fun u => tubeSlice F (y + u • unitDirection k) phi)
      (-I * tubeSlice F (y + s • unitDirection k)
        (directionalDerivSchwartz (unitDirection k) phi)) s := by
  let delta := Metric.infDist y (osiiTimePositiveCone k)ᶜ / 2
  have hdelta : 0 < delta := half_pos (positiveCone_margin_pos hy)
  let a := y - delta • unitDirection k
  have ha : a ∈ osiiTimePositiveCone k := by
    intro i
    change 0 < y i - delta * 1
    have hi := positiveCone_margin_le_coordinate hy i
    dsimp [delta] at *
    linarith
  have hH := imaginaryTranslate_holomorphic hF ha
  obtain ⟨B, hB, hbound⟩ := exists_imaginaryTranslate_polynomialGrowth hC hgrowth ha
  have hderiv := hasDerivAt_tubeSlice_ray hH hH.continuousOn
    (unitDirection k) (unitDirection_mem k)
    (osiiTimePositiveCone_isCone k) (osiiTimePositiveCone_open k)
    hB hbound (s + delta) (by linarith) phi
  have heq (u : Real) (psi : SchwartzMap (Fin k -> Real) Complex) :
      tubeSlice (imaginaryTranslate F a) ((u + delta) • unitDirection k) psi =
        tubeSlice F (y + u • unitDirection k) psi := by
    rw [tubeSlice_imaginaryTranslate]
    congr 1
    ext i
    simp [a, unitDirection]
    ring
  have hcomp := hderiv.comp_add_const s delta
  simpa only [heq] using hcomp

private theorem positiveOffset_mem {k : Nat}
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    {s : Real} (hs : 0 <= s) :
    y + s • unitDirection k ∈ osiiTimePositiveCone k := by
  intro i
  change 0 < y i + s * 1
  simpa using add_pos_of_pos_of_nonneg (hy i) hs

private theorem norm_smallHeight_le {k : Nat}
    (eta : Fin k -> Real) {epsilon s : Real}
    (hepsilon : 0 <= epsilon) (hepsilon_one : epsilon <= 1)
    (hs : 0 <= s) :
    ‖epsilon • eta + s • unitDirection k‖ <= ‖eta‖ + s := by
  calc
    ‖epsilon • eta + s • unitDirection k‖ <=
        ‖epsilon • eta‖ + ‖s • unitDirection k‖ := norm_add_le _ _
    _ = epsilon * ‖eta‖ + s * ‖unitDirection k‖ := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hepsilon, abs_of_nonneg hs]
    _ <= 1 * ‖eta‖ + s * 1 := by
      gcongr
      exact norm_unitDirection_le k
    _ = ‖eta‖ + s := by ring

private theorem smallHeight_coordinate_ge {k : Nat}
    {eta : Fin k -> Real} (heta : eta ∈ osiiTimePositiveCone k)
    {epsilon : Real} (hepsilon : 0 <= epsilon) (s : Real) (i : Fin k) :
    s <= (epsilon • eta + s • unitDirection k) i := by
  change s <= epsilon * eta i + s * 1
  nlinarith [heta i]

private theorem norm_at_height_le
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {y : Fin k -> Real} {r R : Real}
    (hr : 0 < r) (hcoordinates : forall i, r <= y i)
    (hR : ‖y‖ <= R) (x : Fin k -> Real) :
    ‖F (tubePoint x y)‖ <=
      (C * (1 + R) ^ N * (1 + r⁻¹) ^ M) * (1 + ‖x‖) ^ N := by
  have hy : y ∈ osiiTimePositiveCone k := fun i => hr.trans_le (hcoordinates i)
  have hR_nonneg := (norm_nonneg y).trans hR
  have hmargin := positiveCone_le_margin hcoordinates
  have hinv : (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹ <= r⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hr hmargin
  have hdist : 0 <= Metric.infDist y (osiiTimePositiveCone k)ᶜ :=
    Metric.infDist_nonneg
  have hnorm : 1 + ‖tubePoint x y‖ <= (1 + R) * (1 + ‖x‖) := by
    have h := norm_tubePoint_le x y
    nlinarith [norm_nonneg x]
  calc
    ‖F (tubePoint x y)‖ <= C * (1 + ‖tubePoint x y‖) ^ N *
        (1 + (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹) ^ M := by
      simpa [tubePoint] using hgrowth (tubePoint x y) (tubePoint_mem x hy)
    _ <= C * ((1 + R) * (1 + ‖x‖)) ^ N * (1 + r⁻¹) ^ M := by
      gcongr
    _ = (C * (1 + R) ^ N * (1 + r⁻¹) ^ M) * (1 + ‖x‖) ^ N := by
      rw [mul_pow]
      ring

private theorem continuous_sliceIntegrand {k : Nat}
    {F : (Fin k -> Complex) -> Complex}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k) :
    Continuous (fun x => F (tubePoint x y)) := by
  have hpoint : Continuous (fun x : Fin k -> Real => tubePoint x y) := by
    unfold tubePoint
    fun_prop
  have hcomp : ContinuousOn (fun x => F (tubePoint x y)) univ :=
    hF.continuousOn.comp hpoint.continuousOn (fun x _ => tubePoint_mem x hy)
  simpa using hcomp

private theorem norm_tubeSlice_le_of_heightBounds
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {y : Fin k -> Real} {r R : Real}
    (hr : 0 < r) (hcoordinates : forall i, r <= y i)
    (hR : ‖y‖ <= R)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    ‖tubeSlice F y phi‖ <=
      (C * (1 + R) ^ N * (1 + r⁻¹) ^ M) *
        ∫ x : Fin k -> Real, (1 + ‖x‖) ^ N * ‖phi x‖ := by
  let K := C * (1 + R) ^ N * (1 + r⁻¹) ^ M
  calc
    ‖tubeSlice F y phi‖ <=
        ∫ x : Fin k -> Real, K * ((1 + ‖x‖) ^ N * ‖phi x‖) := by
      apply norm_integral_le_of_norm_le
        ((SCV.schwartzMap_polynomial_norm_integrable phi N).const_mul K)
      filter_upwards with x
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (norm_at_height_le hC hgrowth hr hcoordinates hR x)
        (norm_nonneg (phi x))).trans_eq (by ring)
    _ = K * ∫ x : Fin k -> Real, (1 + ‖x‖) ^ N * ‖phi x‖ :=
      integral_const_mul _ _

private theorem tendsto_tubeSlice_at_positiveHeight
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {eta : Fin k -> Real} (heta : eta ∈ osiiTimePositiveCone k)
    {s : Real} (hs : 0 < s)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Tendsto
      (fun epsilon : Real => tubeSlice F (epsilon • eta + s • unitDirection k) phi)
      (nhdsWithin 0 (Ioi 0))
      (nhds (tubeSlice F (s • unitDirection k) phi)) := by
  let K := C * (1 + (‖eta‖ + s)) ^ N * (1 + s⁻¹) ^ M
  have hmeas : forall epsilon : Real, 0 < epsilon ->
      AEStronglyMeasurable
        (fun x => F (tubePoint x (epsilon • eta + s • unitDirection k)) * phi x)
        volume := by
    intro epsilon hepsilon
    have hy : epsilon • eta + s • unitDirection k ∈ osiiTimePositiveCone k :=
      positiveOffset_mem ((osiiTimePositiveCone_isCone k) eta heta epsilon hepsilon) hs.le
    exact (continuous_sliceIntegrand hF hy).aestronglyMeasurable.mul
      phi.continuous.aestronglyMeasurable
  change Tendsto
    (fun epsilon : Real => ∫ x : Fin k -> Real,
      F (tubePoint x (epsilon • eta + s • unitDirection k)) * phi x)
    _ (nhds (∫ x : Fin k -> Real, F (tubePoint x (s • unitDirection k)) * phi x))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : Fin k -> Real => K * ((1 + ‖x‖) ^ N * ‖phi x‖))
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact hmeas epsilon hepsilon
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : Real) < 1 by norm_num)]
      with epsilon hepsilon
    filter_upwards with x
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (norm_at_height_le hC hgrowth hs
        (smallHeight_coordinate_ge heta hepsilon.1.le s)
        (norm_smallHeight_le eta hepsilon.1.le hepsilon.2 hs.le) x)
      (norm_nonneg (phi x))).trans_eq (by ring)
  · exact (SCV.schwartzMap_polynomial_norm_integrable phi N).const_mul K
  · filter_upwards with x
    have hy : s • unitDirection k ∈ osiiTimePositiveCone k :=
      (osiiTimePositiveCone_isCone k) _ (unitDirection_mem k) s hs
    have hFc := hF.continuousOn.continuousAt
      ((SCV.tubeDomain_isOpen (osiiTimePositiveCone_open k)).mem_nhds
        (tubePoint_mem x hy))
    have hpoint : Continuous
        (fun epsilon : Real => tubePoint x (epsilon • eta + s • unitDirection k)) := by
      unfold tubePoint
      fun_prop
    have hpointLimit : Tendsto
        (fun epsilon : Real => tubePoint x (epsilon • eta + s • unitDirection k))
        (nhdsWithin 0 (Ioi 0)) (nhds (tubePoint x (s • unitDirection k))) := by
      simpa only [zero_smul, zero_add] using
        (hpoint.tendsto (0 : Real)).mono_left nhdsWithin_le_nhds
    exact (hFc.tendsto.comp hpointLimit).mul_const (phi x)

private def sliceJet {k : Nat}
    (F : (Fin k -> Complex) -> Complex)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (j : Nat) (y : Fin k -> Real) : Complex :=
  (-I) ^ j * tubeSlice F y
    (((directionalDerivSchwartz (unitDirection k)) ^ j) phi)

private theorem sliceJet_zero {k : Nat}
    (F : (Fin k -> Complex) -> Complex)
    (phi : SchwartzMap (Fin k -> Real) Complex) (y : Fin k -> Real) :
    sliceJet F phi 0 y = tubeSlice F y phi := by
  simp [sliceJet]

private theorem norm_sliceJet {k : Nat}
    (F : (Fin k -> Complex) -> Complex)
    (phi : SchwartzMap (Fin k -> Real) Complex) (j : Nat) (y : Fin k -> Real) :
    ‖sliceJet F phi j y‖ = ‖tubeSlice F y
      (((directionalDerivSchwartz (unitDirection k)) ^ j) phi)‖ := by
  simp [sliceJet, norm_pow]

private theorem hasDerivAt_sliceJet
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    {s : Real} (hs : 0 <= s)
    (phi : SchwartzMap (Fin k -> Real) Complex) (j : Nat) :
    HasDerivAt (fun u => sliceJet F phi j (y + u • unitDirection k))
      (sliceJet F phi (j + 1) (y + s • unitDirection k)) s := by
  let D := directionalDerivSchwartz (unitDirection k)
  have hD : D ((D ^ j) phi) = (D ^ (j + 1)) phi := by
    rw [pow_succ', ContinuousLinearMap.mul_apply]
  have hscalar : (-I : Complex) ^ (j + 1) = (-I) ^ j * (-I) :=
    pow_succ _ _
  have hderiv := (hasDerivAt_shiftedTubeSlice hF hC hgrowth hy hs
    ((D ^ j) phi)).const_mul ((-I : Complex) ^ j)
  change HasDerivAt
    (fun u => (-I) ^ j * tubeSlice F (y + u • unitDirection k) ((D ^ j) phi))
    ((-I) ^ (j + 1) * tubeSlice F (y + s • unitDirection k) ((D ^ (j + 1)) phi)) s
  rw [hscalar, ← hD]
  simpa only [mul_assoc] using hderiv

private theorem tubeSlice_eq_testedExpansion
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    tubeSlice F y phi =
      (∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (-1) ^ j) •
          sliceJet F phi j (y + unitDirection k)) -
      (M.factorial : Real)⁻¹ • ∫ s in (0 : Real)..1,
        (-s) ^ M • sliceJet F phi (M + 1) (y + s • unitDirection k) := by
  have h := osii_testedTaylor_endpoint
    (fun j s => sliceJet F phi j (y + s • unitDirection k)) M
    (fun j s hs => hasDerivAt_sliceJet hF hC hgrowth hy hs.1 phi j)
  simpa only [zero_smul, add_zero, one_smul, sliceJet_zero] using h

private def testedBoundaryValue {k : Nat}
    (F : (Fin k -> Complex) -> Complex) (M : Nat)
    (phi : SchwartzMap (Fin k -> Real) Complex) : Complex :=
  (∑ j ∈ Finset.range (M + 1),
    ((j.factorial : Real)⁻¹ * (-1) ^ j) • sliceJet F phi j (unitDirection k)) -
  (M.factorial : Real)⁻¹ • ∫ s in (0 : Real)..1,
    (-s) ^ M • sliceJet F phi (M + 1) (s • unitDirection k)

private theorem tendsto_sliceJet_at_positiveHeight
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {eta : Fin k -> Real} (heta : eta ∈ osiiTimePositiveCone k)
    {s : Real} (hs : 0 < s)
    (phi : SchwartzMap (Fin k -> Real) Complex) (j : Nat) :
    Tendsto
      (fun epsilon : Real =>
        sliceJet F phi j (epsilon • eta + s • unitDirection k))
      (nhdsWithin 0 (Ioi 0))
      (nhds (sliceJet F phi j (s • unitDirection k))) :=
  (tendsto_tubeSlice_at_positiveHeight hF hC hgrowth heta hs _
    ).const_mul ((-I : Complex) ^ j)

private theorem weightedRemainder_norm_le
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {eta : Fin k -> Real} (heta : eta ∈ osiiTimePositiveCone k)
    {epsilon s : Real} (hepsilon : epsilon ∈ Ioc (0 : Real) 1)
    (hs : s ∈ Ioc (0 : Real) 1)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    ‖(-s) ^ M • sliceJet F phi (M + 1)
        (epsilon • eta + s • unitDirection k)‖ <=
      C * (1 + (‖eta‖ + 1)) ^ N * 2 ^ M *
        ∫ x : Fin k -> Real, (1 + ‖x‖) ^ N *
          ‖(((directionalDerivSchwartz (unitDirection k)) ^ (M + 1)) phi) x‖ := by
  let psi := ((directionalDerivSchwartz (unitDirection k)) ^ (M + 1)) phi
  let p : Real := ∫ x : Fin k -> Real, (1 + ‖x‖) ^ N * ‖psi x‖
  have hp : 0 <= p := integral_nonneg (fun x => by positivity)
  have hheight : ‖epsilon • eta + s • unitDirection k‖ <= ‖eta‖ + 1 :=
    (norm_smallHeight_le eta hepsilon.1.le hepsilon.2 hs.1.le).trans
      (add_le_add (le_refl ‖eta‖) hs.2)
  have hslice := norm_tubeSlice_le_of_heightBounds hC hgrowth hs.1
    (smallHeight_coordinate_ge heta hepsilon.1.le s) hheight psi
  have hcancel : s ^ M * (1 + s⁻¹) ^ M <= (2 : Real) ^ M := by
    rw [← mul_pow]
    have hbase : s * (1 + s⁻¹) = s + 1 := by
      rw [mul_add, mul_one, mul_inv_cancel₀ hs.1.ne']
    rw [hbase]
    exact pow_le_pow_left₀ (add_nonneg hs.1.le zero_le_one)
      (by linarith [hs.2]) M
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_of_pos hs.1,
    norm_sliceJet]
  calc
    s ^ M * ‖tubeSlice F (epsilon • eta + s • unitDirection k) psi‖ <=
        s ^ M * ((C * (1 + (‖eta‖ + 1)) ^ N * (1 + s⁻¹) ^ M) * p) :=
      mul_le_mul_of_nonneg_left hslice (pow_nonneg hs.1.le _)
    _ = (C * (1 + (‖eta‖ + 1)) ^ N * p) *
        (s ^ M * (1 + s⁻¹) ^ M) := by ring
    _ <= (C * (1 + (‖eta‖ + 1)) ^ N * p) * 2 ^ M :=
      mul_le_mul_of_nonneg_left hcancel (by positivity)
    _ = C * (1 + (‖eta‖ + 1)) ^ N * 2 ^ M * p := by ring

private theorem tendsto_weightedRemainder
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {eta : Fin k -> Real} (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Tendsto
      (fun epsilon : Real => ∫ s in (0 : Real)..1,
        (-s) ^ M • sliceJet F phi (M + 1)
          (epsilon • eta + s • unitDirection k))
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ s in (0 : Real)..1,
        (-s) ^ M • sliceJet F phi (M + 1) (s • unitDirection k))) := by
  let B := C * (1 + (‖eta‖ + 1)) ^ N * 2 ^ M *
    ∫ x : Fin k -> Real, (1 + ‖x‖) ^ N *
      ‖(((directionalDerivSchwartz (unitDirection k)) ^ (M + 1)) phi) x‖
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : Real => B)
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    have hy := (osiiTimePositiveCone_isCone k) eta heta epsilon hepsilon
    have hjcont : ContinuousOn
        (fun s => sliceJet F phi (M + 1) (epsilon • eta + s • unitDirection k))
        (Icc (0 : Real) 1) := by
      intro s hs
      exact (hasDerivAt_sliceJet hF hC hgrowth hy hs.1 phi (M + 1)
        ).continuousAt.continuousWithinAt
    have hcont := (continuousOn_id.neg.pow M).smul hjcont
    simpa only [uIoc_of_le (show (0 : Real) <= 1 by norm_num)] using
      (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : Real) < 1 by norm_num)]
      with epsilon hepsilon
    exact Filter.Eventually.of_forall fun s hs =>
      weightedRemainder_norm_le hC hgrowth heta hepsilon
        (by simpa using hs) phi
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s hs =>
      (tendsto_sliceJet_at_positiveHeight hF hC hgrowth heta
        (by simpa using hs.1) phi (M + 1)).const_smul ((-s) ^ M)

private theorem tendsto_testedBoundaryValue
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M)
    {eta : Fin k -> Real} (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Tendsto (fun epsilon : Real => tubeSlice F (epsilon • eta) phi)
      (nhdsWithin 0 (Ioi 0)) (nhds (testedBoundaryValue F M phi)) := by
  have hsum : Tendsto
      (fun epsilon : Real => ∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (-1) ^ j) •
          sliceJet F phi j (epsilon • eta + unitDirection k))
      (nhdsWithin 0 (Ioi 0))
      (nhds (∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (-1) ^ j) •
          sliceJet F phi j (unitDirection k))) := by
    apply tendsto_finset_sum
    intro j hj
    simpa only [one_smul] using
      (tendsto_sliceJet_at_positiveHeight hF hC hgrowth heta
        (show (0 : Real) < 1 by norm_num) phi j).const_smul
          ((j.factorial : Real)⁻¹ * (-1) ^ j)
  have hlim := hsum.sub
    ((tendsto_weightedRemainder hF hC hgrowth heta phi
      ).const_smul (M.factorial : Real)⁻¹)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  exact (tubeSlice_eq_testedExpansion hF hC hgrowth
    ((osiiTimePositiveCone_isCone k) eta heta epsilon hepsilon) phi).symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_temperedBoundary_pos
    {k : Nat} [NeZero k]
    {F : (Fin k -> Complex) -> Complex} {C : Real} {N M : Nat}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    (hC : 0 < C) (hgrowth : RegulatedGrowth F C N M) :
    exists W : SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (eta : Fin k -> Real), eta ∈ osiiTimePositiveCone k ->
        Tendsto (fun epsilon : Real => tubeSlice F (epsilon • eta) phi)
          (nhdsWithin 0 (Ioi 0)) (nhds (W phi)) := by
  let T : Real -> SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex :=
    fun epsilon => if hepsilon : 0 < epsilon then
      Classical.choose (tubeSlice_temperedDistribution
        (osiiTimePositiveCone_open k) (osiiTimePositiveCone_isCone k)
        hF.continuousOn hC hgrowth
        (unitDirection k) (unitDirection_mem k) epsilon hepsilon)
      else 0
  have hT (epsilon : Real) (hepsilon : 0 < epsilon)
      (phi : SchwartzMap (Fin k -> Real) Complex) :
      T epsilon phi = tubeSlice F (epsilon • unitDirection k) phi := by
    simp only [T, dif_pos hepsilon]
    exact Classical.choose_spec (tubeSlice_temperedDistribution
      (osiiTimePositiveCone_open k) (osiiTimePositiveCone_isCone k)
      hF.continuousOn hC hgrowth
      (unitDirection k) (unitDirection_mem k) epsilon hepsilon) phi
  let value := testedBoundaryValue F M
  have hpointwise : forall phi,
      Tendsto (fun epsilon : Real => T epsilon phi)
        (nhdsWithin 0 (Ioi 0)) (nhds (value phi)) := by
    intro phi
    apply (tendsto_testedBoundaryValue hF hC hgrowth (unitDirection_mem k) phi).congr'
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact (hT epsilon hepsilon phi).symm
  have hfun : Tendsto (fun epsilon phi => T epsilon phi)
      (nhdsWithin 0 (Ioi 0)) (nhds value) := by
    rw [tendsto_pi_nhds]
    exact hpointwise
  have hadd : forall phi psi, value (phi + psi) = value phi + value psi := by
    intro phi psi
    apply tendsto_nhds_unique (hpointwise (phi + psi))
    simpa only [map_add] using (hpointwise phi).add (hpointwise psi)
  have hsmul : forall (c : Complex) phi, value (c • phi) = c • value phi := by
    intro c phi
    apply tendsto_nhds_unique (hpointwise (c • phi))
    simpa only [map_smul] using tendsto_const_nhds.smul (hpointwise phi)
  letI : ContinuousSMul Real (SchwartzMap (Fin k -> Real) Complex) :=
    SchwartzMap.instContinuousSMul
  let LR : SchwartzMap (Fin k -> Real) Complex →L[Real] Complex :=
    continuousLinearMapOfTendsto
      (fun epsilon => (T epsilon).restrictScalars Real) hfun
  have hcontinuous : Continuous value := by
    simpa [LR, continuousLinearMapOfTendsto] using LR.continuous
  let W : SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex :=
    { toLinearMap := { toFun := value, map_add' := hadd, map_smul' := hsmul }
      cont := hcontinuous }
  refine ⟨W, ?_⟩
  intro phi eta heta
  exact tendsto_testedBoundaryValue hF hC hgrowth heta phi

end OSIITestedTimeBoundary

/-- The tested Cauchy--Riemann identity on a positive ray under the actual
regulated growth hypothesis. A fixed positive translate lets the existing
polynomial-growth differentiation theorem apply locally at the given height. -/
theorem osiiTimeTube_hasDerivAt_ray_of_vladimirovGrowth
    {k : Nat} [NeZero k] {F : (Fin k -> Complex) -> Complex}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    {C : Real} {N M : Nat} (hC : 0 < C)
    (hgrowth : forall z, z ∈ SCV.TubeDomain (osiiTimePositiveCone k) ->
      ‖F z‖ <= C * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im)
          (osiiTimePositiveCone k)ᶜ)⁻¹) ^ M)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (t : Real) (ht : 0 < t)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    HasDerivAt (fun u => tubeSlice F (u • eta) phi)
      (-I * tubeSlice F (t • eta) (directionalDerivSchwartz eta phi)) t := by
  let delta := t / 2
  let a := delta • eta
  have hdelta : 0 < delta := half_pos ht
  have ha : a ∈ osiiTimePositiveCone k :=
    osiiTimePositiveCone_isCone k eta heta delta hdelta
  have hH := OSIITestedTimeBoundary.imaginaryTranslate_holomorphic hF ha
  obtain ⟨B, hB, hbound⟩ :=
    OSIITestedTimeBoundary.exists_imaginaryTranslate_polynomialGrowth hC hgrowth ha
  have hderiv := hasDerivAt_tubeSlice_ray hH hH.continuousOn eta heta
    (osiiTimePositiveCone_isCone k) (osiiTimePositiveCone_open k)
    hB hbound (t - delta) (by dsimp [delta]; linarith) phi
  have heq (u : Real) (psi : SchwartzMap (Fin k -> Real) Complex) :
      tubeSlice (OSIITestedTimeBoundary.imaginaryTranslate F a)
        ((u - delta) • eta) psi = tubeSlice F (u • eta) psi := by
    rw [OSIITestedTimeBoundary.tubeSlice_imaginaryTranslate]
    congr 1
    ext i
    simp [a]
    ring
  simpa only [heq] using hderiv.comp_sub_const t delta

/-- Globally regulated growth on the positive time tube gives one tempered
Schwartz boundary along every positive direction. This is the proved
positive-orthant instance of the Vladimirov boundary theorem; spectral
support is not included in its conclusion. -/
theorem osiiTimeTube_boundaryValue_of_vladimirovGrowth
    {k : Nat} {F : (Fin k -> Complex) -> Complex}
    (hF : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)))
    {C : Real} {N M : Nat} (hC : 0 < C)
    (hgrowth : forall z, z ∈ SCV.TubeDomain (osiiTimePositiveCone k) ->
      ‖F z‖ <= C * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im)
          (osiiTimePositiveCone k)ᶜ)⁻¹) ^ M) :
    exists W : SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (eta : Fin k -> Real), eta ∈ osiiTimePositiveCone k ->
        Tendsto (fun epsilon : Real => tubeSlice F (epsilon • eta) phi)
          (nhdsWithin 0 (Ioi 0)) (nhds (W phi)) := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨W, hW⟩ := tubeSlice_temperedDistribution
      (osiiTimePositiveCone_open 0) (osiiTimePositiveCone_isCone 0)
      hF.continuousOn hC hgrowth
      (OSIITestedTimeBoundary.unitDirection 0)
      (OSIITestedTimeBoundary.unitDirection_mem 0) 1 zero_lt_one
    refine ⟨W, ?_⟩
    intro phi eta _heta
    have heq : (fun epsilon : Real => tubeSlice F (epsilon • eta) phi) =
        fun _ => W phi := by
      funext epsilon
      exact (congrArg (fun y : Fin 0 -> Real => tubeSlice F y phi)
        (Subsingleton.elim _ _)).trans (hW phi).symm
    rw [heq]
    exact tendsto_const_nhds
  · letI : NeZero k := ⟨hk⟩
    exact OSIITestedTimeBoundary.exists_temperedBoundary_pos hF hC hgrowth

end OSReconstruction
