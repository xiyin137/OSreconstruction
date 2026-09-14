/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertCauchyContinuation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedHilbertGram












noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Complex-linear coordinates whose real locus is the reflected diagonal.
For real block coordinates `(x,y)`, the output is
`(x - i y, x + i y) = (conj z, z)` with `z = x + i y`. -/
def reflectedDiagonalComplexLinearMap
    (m : ℕ) :
    (Fin (m + m) → ℂ) →ₗ[ℂ] (Fin (m + m) → ℂ) where
  toFun u :=
    Fin.addCases
      (fun i =>
        u (Fin.castAdd m i) -
          Complex.I * u (Fin.natAdd m i))
      (fun i =>
        u (Fin.castAdd m i) +
          Complex.I * u (Fin.natAdd m i))
  map_add' u v := by
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [Pi.add_apply, Fin.addCases_left]
      ring
    · intro i
      simp only [Pi.add_apply, Fin.addCases_right]
      ring
  map_smul' c u := by
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Fin.addCases_left]
      ring
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Fin.addCases_right]
      ring

@[simp] theorem reflectedDiagonalComplexLinearMap_left
    {m : ℕ}
    (u : Fin (m + m) → ℂ)
    (i : Fin m) :
    reflectedDiagonalComplexLinearMap m u (Fin.castAdd m i) =
      u (Fin.castAdd m i) -
        Complex.I * u (Fin.natAdd m i) := by
  simp [reflectedDiagonalComplexLinearMap]

@[simp] theorem reflectedDiagonalComplexLinearMap_right
    {m : ℕ}
    (u : Fin (m + m) → ℂ)
    (i : Fin m) :
    reflectedDiagonalComplexLinearMap m u (Fin.natAdd m i) =
      u (Fin.castAdd m i) +
        Complex.I * u (Fin.natAdd m i) := by
  change
    (Fin.addCases
      (motive := fun _ : Fin (m + m) => ℂ)
      (fun j =>
        u (Fin.castAdd m j) -
          Complex.I * u (Fin.natAdd m j))
      (fun j =>
        u (Fin.castAdd m j) +
          Complex.I * u (Fin.natAdd m j))
      (Fin.natAdd m i)) =
        u (Fin.castAdd m i) +
          Complex.I * u (Fin.natAdd m i)
  rw [Fin.addCases_right]

theorem reflectedDiagonalComplexLinearMap_injective
    (m : ℕ) :
    Function.Injective (reflectedDiagonalComplexLinearMap m) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply funext
  intro j
  let w := u - v
  have hw :
      reflectedDiagonalComplexLinearMap m w = 0 := by
    rw [map_sub, huv, sub_self]
  refine Fin.addCases ?_ ?_ j
  · intro i
    have hleft :
      w (Fin.castAdd m i) -
          Complex.I * w (Fin.natAdd m i) = 0 := by
      simpa only [reflectedDiagonalComplexLinearMap_left, Pi.zero_apply] using
        congr_fun hw (Fin.castAdd m i)
    have hright :
      w (Fin.castAdd m i) +
          Complex.I * w (Fin.natAdd m i) = 0 := by
      simpa only [reflectedDiagonalComplexLinearMap_right, Pi.zero_apply] using
        congr_fun hw (Fin.natAdd m i)
    have htwo :
        (2 : ℂ) * w (Fin.castAdd m i) = 0 := by
      calc
        (2 : ℂ) * w (Fin.castAdd m i) =
            (w (Fin.castAdd m i) -
                Complex.I * w (Fin.natAdd m i)) +
              (w (Fin.castAdd m i) +
                Complex.I * w (Fin.natAdd m i)) := by ring
        _ = 0 := by rw [hleft, hright, add_zero]
    have hwleft :
        w (Fin.castAdd m i) = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    simpa [w, Pi.sub_apply] using hwleft
  · intro i
    have hleft :
      w (Fin.castAdd m i) -
          Complex.I * w (Fin.natAdd m i) = 0 := by
      simpa only [reflectedDiagonalComplexLinearMap_left, Pi.zero_apply] using
        congr_fun hw (Fin.castAdd m i)
    have hright :
      w (Fin.castAdd m i) +
          Complex.I * w (Fin.natAdd m i) = 0 := by
      simpa only [reflectedDiagonalComplexLinearMap_right, Pi.zero_apply] using
        congr_fun hw (Fin.natAdd m i)
    have htwo :
        (2 * Complex.I) * w (Fin.natAdd m i) = 0 := by
      calc
        (2 * Complex.I) * w (Fin.natAdd m i) =
            (w (Fin.castAdd m i) +
                Complex.I * w (Fin.natAdd m i)) -
              (w (Fin.castAdd m i) -
                Complex.I * w (Fin.natAdd m i)) := by ring
        _ = 0 := by rw [hleft, hright, sub_zero]
    have hcoeff : (2 * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) Complex.I_ne_zero
    have hwright :
        w (Fin.natAdd m i) = 0 :=
      (mul_eq_zero.mp htwo).resolve_left hcoeff
    simpa [w, Pi.sub_apply] using hwright

theorem reflectedDiagonalComplexLinearMap_surjective
    (m : ℕ) :
    Function.Surjective (reflectedDiagonalComplexLinearMap m) := by
  intro w
  let u : Fin (m + m) → ℂ :=
    Fin.addCases
      (fun i =>
        (w (Fin.castAdd m i) +
          w (Fin.natAdd m i)) / 2)
      (fun i =>
        Complex.I *
          (w (Fin.castAdd m i) -
            w (Fin.natAdd m i)) / 2)
  refine ⟨u, ?_⟩
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedDiagonalComplexLinearMap_left]
    simp only [u, Fin.addCases_left, Fin.addCases_right]
    have hI :
        Complex.I *
            (Complex.I *
              (w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2) =
          -(w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2 := by
      calc
        Complex.I *
            (Complex.I *
              (w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2) =
            (Complex.I * Complex.I) *
              (w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2 := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [hI]
    ring
  · intro i
    rw [reflectedDiagonalComplexLinearMap_right]
    simp only [u, Fin.addCases_left, Fin.addCases_right]
    have hI :
        Complex.I *
            (Complex.I *
              (w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2) =
          -(w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2 := by
      calc
        Complex.I *
            (Complex.I *
              (w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2) =
            (Complex.I * Complex.I) *
              (w (Fin.castAdd m i) -
                w (Fin.natAdd m i)) / 2 := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [hI]
    ring

/-- Continuous linear equivalence implementing reflected-diagonal
coordinates. -/
def reflectedDiagonalComplexCLE
    (m : ℕ) :
    (Fin (m + m) → ℂ) ≃L[ℂ] (Fin (m + m) → ℂ) :=
  (LinearEquiv.ofBijective
    (reflectedDiagonalComplexLinearMap m)
    ⟨reflectedDiagonalComplexLinearMap_injective m,
      reflectedDiagonalComplexLinearMap_surjective m⟩)
    |>.toContinuousLinearEquiv

theorem reflectedDiagonalComplexCLE_real
    {m : ℕ}
    (x : Fin (m + m) → ℝ) :
    reflectedDiagonalComplexCLE m (SCV.realToComplex x) =
      reflectedCauchyIncrement
        (fun i =>
          (x (Fin.castAdd m i) : ℂ) +
            Complex.I * (x (Fin.natAdd m i) : ℂ)) := by
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [show
      reflectedDiagonalComplexCLE m (SCV.realToComplex x) =
        reflectedDiagonalComplexLinearMap m (SCV.realToComplex x) by rfl]
    rw [reflectedDiagonalComplexLinearMap_left,
      reflectedCauchyIncrement_left]
    simp only [SCV.realToComplex_apply]
    rw [map_add, map_mul]
    simp
    ring
  · intro i
    rw [show
      reflectedDiagonalComplexCLE m (SCV.realToComplex x) =
        reflectedDiagonalComplexLinearMap m (SCV.realToComplex x) by rfl]
    rw [reflectedDiagonalComplexLinearMap_right,
      reflectedCauchyIncrement_right]
    rfl

/-- Equality of two holomorphic functions on a reflected diagonal open patch
determines them on the complete connected doubled polydisc. -/
theorem eqOn_polydisc_of_eq_reflectedDiagonal
    {m : ℕ}
    {F G : (Fin (m + m) → ℂ) → ℂ}
    {R r : ℝ}
    (hR : 0 < R)
    (hr : 0 < r)
    (hrR : r ≤ R)
    (hF :
      DifferentiableOn ℂ F
        (SCV.Polydisc
          (0 : Fin (m + m) → ℂ) (fun _ => R)))
    (hG :
      DifferentiableOn ℂ G
        (SCV.Polydisc
          (0 : Fin (m + m) → ℂ) (fun _ => R)))
    (hdiag :
      ∀ z : Fin m → ℂ, ‖z‖ < r →
        F (reflectedCauchyIncrement z) =
          G (reflectedCauchyIncrement z)) :
    Set.EqOn F G
      (SCV.Polydisc
        (0 : Fin (m + m) → ℂ) (fun _ => R)) := by
  let L := reflectedDiagonalComplexCLE m
  let P :=
    SCV.Polydisc
      (0 : Fin (m + m) → ℂ) (fun _ => R)
  let U : Set (Fin (m + m) → ℂ) := L ⁻¹' P
  let F' : (Fin (m + m) → ℂ) → ℂ := F ∘ L
  let G' : (Fin (m + m) → ℂ) → ℂ := G ∘ L
  let V : Set (Fin (m + m) → ℝ) :=
    Metric.ball 0 (r / 2)
  have hP_open : IsOpen P :=
    SCV.polydisc_isOpen
  have hP_connected : IsConnected P :=
    SCV.polydisc_convex.isConnected
      ⟨0, SCV.center_mem_polydisc (fun _ => hR)⟩
  have hU_open : IsOpen U :=
    hP_open.preimage L.continuous
  have hU_connected : IsConnected U :=
    L.toHomeomorph.isConnected_preimage.mpr hP_connected
  have hF' : DifferentiableOn ℂ F' U :=
    hF.comp L.differentiable.differentiableOn
      (Set.mapsTo_preimage L P)
  have hG' : DifferentiableOn ℂ G' U :=
    hG.comp L.differentiable.differentiableOn
      (Set.mapsTo_preimage L P)
  have hV_open : IsOpen V :=
    Metric.isOpen_ball
  have hV_nonempty : V.Nonempty := by
    exact ⟨0, Metric.mem_ball_self (half_pos hr)⟩
  have hreal_norm :
      ∀ x ∈ V,
        let z : Fin m → ℂ :=
          fun i =>
            (x (Fin.castAdd m i) : ℂ) +
              Complex.I * (x (Fin.natAdd m i) : ℂ)
        ‖z‖ < r := by
    intro x hx
    dsimp only
    have hxnorm : ‖x‖ < r / 2 := by
      simpa [V, Metric.mem_ball, dist_zero_right] using hx
    rw [pi_norm_lt_iff hr]
    intro i
    calc
      ‖(x (Fin.castAdd m i) : ℂ) +
          Complex.I * (x (Fin.natAdd m i) : ℂ)‖
          ≤ ‖(x (Fin.castAdd m i) : ℂ)‖ +
              ‖Complex.I * (x (Fin.natAdd m i) : ℂ)‖ :=
        norm_add_le _ _
      _ = |x (Fin.castAdd m i)| +
          |x (Fin.natAdd m i)| := by
        rw [norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖x‖ + ‖x‖ := by
        exact add_le_add
          (by simpa [Real.norm_eq_abs] using
            norm_le_pi_norm x (Fin.castAdd m i))
          (by simpa [Real.norm_eq_abs] using
            norm_le_pi_norm x (Fin.natAdd m i))
      _ < r := by linarith
  have hV_sub :
      ∀ x ∈ V,
        SCV.realToComplex x ∈ U := by
    intro x hx
    let z : Fin m → ℂ :=
      fun i =>
        (x (Fin.castAdd m i) : ℂ) +
          Complex.I * (x (Fin.natAdd m i) : ℂ)
    have hz : ‖z‖ < r :=
      hreal_norm x hx
    change L (SCV.realToComplex x) ∈ P
    rw [reflectedDiagonalComplexCLE_real]
    intro j
    change dist (reflectedCauchyIncrement z j) 0 < R
    rw [dist_zero_right]
    refine Fin.addCases ?_ ?_ j
    · intro i
      rw [reflectedCauchyIncrement_left]
      simpa using
        (norm_le_pi_norm z i).trans_lt (hz.trans_le hrR)
    · intro i
      rw [reflectedCauchyIncrement_right]
      exact
        (norm_le_pi_norm z i).trans_lt (hz.trans_le hrR)
  have hFG_real :
      ∀ x ∈ V,
        F' (SCV.realToComplex x) =
          G' (SCV.realToComplex x) := by
    intro x hx
    let z : Fin m → ℂ :=
      fun i =>
        (x (Fin.castAdd m i) : ℂ) +
          Complex.I * (x (Fin.natAdd m i) : ℂ)
    have hz : ‖z‖ < r :=
      hreal_norm x hx
    simpa [F', G', L, z, reflectedDiagonalComplexCLE_real] using
      hdiag z hz
  have hident :
      ∀ u ∈ U, F' u = G' u :=
    SCV.holomorphic_eq_of_eq_on_open_real_of_connected_finite
      hU_open hU_connected hF' hG'
      hV_open hV_nonempty hV_sub hFG_real
  intro w hw
  have hwU : L.symm w ∈ U := by
    simpa [U, P] using hw
  have heq := hident (L.symm w) hwU
  simpa [F', G'] using heq

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q : ℕ} [NeZero d]

/-- The mixed Gram identity for two source indices determines their complete
reflected pair kernel on the common origin polydisc. -/
theorem cauchy_scalar_eqOn_reflectedHilbertPairKernel
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι →
      euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f)
    (G : UniformCompactTimeMixedHilbertGramFamilyData
      OS f stage germ)
    (a b : ι) :
    Set.EqOn (G.cauchy a b).scalar
      (reflectedHilbertPairKernel
        (G.hilbert.field a) (G.hilbert.field b))
      (SCV.Polydisc
        (0 : Fin ((q + 1) + (q + 1)) → ℂ)
        (fun _ => G.gramRadius)) := by
  have hscalar :
      DifferentiableOn ℂ (G.cauchy a b).scalar
        (SCV.Polydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ)
          (fun _ => G.gramRadius)) := by
    apply (G.cauchy_holomorphic a b).mono
    intro w hw
    apply G.cauchy_closed a b
    rw [G.cauchy_center a b, G.cauchy_radius a b]
    apply SCV.closedPolydisc_mono
      (fun _ => le_of_lt G.gramRadius_lt_cauchy)
    exact SCV.polydisc_subset_closedPolydisc hw
  have hkernel :
      DifferentiableOn ℂ
        (reflectedHilbertPairKernel
          (G.hilbert.field a) (G.hilbert.field b))
        (SCV.Polydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ)
          (fun _ => G.gramRadius)) := by
    have hfull :=
      reflectedHilbertPairKernel_holomorphic
        SCV.polydisc_isOpen SCV.polydisc_isOpen
        (G.hilbert.holomorphic a)
        (G.hilbert.holomorphic b)
    apply hfull.mono
    rw [show
      reflectedHilbertPairKernelDomain
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => G.hilbert.radius))
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => G.hilbert.radius)) =
        reflectedHilbertKernelDomain
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => G.hilbert.radius)) by rfl]
    rw [reflectedHilbertKernelDomain_polydisc]
    have hzero :
        reflectedCauchyCenter
            (0 : Fin (q + 1) → ℂ) =
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) := by
      ext j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp
      · intro i
        simpa using
          reflectedCauchyCenter_right
            (0 : Fin (q + 1) → ℂ) i
    rw [hzero]
    exact
      SCV.polydisc_mono
        (fun _ => le_of_lt G.gramRadius_lt_hilbert)
  apply
    eqOn_polydisc_of_eq_reflectedDiagonal
      G.gramRadius_pos G.gramRadius_pos le_rfl
      hscalar hkernel
  intro z hz
  have hinner := G.mixed_inner a b z hz
  rw [G.cauchy_center a b, zero_add] at hinner
  have hleft :
      star (fun i =>
        reflectedCauchyIncrement z
          (Fin.castAdd (q + 1) i)) = z := by
    funext i
    simp
  have hright :
      (fun i =>
        reflectedCauchyIncrement z
          (Fin.natAdd (q + 1) i)) = z := by
    funext i
    exact reflectedCauchyIncrement_right z i
  rw [reflectedHilbertPairKernel, hleft, hright]
  exact hinner.symm

end UniformCompactTimeMixedHilbertGramFamilyData

end OSIIChapterV
end OSReconstruction
