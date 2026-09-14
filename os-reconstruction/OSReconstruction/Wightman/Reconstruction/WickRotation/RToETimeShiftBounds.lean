/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEReflectedClusterClosure
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketGrowth
import OSReconstruction.SCV.MultipleReflection

/-!
# Uniform Reflected Time-Shift Bounds

Ordinary continuity on the zero-diagonal space gives polynomial growth of a
translated fixed source. Sharp reflected Cauchy-Schwarz and translation
covariance give the doubling inequality, so multiple reflection removes
positive-time growth. The resulting two-source bound is uniform in independent
positive time shifts and arbitrary spatial separation. The time orbit also
has a Cauchy tail in the reflected seminorm, proved through the nonnegative
limit of its decreasing diagonal function.

No full OS record, clustering premise, or full-Schwartz Euclidean extension is
assumed. Extending clustering to arbitrary zero-diagonal block tests remains
a separate obligation.
-/

noncomputable section

open scoped Topology NNReal
open Set Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

local instance (n : ℕ) : AddCommGroup (ZeroDiagonalSchwartz d n) :=
  inferInstanceAs (AddCommGroup ↥(zeroDiagonalSubmodule d n))

omit [NeZero d] in
private theorem zeroDiagonalCLM_finite_bound {n : ℕ}
    (L : ZeroDiagonalSchwartz d n →L[ℂ] ℂ) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ZeroDiagonalSchwartz d n,
      ‖L f‖ ≤ C * (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1 := by
  let p := (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ).comp
    (zeroDiagonalSubmodule d n).subtype
  let q := (normSeminorm ℂ ℂ).comp L.toLinearMap
  have hp : WithSeminorms p := Topology.IsInducing.withSeminorms
    (schwartz_withSeminorms ℂ (NPointDomain d n) ℂ) Topology.IsInducing.subtypeVal
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, _, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  let r := s.sup (fun j : ℕ × ℕ => max j.1 j.2)
  refine ⟨r, C, C.2, fun f => ?_⟩
  have hsmall : s.sup p f ≤ (Finset.Iic (r, r)).sup
      (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1 := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    have hjr := Finset.le_sup (f := fun j : ℕ × ℕ => max j.1 j.2) hj
    change SchwartzMap.seminorm ℝ j.1 j.2 f.1 ≤ _
    apply Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) (i := j)
    exact Finset.mem_Iic.mpr
      ⟨(le_max_left _ _).trans hjr, (le_max_right _ _).trans hjr⟩
  exact (hbound f).trans (mul_le_mul_of_nonneg_left hsmall C.2)

private theorem zeroDiagonalCLM_translate_polynomial_bound {n : ℕ}
    (L : ZeroDiagonalSchwartz d n →L[ℂ] ℂ)
    (f : SchwartzNPoint d n) (v : NPointDomain d n) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ∀ g : ZeroDiagonalSchwartz d n,
        g.1 = translateSchwartzConfiguration (t • v) f → ‖L g‖ ≤ C * t ^ r := by
  obtain ⟨r, C, hC, hbound⟩ := zeroDiagonalCLM_finite_bound L
  let Q := (Finset.Iic (r, r)).sup
    (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ)
  have hQ : 0 ≤ Q f := apply_nonneg _ _
  refine ⟨r, C * 2 ^ r * (1 + ‖v‖) ^ r * Q f, by positivity, ?_⟩
  intro t ht g hg
  have ht0 : 0 ≤ t := by linarith
  have hscale : 1 + ‖t • v‖ ≤ t * (1 + ‖v‖) := by
    rw [norm_smul, Real.norm_of_nonneg ht0]
    nlinarith
  calc
    ‖L g‖ ≤ C * Q g.1 := hbound g
    _ = C * Q (translateSchwartzConfiguration (t • v) f) := by rw [hg]
    _ ≤ C * (2 ^ r * (1 + ‖t • v‖) ^ r * Q f) :=
      mul_le_mul_of_nonneg_left
        (osiiFiniteSchwartzSeminorm_translateSchwartzConfiguration_le r (t • v) f) hC
    _ ≤ C * (2 ^ r * (t * (1 + ‖v‖)) ^ r * Q f) := by gcongr
    _ = (C * 2 ^ r * (1 + ‖v‖) ^ r * Q f) * t ^ r := by rw [mul_pow]; ring

omit [NeZero d] in
private theorem timeShift_zero {n : ℕ} (f : SchwartzNPoint d n) :
    timeShiftSchwartzNPoint (d := d) 0 f = f := by
  ext x
  simp

private def orderedTimeShift {n : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨timeShiftSchwartzNPoint (d := d) t f.1, by
    rcases eq_or_lt_of_le ht with rfl | ht'
    · simpa only [timeShift_zero] using f.2
    · exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport t ht' f.1 f.2⟩

private theorem reflected_timeShift_pairing (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (s t : ℝ) :
    wickRotatedBoundaryPairing Wfn (n + m)
      ((timeShiftSchwartzNPoint (d := d) s f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t g)) =
    wickRotatedBoundaryPairing Wfn (n + m)
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (s + t) g)) := by
  symm
  apply wickRotatedBoundaryPairing_translation_invariant Wfn (n + m) (timeShiftVec d s)
  intro x
  change ((timeShiftSchwartzNPoint (d := d) s f).osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t g)) x =
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (s + t) g))
      (fun i => x i + timeShiftVec d s)
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, timeShiftSchwartzNPoint_apply]
  congr
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, timeReflection, splitFirst, timeShiftVec]
      ring
    · simp [timeReflectionN, timeReflection, splitFirst, timeShiftVec, hμ]
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitLast, timeShiftVec]
      ring
    · simp [splitLast, timeShiftVec, hμ]

private def shiftedSelf (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (t : ℝ) : ℂ :=
  wickRotatedBoundaryPairing Wfn (n + n)
    ((timeShiftSchwartzNPoint (d := d) t f.1).osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t f.1))

private theorem shiftedSelf_eq (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (t : ℝ) :
    shiftedSelf Wfn f t = wickRotatedBoundaryPairing Wfn (n + n)
      (f.1.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (2 * t) f.1)) := by
  simpa only [shiftedSelf, two_mul] using reflected_timeShift_pairing Wfn f.1 f.1 t t

private theorem re_mul_le_norm (p q : ℂ) : p.re * q.re ≤ ‖p‖ * ‖q‖ := by
  calc
    p.re * q.re ≤ |p.re * q.re| := le_abs_self _
    _ = |p.re| * |q.re| := abs_mul _ _
    _ ≤ ‖p‖ * ‖q‖ := mul_le_mul (Complex.abs_re_le_norm p)
      (Complex.abs_re_le_norm q) (abs_nonneg _) (norm_nonneg _)

private theorem shiftedSelf_doubling (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (t : ℝ) (ht : 0 < t) :
    ‖shiftedSelf Wfn f t‖ ^ 2 ≤
      ‖shiftedSelf Wfn f 0‖ * ‖shiftedSelf Wfn f (2 * t)‖ := by
  let g := orderedTimeShift (2 * t) (by linarith : 0 ≤ 2 * t) f
  have hpair : rToEReflectedPairing Wfn f g = shiftedSelf Wfn f t := by
    simpa only [rToEReflectedPairing_apply, g, orderedTimeShift] using
      (shiftedSelf_eq Wfn f t).symm
  have hff : rToEReflectedPairing Wfn f f = shiftedSelf Wfn f 0 := by
    simp only [rToEReflectedPairing_apply, shiftedSelf, timeShift_zero]
  have hgg : rToEReflectedPairing Wfn g g = shiftedSelf Wfn f (2 * t) := rfl
  have hbound := rToE_reflected_pairing_cauchy_schwarz Wfn f g
  have hnorm := re_mul_le_norm (rToEReflectedPairing Wfn f f) (rToEReflectedPairing Wfn g g)
  rw [hpair, hff, hgg] at hbound
  rw [hff, hgg] at hnorm
  nlinarith

private theorem shiftedSelf_polynomial (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖shiftedSelf Wfn f t‖ ≤ C * t ^ r := by
  let K := f.1.osConjTensorProduct f.1
  let v : NPointDomain d (n + n) :=
    fun i => if n ≤ i.val then (-2 : ℝ) • timeShiftVec d 1 else 0
  obtain ⟨r, C, hC, hbound⟩ :=
    zeroDiagonalCLM_translate_polynomial_bound (rToESchwingerCLM Wfn (n + n)) K v
  refine ⟨r, C, hC, fun t ht => ?_⟩
  let g := orderedTimeShift (2 * t) (by linarith : 0 ≤ 2 * t) f
  let P : ZeroDiagonalSchwartz d (n + n) :=
    ⟨f.1.osConjTensorProduct g.1,
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (f := f.1) (g := g.1) f.2 g.2⟩
  have hP : P.1 = translateSchwartzConfiguration (t • v) K := by
    ext x
    change (f.1.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (2 * t) f.1)) x =
      K (x + t • v)
    rw [osConjTensorProduct_timeShift_eq_tailShift]
    congr 1
    ext i μ
    by_cases hi : n ≤ i.val <;> by_cases hμ : μ = 0
    · subst hμ
      simp [v, hi, timeShiftVec]
      ring
    · simp [v, hi, timeShiftVec, hμ]
    · subst hμ
      simp [v, hi]
    · simp [v, hi]
  have h := hbound t ht P hP
  rwa [shiftedSelf_eq Wfn f t]

private theorem shiftedSelf_uniform_bound (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (t : ℝ) (ht : 0 ≤ t) :
    ‖shiftedSelf Wfn f t‖ ≤ ‖shiftedSelf Wfn f 0‖ := by
  by_cases ht0 : t = 0
  · rw [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  obtain ⟨r, C, hC, hpoly⟩ := shiftedSelf_polynomial Wfn f
  let N : ℝ → ℝ := fun s => ‖shiftedSelf Wfn f s‖
  have hD : SCV.MultipleReflection.HasDoublingBound N :=
    ⟨fun _ _ => norm_nonneg _, norm_nonneg _, shiftedSelf_doubling Wfn f⟩
  have hlarge : ∀ s, 1 ≤ s → N s ≤ (C + 1) * s ^ (r : ℝ) := by
    intro s hs
    simp only [N, Real.rpow_natCast]
    exact (hpoly s hs).trans (mul_le_mul_of_nonneg_right (by linarith)
      (pow_nonneg (by linarith) _))
  exact SCV.MultipleReflection.contraction_of_doubling_and_growth N hD
    (C + 1) r (by linarith) (by positivity) hlarge t htpos

/-- Uniform positive-time control from Wightman data alone. This is a bound,
not full zero-diagonal clustering or an assumption of a complete OS record. -/
theorem rToE_reflected_timeShift_self_bound (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (t : ℝ) (ht : 0 ≤ t) :
    ‖wickRotatedBoundaryPairing Wfn (n + n)
      ((timeShiftSchwartzNPoint (d := d) t f.1).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t f.1))‖ ≤
      ‖rToEReflectedPairing Wfn f f‖ := by
  simpa only [shiftedSelf, timeShift_zero, rToEReflectedPairing_apply] using
    shiftedSelf_uniform_bound Wfn f t ht

private theorem reflected_spatialTranslate_self (Wfn : WightmanFunctions d) {n : ℕ}
    (f : SchwartzNPoint d n) (a : Fin d → ℝ) :
    wickRotatedBoundaryPairing Wfn (n + n)
      ((translateSchwartzNPoint (Fin.cons 0 a) f).osConjTensorProduct
        (translateSchwartzNPoint (Fin.cons 0 a) f)) =
      wickRotatedBoundaryPairing Wfn (n + n) (f.osConjTensorProduct f) := by
  symm
  apply wickRotatedBoundaryPairing_translation_invariant Wfn (n + n) (-Fin.cons 0 a)
  intro x
  change ((translateSchwartzNPoint (Fin.cons 0 a) f).osConjTensorProduct
      (translateSchwartzNPoint (Fin.cons 0 a) f)) x =
    (f.osConjTensorProduct f) (fun i => x i + -Fin.cons 0 a)
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, translateSchwartzNPoint_apply]
  have harg : (fun i => (timeReflectionN d (splitFirst n n x)) i - Fin.cons 0 a) =
      timeReflectionN d (splitFirst n n (fun i => x i + -Fin.cons 0 a)) := by
    ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, timeReflection, splitFirst]
    · simp [timeReflectionN, timeReflection, splitFirst, hμ, sub_eq_add_neg]
  rw [harg]
  rfl

/-- A single bound controls independent positive time shifts and arbitrary
spatial separation of two reflected sources. -/
theorem rToE_reflected_timeSpaceShift_pairing_bound (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (a : Fin d → ℝ) :
    ‖wickRotatedBoundaryPairing Wfn (n + m)
      ((timeShiftSchwartzNPoint (d := d) s f.1).osConjTensorProduct
        (translateSchwartzNPoint (Fin.cons 0 a)
          (timeShiftSchwartzNPoint (d := d) t g.1)))‖ ^ 2 ≤
      ‖rToEReflectedPairing Wfn f f‖ * ‖rToEReflectedPairing Wfn g g‖ := by
  let fs := orderedTimeShift s hs f
  let gt := orderedTimeShift t ht g
  let ga : euclideanPositiveTimeSubmodule (d := d) m :=
    ⟨translateSchwartzNPoint (Fin.cons 0 a) gt.1,
      translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (Fin.cons 0 a) (by simp) gt.1 gt.2⟩
  have hfg := rToE_reflected_pairing_cauchy_schwarz Wfn fs ga
  have hn := re_mul_le_norm (rToEReflectedPairing Wfn fs fs) (rToEReflectedPairing Wfn ga ga)
  have hf : ‖rToEReflectedPairing Wfn fs fs‖ ≤ ‖rToEReflectedPairing Wfn f f‖ :=
    rToE_reflected_timeShift_self_bound Wfn f s hs
  have hg : ‖rToEReflectedPairing Wfn ga ga‖ ≤ ‖rToEReflectedPairing Wfn g g‖ := by
    change ‖wickRotatedBoundaryPairing Wfn (m + m)
      ((translateSchwartzNPoint (Fin.cons 0 a) gt.1).osConjTensorProduct
        (translateSchwartzNPoint (Fin.cons 0 a) gt.1))‖ ≤ _
    rw [reflected_spatialTranslate_self]
    exact rToE_reflected_timeShift_self_bound Wfn g t ht
  exact (hfg.trans hn).trans
    (mul_le_mul hf hg (norm_nonneg _) (norm_nonneg _))

private theorem reflected_self_nonneg (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    0 ≤ (rToEReflectedPairing Wfn f f).re := by
  let F := PositiveTimeBorchersSequence.single n f.1 f.2
  have h := rToE_schwingerExtension_os_positivity Wfn F.toBorchersSequence F.ordered_tsupport
  change 0 ≤ (OSInnerProduct d (constructSchwingerFunctions Wfn)
    (BorchersSequence.single n f.1) (BorchersSequence.single n f.1)).re at h
  rw [OSInnerProduct_single_single d _ (constructedZeroDiagonalSchwinger_linear Wfn)] at h
  have hv := VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    (f := f.1) (g := f.1) f.2 f.2
  simpa only [constructSchwingerFunctions,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _ hv,
    rToEReflectedPairing_apply] using h

private theorem reflected_self_norm (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    rToEReflectedPairing Wfn f f = (‖rToEReflectedPairing Wfn f f‖ : ℂ) := by
  let z := rToEReflectedPairing Wfn f f
  have h := rToE_reflected_pairing_cauchy_schwarz Wfn f f
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hi : z.im = 0 := by
    change ‖z‖ ^ 2 ≤ z.re * z.re at h
    nlinarith [sq_nonneg z.im]
  have hre : 0 ≤ z.re := reflected_self_nonneg Wfn f
  have hreal : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hi)
  change z = (‖z‖ : ℂ)
  rw [hreal, Complex.norm_of_nonneg hre]

omit [NeZero d] in
private theorem timeShift_add {n : ℕ} (s t : ℝ) (f : SchwartzNPoint d n) :
    timeShiftSchwartzNPoint (d := d) s (timeShiftSchwartzNPoint (d := d) t f) =
      timeShiftSchwartzNPoint (d := d) (s + t) f := by
  ext x
  simp only [timeShiftSchwartzNPoint_apply]
  congr 1
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeShiftVec]
    ring
  · simp [timeShiftVec, hμ]

private theorem shiftedSelf_antitone (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    Antitone (fun t : ℝ≥0 => ‖shiftedSelf Wfn f t‖) := by
  intro s t hst
  have h := rToE_reflected_timeShift_self_bound Wfn
    (orderedTimeShift s s.2 f) (t - s) (sub_nonneg.mpr hst)
  simpa only [orderedTimeShift, timeShift_add, sub_add_cancel,
    rToEReflectedPairing_apply, shiftedSelf] using h

private theorem shiftedSelf_norm_eq (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (t : ℝ) (ht : 0 ≤ t) :
    shiftedSelf Wfn f t = (‖shiftedSelf Wfn f t‖ : ℂ) :=
  reflected_self_norm Wfn (orderedTimeShift t ht f)

private theorem reflected_sub_self (Wfn : WightmanFunctions d) {n : ℕ}
    (f g : euclideanPositiveTimeSubmodule (d := d) n) :
    rToEReflectedPairing Wfn (f - g) (f - g) =
      rToEReflectedPairing Wfn f f - rToEReflectedPairing Wfn f g -
        rToEReflectedPairing Wfn g f + rToEReflectedPairing Wfn g g := by
  let K (u v : euclideanPositiveTimeSubmodule (d := d) n) :
      ZeroDiagonalSchwartz d (n + n) :=
    ⟨u.1.osConjTensorProduct v.1,
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (f := u.1) (g := v.1) u.2 v.2⟩
  have hK : K (f - g) (f - g) = K f f - K f g - K g f + K g g := by
    apply Subtype.ext
    ext x
    change ((f.1 - g.1).osConjTensorProduct (f.1 - g.1)) x =
      (f.1.osConjTensorProduct f.1) x - (f.1.osConjTensorProduct g.1) x -
        (g.1.osConjTensorProduct f.1) x + (g.1.osConjTensorProduct g.1) x
    simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
      SchwartzNPoint.osConj_apply]
    ring
  change rToESchwingerCLM Wfn (n + n) (K (f - g) (f - g)) = _
  rw [hK, map_add, map_sub, map_sub]
  rfl

private theorem reflected_timeShift_midpoint (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    rToEReflectedPairing Wfn (orderedTimeShift s hs f) (orderedTimeShift t ht f) =
      shiftedSelf Wfn f ((s + t) / 2) := by
  change wickRotatedBoundaryPairing Wfn (n + n)
    ((timeShiftSchwartzNPoint (d := d) s f.1).osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t f.1)) = _
  rw [reflected_timeShift_pairing, shiftedSelf_eq,
    show 2 * ((s + t) / 2) = s + t by ring]

private theorem reflected_timeShift_distance (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖rToEReflectedPairing Wfn
      (orderedTimeShift s hs f - orderedTimeShift t ht f)
      (orderedTimeShift s hs f - orderedTimeShift t ht f)‖ =
    ‖shiftedSelf Wfn f s‖ + ‖shiftedSelf Wfn f t‖ -
      2 * ‖shiftedSelf Wfn f ((s + t) / 2)‖ := by
  have hd := congrArg Complex.re (reflected_self_norm Wfn
    (orderedTimeShift s hs f - orderedTimeShift t ht f))
  rw [Complex.ofReal_re] at hd
  rw [← hd, reflected_sub_self,
    reflected_timeShift_midpoint Wfn f s t hs ht,
    reflected_timeShift_midpoint Wfn f t s ht hs, add_comm t s]
  change ((shiftedSelf Wfn f s) - shiftedSelf Wfn f ((s + t) / 2) -
    shiftedSelf Wfn f ((s + t) / 2) + shiftedSelf Wfn f t).re = _
  rw [shiftedSelf_norm_eq Wfn f s hs, shiftedSelf_norm_eq Wfn f t ht,
    shiftedSelf_norm_eq Wfn f ((s + t) / 2) (by positivity)]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.norm_real, norm_norm]
  ring

/-- Late positive-time translates form a Cauchy tail in the reflected
seminorm. This does not assert Schwartz convergence or full E4. -/
theorem rToE_reflected_timeShift_cauchy_tail (Wfn : WightmanFunctions d) {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ s t : ℝ, T ≤ s → T ≤ t →
      ‖wickRotatedBoundaryPairing Wfn (n + n)
        ((timeShiftSchwartzNPoint (d := d) s f.1 -
          timeShiftSchwartzNPoint (d := d) t f.1).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s f.1 -
          timeShiftSchwartzNPoint (d := d) t f.1))‖ < ε := by
  let N : ℝ≥0 → ℝ := fun t => ‖shiftedSelf Wfn f t‖
  have hb : BddBelow (Set.range N) := ⟨0, by rintro _ ⟨t, rfl⟩; exact norm_nonneg _⟩
  let l := ⨅ t, N t
  have hlim : Tendsto N atTop (𝓝 l) :=
    tendsto_atTop_ciInf (shiftedSelf_antitone Wfn f) hb
  have he : ∀ᶠ t in atTop, N t < l + ε / 2 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.1 he
  refine ⟨T, T.2, fun s t hs ht => ?_⟩
  have hs0 : 0 ≤ s := T.2.trans hs
  have ht0 : 0 ≤ t := T.2.trans ht
  have hNs := hT ⟨s, hs0⟩ hs
  have hNt := hT ⟨t, ht0⟩ ht
  have hNm : l ≤ N ⟨(s + t) / 2, by positivity⟩ := ciInf_le hb _
  have hd := reflected_timeShift_distance Wfn f s t hs0 ht0
  change ‖wickRotatedBoundaryPairing Wfn (n + n)
    ((timeShiftSchwartzNPoint (d := d) s f.1 -
      timeShiftSchwartzNPoint (d := d) t f.1).osConjTensorProduct
    (timeShiftSchwartzNPoint (d := d) s f.1 -
      timeShiftSchwartzNPoint (d := d) t f.1))‖ = _ at hd
  rw [hd]
  change ‖shiftedSelf Wfn f s‖ < l + ε / 2 at hNs
  change ‖shiftedSelf Wfn f t‖ < l + ε / 2 at hNt
  change l ≤ ‖shiftedSelf Wfn f ((s + t) / 2)‖ at hNm
  linarith

end OSReconstruction
