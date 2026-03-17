/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesSCV
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.SemigroupBochner
import OSReconstruction.SCV.MultipleReflection
import OSReconstruction.vNA.Bochner.SemigroupRoots
import OSReconstruction.vNA.Spectral.ComplexSemigroup
import OSReconstruction.vNA.Spectral.SelfAdjointFunctionalViaRMK
import OSReconstruction.vNA.Unbounded.BoundedBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# OS to Wightman Semigroup Core

Phase 2 of the `E'→R'` reconstruction chain: the honest OS Hilbert-space
semigroup, its spectral/Laplace bridge, and the one-variable holomorphic
matrix-element package built from Euclidean time translation.

The critical point is that the Euclidean input is honest Schwinger data on the
zero-diagonal test space `°S`, while the Wightman output is a full tempered
distribution family on Schwartz space. That jump is the heart of OS
reconstruction; it must not be smuggled into the Euclidean hypothesis by
quietly assuming a full-Schwartz Schwinger theory from the start.

- Phase 2: Euclidean time translation semigroup

The downstream analytic-continuation stack is now split across:
- `OSToWightmanBase.lean` for shared geometry and coordinate infrastructure,
- `OSToWightmanKernel.lean` for the specialized `k = 2` holomorphic-kernel
  route,
- `OSToWightman.lean` for the general continuation core and wrappers, and
- `OSToWightmanBoundaryValues.lean` for the boundary-value/transfer package.
-/

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ### OS to Wightman (Theorem E'→R') -/

/-- Phase 2: The Euclidean time translation semigroup.

    For t > 0, define the operator T(t) on the Hilbert space by:
      T(t) [f](τ₁,...,τₙ) = [f(τ₁ + t,..., τₙ + t)]

    On the honest Euclidean quotient `OSPreHilbertSpace OS`, this gives a
    target contraction semigroup with:
    - T(s)T(t) = T(s+t)
    - ‖T(t)‖ ≤ 1 (the extra positivity/contractivity input needed to force
      nonnegative spectral support)
    - T(t) → I as t → 0⁺ (strong continuity, from E0)

    By the Hille-Yosida theorem, T(t) = e^{-tH} where H ≥ 0 is self-adjoint.
    This H is the Hamiltonian of the reconstructed QFT.

    The current honest gap is precisely the contraction/spectral-support step:
    the quotient kernel is semigroup-positive-definite, but that alone still
    allows exponentially growing examples like `t ↦ exp (a t)`. -/
structure EuclideanSemigroup (OS : OsterwalderSchraderAxioms d) where
  /-- The semigroup operator for positive Euclidean times on the honest OS quotient. -/
  T : ∀ t : ℝ, 0 < t → OSPreHilbertSpace OS →ₗ[ℂ] OSPreHilbertSpace OS
  /-- Semigroup property: T(s) ∘ T(t) = T(s+t) for positive times. -/
  semigroup : ∀ s t : ℝ, ∀ hs : 0 < s, ∀ ht : 0 < t,
    (T s hs).comp (T t ht) = T (s + t) (add_pos hs ht)
  /-- Contraction: ‖T(t)x‖ ≤ ‖x‖ on the honest Euclidean quotient. -/
  contraction : ∀ t : ℝ, ∀ ht : 0 < t, ∀ x : OSPreHilbertSpace OS,
    ‖(T t ht) x‖ ≤ ‖x‖
  /-- Positivity of Euclidean time translation matrix elements. -/
  positive : ∀ t : ℝ, ∀ ht : 0 < t, ∀ x : OSPreHilbertSpace OS,
    0 ≤ RCLike.re
      (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((T t ht) x))

namespace EuclideanSemigroup

variable {OS : OsterwalderSchraderAxioms d}

/-- Matrix elements of a contraction semigroup are uniformly bounded by the norm
square of the vector. This is the extra control absent from bare
semigroup-positive-definiteness. -/
theorem kernel_norm_le_norm_sq (E : EuclideanSemigroup OS)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((E.T t ht) x)‖ ≤ ‖x‖ ^ 2 := by
  calc
    ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((E.T t ht) x)‖ ≤ ‖x‖ * ‖(E.T t ht) x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left (E.contraction t ht x) (norm_nonneg _)
    _ = ‖x‖ ^ 2 := by ring

/-- The real part of a contraction-semigroup matrix element is bounded above by
the same norm square. -/
theorem kernel_re_le_norm_sq (E : EuclideanSemigroup OS)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    RCLike.re
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((E.T t ht) x)) ≤ ‖x‖ ^ 2 := by
  calc
    RCLike.re
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((E.T t ht) x)) ≤
        ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((E.T t ht) x)‖ := RCLike.re_le_norm _
    _ ≤ ‖x‖ ^ 2 := E.kernel_norm_le_norm_sq t ht x

end EuclideanSemigroup

abbrev timeShiftVec (d : ℕ) (t : ℝ) : SpacetimeDim d :=
  fun μ => if μ = 0 then t else 0

omit [NeZero d] in
private theorem timeShiftConfig_eq_smul {m : ℕ} (t : ℝ) :
    (fun _ : Fin m => timeShiftVec d t : NPointDomain d m) =
      t • (fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m) := by
  funext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeShiftVec]
  · simp [timeShiftVec, hμ]

omit [NeZero d] in
private theorem norm_timeShiftConfig_eq_mul {m : ℕ} (t : ℝ) :
    ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖ =
      ‖t‖ * ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖ := by
  rw [timeShiftConfig_eq_smul (d := d) (m := m) t]
  simpa using (norm_smul t (fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m))

omit [NeZero d] in
private theorem one_add_norm_timeShiftConfig_pow_le {m s : ℕ} (t : ℝ) (ht : 1 ≤ t) :
    (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ s ≤
      (1 + ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖) ^ s * t ^ s := by
  have ht0 : 0 ≤ t := by linarith
  have hcfg :
      ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖ =
        t * ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖ := by
    rw [norm_timeShiftConfig_eq_mul (d := d) (m := m) t, Real.norm_of_nonneg ht0]
  have hbase :
      1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖ ≤
        t * (1 + ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖) := by
    rw [hcfg]
    have hD : 0 ≤ ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖ := norm_nonneg _
    nlinarith
  calc
    (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ s
      ≤ (t * (1 + ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖)) ^ s := by
          exact pow_le_pow_left₀ (by positivity) hbase s
    _ = (1 + ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖) ^ s * t ^ s := by
      rw [mul_pow, mul_comm]

abbrev translateNPointDomain (a : SpacetimeDim d) {n : ℕ} :
    NPointDomain d n → NPointDomain d n :=
  fun x i => x i - a

omit [NeZero d] in
private theorem continuous_translateNPointDomain (a : SpacetimeDim d) {n : ℕ} :
    Continuous (translateNPointDomain (d := d) (n := n) a) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).sub continuous_const

omit [NeZero d] in
private def translateNPointDomainHomeomorph (a : SpacetimeDim d) {n : ℕ} :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toFun := translateNPointDomain (d := d) (n := n) a
  invFun := translateNPointDomain (d := d) (n := n) (-a)
  left_inv x := by
    ext i μ
    simp [translateNPointDomain, sub_eq_add_neg]
  right_inv x := by
    ext i μ
    simp [translateNPointDomain, sub_eq_add_neg]
  continuous_toFun := continuous_translateNPointDomain (d := d) (n := n) a
  continuous_invFun := continuous_translateNPointDomain (d := d) (n := n) (-a)

omit [NeZero d] in
private theorem tsupport_precomp_subset {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

omit [NeZero d] in
private theorem translateNPointDomain_antilipschitz (a : SpacetimeDim d) {n : ℕ} :
    AntilipschitzWith 1 (translateNPointDomain (d := d) (n := n) a) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro x y
  have hsub :
      x - y = translateNPointDomain (d := d) (n := n) a x -
        translateNPointDomain (d := d) (n := n) a y := by
    ext i μ
    simp [translateNPointDomain, sub_eq_add_neg]
    abel_nf
  simpa [one_mul, dist_eq_norm] using le_of_eq (congrArg norm hsub)

omit [NeZero d] in
private theorem translateNPointDomain_hasTemperateGrowth (a : SpacetimeDim d) {n : ℕ} :
    Function.HasTemperateGrowth (translateNPointDomain (d := d) (n := n) a) := by
  let c : NPointDomain d n := fun _ => -a
  have hconst : Function.HasTemperateGrowth (fun _ : NPointDomain d n => c) :=
    Function.HasTemperateGrowth.const c
  have hid : Function.HasTemperateGrowth (fun x : NPointDomain d n => x) := by
    simpa using (ContinuousLinearMap.id ℝ (NPointDomain d n)).hasTemperateGrowth
  simpa [translateNPointDomain, c, sub_eq_add_neg, Pi.add_apply] using hid.add hconst

abbrev translateSchwartzNPoint (a : SpacetimeDim d) {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (translateNPointDomain_hasTemperateGrowth (d := d) (n := n) a)
    (translateNPointDomain_antilipschitz (d := d) (n := n) a)

omit [NeZero d] in
@[simp] theorem translateSchwartzNPoint_apply (a : SpacetimeDim d) {n : ℕ}
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    translateSchwartzNPoint (d := d) a f x = f (fun i => x i - a) := by
  simp [translateSchwartzNPoint]

abbrev timeShiftSchwartzNPoint (t : ℝ) {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  translateSchwartzNPoint (d := d) (timeShiftVec d t)

omit [NeZero d] in
@[simp] theorem timeShiftSchwartzNPoint_apply (t : ℝ) {n : ℕ}
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    timeShiftSchwartzNPoint (d := d) t f x =
      f (fun i => x i - timeShiftVec d t) := by
  simp [timeShiftSchwartzNPoint, translateSchwartzNPoint_apply]

omit [NeZero d] in
theorem translateSchwartzNPoint_timeShiftSchwartzNPoint
    (a : SpacetimeDim d) (t : ℝ) {n : ℕ} (f : SchwartzNPoint d n) :
    translateSchwartzNPoint (d := d) a (timeShiftSchwartzNPoint (d := d) t f) =
      timeShiftSchwartzNPoint (d := d) t (translateSchwartzNPoint (d := d) a f) := by
  ext x
  simp [translateSchwartzNPoint_apply, timeShiftSchwartzNPoint_apply, sub_eq_add_neg,
    Pi.add_apply, add_comm, add_left_comm, add_assoc]

/-- Euclidean time translation has polynomial Schwartz-seminorm growth. -/
private theorem seminorm_timeShiftSchwartzNPoint_le (k l : ℕ) (t : ℝ) {n : ℕ}
    (f : SchwartzNPoint d n) :
    SchwartzMap.seminorm ℝ k l (timeShiftSchwartzNPoint (d := d) t f) ≤
      2 ^ (k - 1) *
        (SchwartzMap.seminorm ℝ k l f +
          ‖(fun _ : Fin n => timeShiftVec d t : NPointDomain d n)‖ ^ k *
            SchwartzMap.seminorm ℝ 0 l f) := by
  refine SchwartzMap.seminorm_le_bound ℝ k l _ (by positivity) ?_
  intro x
  let a : NPointDomain d n := fun _ => -timeShiftVec d t
  have hfun :
      (fun z : NPointDomain d n => f (fun i => z i - timeShiftVec d t)) =
        fun z : NPointDomain d n => f (z + a) := by
    funext z
    have hz : (fun i => z i - timeShiftVec d t) = z + a := by
      funext i
      simp [a, sub_eq_add_neg]
    rw [hz]
  have hderiv :
      iteratedFDeriv ℝ l
          (fun z : NPointDomain d n => f (fun i => z i - timeShiftVec d t)) x =
        iteratedFDeriv ℝ l f.toFun (x + a) := by
    rw [hfun]
    simpa using (iteratedFDeriv_comp_add_right (f := f.toFun) l a x)
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by
        congr 1
        ext i μ
        simp [a]
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  have hC0 : ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ ≤ SchwartzMap.seminorm ℝ 0 l f := by
    simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm ℝ 0 l f (x + a)
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ l
            (fun z : NPointDomain d n => f (fun i => z i - timeShiftVec d t)) x‖
      = ‖x‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by rw [hderiv]
    _ ≤ (‖x + a‖ + ‖a‖) ^ k * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
      gcongr
    _ ≤ (2 ^ (k - 1) * (‖x + a‖ ^ k + ‖a‖ ^ k)) *
          ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
      gcongr
      exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
    _ = 2 ^ (k - 1) *
          (‖x + a‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ +
            ‖a‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖) := by ring
    _ ≤ 2 ^ (k - 1) *
          (SchwartzMap.seminorm ℝ k l f +
            ‖a‖ ^ k * SchwartzMap.seminorm ℝ 0 l f) := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact add_le_add
        (SchwartzMap.le_seminorm ℝ k l f (x + a))
        (mul_le_mul_of_nonneg_left hC0 (pow_nonneg (norm_nonneg _) _))
    _ = 2 ^ (k - 1) *
          (SchwartzMap.seminorm ℝ k l f +
            ‖(fun _ : Fin n => timeShiftVec d t : NPointDomain d n)‖ ^ k *
              SchwartzMap.seminorm ℝ 0 l f) := by
      have ha_norm :
          ‖a‖ = ‖(fun _ : Fin n => timeShiftVec d t : NPointDomain d n)‖ := by
        dsimp [a]
        rw [show (fun x : Fin n => -timeShiftVec d t) =
            -(fun _ : Fin n => timeShiftVec d t : NPointDomain d n) by
              funext i
              simp]
        simp
      rw [ha_norm]

/-- The OS test kernel `(\theta \bar f) \otimes \tau_t g` has polynomial
Schwartz-seminorm growth in the Euclidean time shift. This is the quantitative
input needed to combine `OSLinearGrowthCondition` with the quotient semigroup
recursion. -/
private theorem exists_seminorm_osConjTensorProduct_timeShift_le_polynomial
    (s : ℕ) {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ s s
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) ≤
        C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ s := by
  let A0 : ℕ → ℝ := fun i => 2 * SchwartzMap.seminorm ℝ 0 (s - i) g
  let As : ℕ → ℝ := fun i =>
    2 ^ (s - 1) *
      (SchwartzMap.seminorm ℝ s (s - i) g + SchwartzMap.seminorm ℝ 0 (s - i) g)
  let C : ℝ :=
    2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
      (SchwartzMap.seminorm ℝ s i f * A0 i + SchwartzMap.seminorm ℝ 0 i f * As i)
  refine ⟨C, by positivity, ?_⟩
  intro t
  let ρ : ℝ := ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖
  have hρ_nonneg : 0 ≤ ρ := norm_nonneg _
  have hpow_one : 1 ≤ (1 + ρ) ^ s := by
    exact one_le_pow₀ (by linarith)
  have hpow_ρ : ρ ^ s ≤ (1 + ρ) ^ s := by
    exact pow_le_pow_left₀ hρ_nonneg (by linarith) s
  have hshift0 :
      ∀ i ∈ Finset.range (s + 1),
        SchwartzMap.seminorm ℝ 0 (s - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          A0 i * (1 + ρ) ^ s := by
    intro i hi
    have hbase :
        SchwartzMap.seminorm ℝ 0 (s - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          2 * SchwartzMap.seminorm ℝ 0 (s - i) g := by
      simpa [two_mul, ρ, A0] using seminorm_timeShiftSchwartzNPoint_le
        (d := d) 0 (s - i) t g
    have hA0_nonneg : 0 ≤ A0 i := by
      dsimp [A0]
      positivity
    calc
      SchwartzMap.seminorm ℝ 0 (s - i) (timeShiftSchwartzNPoint (d := d) t g)
        ≤ A0 i := by simpa [A0] using hbase
      _ ≤ A0 i * (1 + ρ) ^ s := by
        simpa [one_mul] using mul_le_mul_of_nonneg_left hpow_one hA0_nonneg
  have hshiftS :
      ∀ i ∈ Finset.range (s + 1),
        SchwartzMap.seminorm ℝ s (s - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          As i * (1 + ρ) ^ s := by
    intro i hi
    have hbase :
        SchwartzMap.seminorm ℝ s (s - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          2 ^ (s - 1) *
            (SchwartzMap.seminorm ℝ s (s - i) g +
              ρ ^ s * SchwartzMap.seminorm ℝ 0 (s - i) g) := by
      simpa [ρ] using seminorm_timeShiftSchwartzNPoint_le
        (d := d) s (s - i) t g
    have hs_nonneg : 0 ≤ SchwartzMap.seminorm ℝ s (s - i) g := by positivity
    have h0_nonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 (s - i) g := by positivity
    calc
      SchwartzMap.seminorm ℝ s (s - i) (timeShiftSchwartzNPoint (d := d) t g)
        ≤ 2 ^ (s - 1) *
            (SchwartzMap.seminorm ℝ s (s - i) g +
              ρ ^ s * SchwartzMap.seminorm ℝ 0 (s - i) g) := hbase
      _ ≤ 2 ^ (s - 1) *
            ((1 + ρ) ^ s * SchwartzMap.seminorm ℝ s (s - i) g +
              (1 + ρ) ^ s * SchwartzMap.seminorm ℝ 0 (s - i) g) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine add_le_add ?_ ?_
        · simpa [one_mul, mul_comm] using
            (mul_le_mul_of_nonneg_right hpow_one hs_nonneg)
        · exact mul_le_mul_of_nonneg_right hpow_ρ h0_nonneg
      _ = As i * (1 + ρ) ^ s := by
        dsimp [As]
        ring
  have htensor :=
    SchwartzMap.tensorProduct_seminorm_le (p := s) (l := s) f.osConj
      (timeShiftSchwartzNPoint (d := d) t g)
  calc
    SchwartzMap.seminorm ℝ s s
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
      = SchwartzMap.seminorm ℝ s s
          (f.osConj.tensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
            rfl
    _ ≤ 2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
        (SchwartzMap.seminorm ℝ s i f.osConj *
            SchwartzMap.seminorm ℝ 0 (s - i) (timeShiftSchwartzNPoint (d := d) t g) +
          SchwartzMap.seminorm ℝ 0 i f.osConj *
            SchwartzMap.seminorm ℝ s (s - i) (timeShiftSchwartzNPoint (d := d) t g)) := htensor
    _ ≤ 2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
        (SchwartzMap.seminorm ℝ s i f * A0 i * (1 + ρ) ^ s +
          SchwartzMap.seminorm ℝ 0 i f * As i * (1 + ρ) ^ s) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
      intro i hi
      have hfS : SchwartzMap.seminorm ℝ s i f.osConj ≤ SchwartzMap.seminorm ℝ s i f :=
        SchwartzNPoint.seminorm_osConj_le (d := d) s i f
      have hf0 : SchwartzMap.seminorm ℝ 0 i f.osConj ≤ SchwartzMap.seminorm ℝ 0 i f :=
        SchwartzNPoint.seminorm_osConj_le (d := d) 0 i f
      have hchoose_nonneg : (0 : ℝ) ≤ ↑(s.choose i) := Nat.cast_nonneg _
      apply mul_le_mul_of_nonneg_left ?_ hchoose_nonneg
      refine add_le_add ?_ ?_
      · calc
          SchwartzMap.seminorm ℝ s i f.osConj *
              SchwartzMap.seminorm ℝ 0 (s - i) (timeShiftSchwartzNPoint (d := d) t g)
            ≤ SchwartzMap.seminorm ℝ s i f *
                SchwartzMap.seminorm ℝ 0 (s - i) (timeShiftSchwartzNPoint (d := d) t g) := by
                  exact mul_le_mul_of_nonneg_right hfS (by positivity)
          _ ≤ SchwartzMap.seminorm ℝ s i f * (A0 i * (1 + ρ) ^ s) := by
                  exact mul_le_mul_of_nonneg_left (hshift0 i hi) (by positivity)
          _ = SchwartzMap.seminorm ℝ s i f * A0 i * (1 + ρ) ^ s := by
                  ring
      · calc
          SchwartzMap.seminorm ℝ 0 i f.osConj *
              SchwartzMap.seminorm ℝ s (s - i) (timeShiftSchwartzNPoint (d := d) t g)
            ≤ SchwartzMap.seminorm ℝ 0 i f *
                SchwartzMap.seminorm ℝ s (s - i) (timeShiftSchwartzNPoint (d := d) t g) := by
                  exact mul_le_mul_of_nonneg_right hf0 (by positivity)
          _ ≤ SchwartzMap.seminorm ℝ 0 i f * (As i * (1 + ρ) ^ s) := by
                  exact mul_le_mul_of_nonneg_left (hshiftS i hi) (by positivity)
          _ = SchwartzMap.seminorm ℝ 0 i f * As i * (1 + ρ) ^ s := by
                  ring
    _ = C * (1 + ρ) ^ s := by
      dsimp [C]
      have hsum :
          ∑ i ∈ Finset.range (s + 1),
              ↑(s.choose i) *
                (SchwartzMap.seminorm ℝ s i f * A0 i * (1 + ρ) ^ s +
                  SchwartzMap.seminorm ℝ 0 i f * As i * (1 + ρ) ^ s) =
            (∑ i ∈ Finset.range (s + 1),
                ↑(s.choose i) *
                  (SchwartzMap.seminorm ℝ s i f * A0 i +
                    SchwartzMap.seminorm ℝ 0 i f * As i)) * (1 + ρ) ^ s := by
        calc
          ∑ i ∈ Finset.range (s + 1),
              ↑(s.choose i) *
                (SchwartzMap.seminorm ℝ s i f * A0 i * (1 + ρ) ^ s +
                  SchwartzMap.seminorm ℝ 0 i f * As i * (1 + ρ) ^ s)
            = ∑ i ∈ Finset.range (s + 1),
                (↑(s.choose i) *
                  (SchwartzMap.seminorm ℝ s i f * A0 i +
                    SchwartzMap.seminorm ℝ 0 i f * As i)) * (1 + ρ) ^ s := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
          _ = (∑ i ∈ Finset.range (s + 1),
                ↑(s.choose i) *
                  (SchwartzMap.seminorm ℝ s i f * A0 i +
                    SchwartzMap.seminorm ℝ 0 i f * As i)) * (1 + ρ) ^ s := by
                  rw [Finset.sum_mul]
      rw [hsum]
      ring
    _ = C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ s := by
      simp [ρ]

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg_aux
    {n : ℕ} (t : ℝ) (ht : 0 ≤ t) (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((timeShiftSchwartzNPoint (d := d) t f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  intro x hx
  have hxpre :
      (fun i => x i - timeShiftVec d t) ∈
        tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_precomp_subset
      (f := ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (h := translateNPointDomain (d := d) (n := n) (timeShiftVec d t))
      (continuous_translateNPointDomain (d := d) (n := n) (timeShiftVec d t)) hx
  have hord := hf hxpre
  intro i
  constructor
  · have hi := (hord i).1
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t > 0 := by
      simpa [OrderedPositiveTimeRegion, htime] using hi
    linarith
  · intro j hij
    have hij' := (hord i).2 j hij
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t < x j 0 - t := by
      simpa [OrderedPositiveTimeRegion, htime] using hij'
    linarith

/-- A single OS pairing term with ordered positive-time support has polynomial
growth in the Euclidean time shift, as required by the E0' growth hypothesis. -/
private theorem exists_norm_os_pairing_term_timeShift_le_polynomial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_pos : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hg_pos : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))‖ ≤
        C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^
          lgc.sobolev_index := by
  obtain ⟨Csemi, hCsemi_nonneg, hCsemi⟩ :=
    exists_seminorm_osConjTensorProduct_timeShift_le_polynomial
      (d := d) lgc.sobolev_index f g
  let P : ℝ :=
    lgc.alpha * lgc.beta ^ (n + m) * ((n + m).factorial : ℝ) ^ lgc.gamma
  let C : ℝ := P * Csemi
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    have halpha_nonneg : 0 ≤ lgc.alpha := le_of_lt lgc.alpha_pos
    have hbeta_nonneg : 0 ≤ lgc.beta ^ (n + m) := by
      exact pow_nonneg (le_of_lt lgc.beta_pos) _
    have hfac_nonneg : 0 ≤ ((n + m).factorial : ℝ) := by positivity
    have hrpow_nonneg : 0 ≤ ((n + m).factorial : ℝ) ^ lgc.gamma := by
      simpa using Real.rpow_nonneg hfac_nonneg lgc.gamma
    exact mul_nonneg (mul_nonneg halpha_nonneg hbeta_nonneg) hrpow_nonneg
  refine ⟨C, by
    exact mul_nonneg hP_nonneg hCsemi_nonneg, ?_⟩
  intro t ht
  have hzero :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := n) (m := m) (f := f)
      (g := timeShiftSchwartzNPoint (d := d) t g) hf_pos
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg_aux
        (d := d) t ht g hg_pos)
  have hgrowth :
      ‖OS.S (n + m)
          ⟨f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g), hzero⟩‖ ≤
        P * SchwartzMap.seminorm ℝ lgc.sobolev_index lgc.sobolev_index
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
    lgc.growth_estimate (n + m)
      ⟨f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g), hzero⟩
  calc
    ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))‖
      = ‖OS.S (n + m)
          ⟨f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g), hzero⟩‖ := by
            rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
              (f := f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) hzero]
    _ ≤ P * SchwartzMap.seminorm ℝ lgc.sobolev_index lgc.sobolev_index
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := hgrowth
    _ ≤ P * (Csemi * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^
          lgc.sobolev_index) := by
            exact mul_le_mul_of_nonneg_left (hCsemi t) hP_nonneg
    _ = C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^
          lgc.sobolev_index := by
            dsimp [C]
            ring

abbrev timeShiftBorchers (t : ℝ) : BorchersSequence d → BorchersSequence d :=
  fun F =>
    { funcs := fun n => timeShiftSchwartzNPoint (d := d) t (F.funcs n)
      bound := F.bound
      bound_spec := by
        intro n hn
        simp [F.bound_spec n hn] }

omit [NeZero d] in
@[simp] theorem timeShiftBorchers_funcs (t : ℝ) (F : BorchersSequence d) (n : ℕ) :
    (timeShiftBorchers (d := d) t F).funcs n = timeShiftSchwartzNPoint (d := d) t (F.funcs n) :=
  rfl

abbrev translateBorchers (a : SpacetimeDim d) : BorchersSequence d → BorchersSequence d :=
  fun F =>
    { funcs := fun n => translateSchwartzNPoint (d := d) a (F.funcs n)
      bound := F.bound
      bound_spec := by
        intro n hn
        simp [F.bound_spec n hn] }

omit [NeZero d] in
@[simp] theorem translateBorchers_funcs (a : SpacetimeDim d) (F : BorchersSequence d) (n : ℕ) :
    (translateBorchers (d := d) a F).funcs n = translateSchwartzNPoint (d := d) a (F.funcs n) :=
  rfl

omit [NeZero d] in
theorem timeShiftBorchers_translateBorchers
    (t : ℝ) (a : SpacetimeDim d) (F : BorchersSequence d) :
    timeShiftBorchers (d := d) t (translateBorchers (d := d) a F) =
      translateBorchers (d := d) a (timeShiftBorchers (d := d) t F) := by
  cases F
  simp [timeShiftBorchers, translateBorchers,
    translateSchwartzNPoint_timeShiftSchwartzNPoint]

private theorem translate_osConjTensorProduct_eq_of_spatial {n m : ℕ}
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
      (translateSchwartzNPoint (d := d) a g)) x =
      (f.osConjTensorProduct g) (fun i => x i - a) := by
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, translateSchwartzNPoint_apply]
  congr
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, splitFirst, timeReflection, ha0]
    · simp [timeReflectionN, splitFirst, timeReflection, hμ]

private theorem schwinger_translate_tensor_eq_of_spatial (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hleft : VanishesToInfiniteOrderOnCoincidence
      ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a g)))
    (hright : VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct g)) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a g))) =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  symm
  refine OS.E1_translation_invariant (n + m) (-a)
    (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g))
    (ZeroDiagonalSchwartz.ofClassical
      ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a g))) ?_
  intro x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := f.osConjTensorProduct g) hright,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a g))) hleft]
  simpa [sub_eq_add_neg] using
    (translate_osConjTensorProduct_eq_of_spatial (d := d) a ha0 f g x)

private theorem OSInnerProduct_translate_eq_of_spatial (OS : OsterwalderSchraderAxioms d)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (F G : BorchersSequence d)
    (hleft : OSTensorAdmissible d (translateBorchers (d := d) a F)
      (translateBorchers (d := d) a G))
    (hright : OSTensorAdmissible d F G) :
    OSInnerProduct d OS.S (translateBorchers (d := d) a F)
      (translateBorchers (d := d) a G) =
    OSInnerProduct d OS.S F G := by
  unfold OSInnerProduct
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  simpa [translateBorchers_funcs] using
    schwinger_translate_tensor_eq_of_spatial (d := d) OS a ha0
      (F.funcs n) (G.funcs m) (hleft n m) (hright n m)

private theorem OSInnerProduct_translate_right_timeShift_eq_of_spatial
    (OS : OsterwalderSchraderAxioms d)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (F G : BorchersSequence d) (t : ℝ)
    (hleft : OSTensorAdmissible d (translateBorchers (d := d) a F)
      (timeShiftBorchers (d := d) t (translateBorchers (d := d) a G)))
    (hright : OSTensorAdmissible d F
      (timeShiftBorchers (d := d) t G)) :
    OSInnerProduct d OS.S (translateBorchers (d := d) a F)
      (timeShiftBorchers (d := d) t (translateBorchers (d := d) a G)) =
    OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G) := by
  rw [timeShiftBorchers_translateBorchers]
  have hleft' :
      OSTensorAdmissible d (translateBorchers (d := d) a F)
        (translateBorchers (d := d) a (timeShiftBorchers (d := d) t G)) := by
    simpa [timeShiftBorchers_translateBorchers] using hleft
  exact OSInnerProduct_translate_eq_of_spatial
    (d := d) OS a ha0 F (timeShiftBorchers (d := d) t G) hleft' hright

private theorem exists_norm_OSInnerProduct_right_timeShift_le_polynomial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d) t (G : BorchersSequence d))‖ ≤
        C * t ^ lgc.sobolev_index := by
  let Cterm : ℕ → ℕ → ℝ := fun n m =>
    Classical.choose
      (exists_norm_os_pairing_term_timeShift_le_polynomial
        (d := d) OS lgc
        ((F : BorchersSequence d).funcs n)
        ((G : BorchersSequence d).funcs m)
        (F.ordered_tsupport n) (G.ordered_tsupport m))
  have hCterm :
      ∀ n m, 0 ≤ Cterm n m ∧
        ∀ t : ℝ, 0 ≤ t →
          ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
              (((F : BorchersSequence d).funcs n).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))‖ ≤
            Cterm n m *
              (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^
                lgc.sobolev_index := by
    intro n m
    simpa [Cterm] using
      (Classical.choose_spec
        (exists_norm_os_pairing_term_timeShift_le_polynomial
          (d := d) OS lgc
          ((F : BorchersSequence d).funcs n)
          ((G : BorchersSequence d).funcs m)
          (F.ordered_tsupport n) (G.ordered_tsupport m)))
  let D : ℕ → ℝ := fun m =>
    (1 + ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖) ^ lgc.sobolev_index
  let I : Finset ℕ := Finset.range ((F : BorchersSequence d).bound + 1)
  let J : Finset ℕ := Finset.range ((G : BorchersSequence d).bound + 1)
  let C : ℝ := ∑ n ∈ I, ∑ m ∈ J, Cterm n m * D m
  refine ⟨C, by
    dsimp [C, I, J, D]
    refine Finset.sum_nonneg ?_
    intro n hn
    refine Finset.sum_nonneg ?_
    intro m hm
    exact mul_nonneg (hCterm n m).1 (by positivity), ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  calc
    ‖OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) t (G : BorchersSequence d))‖
      = ‖∑ n ∈ I, ∑ m ∈ J,
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (((F : BorchersSequence d).funcs n).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))‖ := by
          simp [OSInnerProduct, I, J]
    _ ≤ ∑ n ∈ I, ‖∑ m ∈ J,
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (((F : BorchersSequence d).funcs n).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))‖ := by
          simpa using
            (norm_sum_le (s := I) (f := fun n =>
              ∑ m ∈ J,
                OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
                  (((F : BorchersSequence d).funcs n).osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))))
    _ ≤ ∑ n ∈ I, ∑ m ∈ J,
          ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (((F : BorchersSequence d).funcs n).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))‖ := by
          refine Finset.sum_le_sum ?_
          intro n hn
          simpa using
            (norm_sum_le (s := J) (f := fun m =>
              OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
                (((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))))
    _ ≤ ∑ n ∈ I, ∑ m ∈ J,
          Cterm n m *
            (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^
              lgc.sobolev_index := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum ?_
          intro m hm
          exact (hCterm n m).2 t ht0
    _ ≤ ∑ n ∈ I, ∑ m ∈ J, Cterm n m * (D m * t ^ lgc.sobolev_index) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum ?_
          intro m hm
          have hCnonneg : 0 ≤ Cterm n m := (hCterm n m).1
          have hpoly :=
            one_add_norm_timeShiftConfig_pow_le (d := d) (m := m)
              (s := lgc.sobolev_index) t ht
          simpa [D] using mul_le_mul_of_nonneg_left hpoly hCnonneg
    _ = ∑ n ∈ I, ∑ m ∈ J, (Cterm n m * D m) * t ^ lgc.sobolev_index := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
    _ = C * t ^ lgc.sobolev_index := by
          calc
            ∑ n ∈ I, ∑ m ∈ J, (Cterm n m * D m) * t ^ lgc.sobolev_index
              = ∑ n ∈ I, (∑ m ∈ J, Cterm n m * D m) * t ^ lgc.sobolev_index := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  rw [← Finset.sum_mul]
            _ = (∑ n ∈ I, ∑ m ∈ J, Cterm n m * D m) * t ^ lgc.sobolev_index := by
                  rw [← Finset.sum_mul]
            _ = C * t ^ lgc.sobolev_index := by
                  rfl

omit [NeZero d] in
abbrev flattenSchwartzNPoint {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1)).symm

omit [NeZero d] in
abbrev unflattenSchwartzNPoint {n : ℕ} :
    SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1))

omit [NeZero d] in
@[simp] theorem flattenSchwartzNPoint_apply {n : ℕ}
    (f : SchwartzNPoint d n) (u : Fin (n * (d + 1)) → ℝ) :
    flattenSchwartzNPoint (d := d) f u = f ((flattenCLEquivReal n (d + 1)).symm u) := rfl

omit [NeZero d] in
@[simp] theorem unflattenSchwartzNPoint_apply {n : ℕ}
    (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (x : NPointDomain d n) :
    unflattenSchwartzNPoint (d := d) f x = f (flattenCLEquivReal n (d + 1) x) := rfl

omit [NeZero d] in
abbrev flatTimeShiftDirection (d n : ℕ) : Fin (n * (d + 1)) → ℝ :=
  fun k => if (finProdFinEquiv.symm k).2 = 0 then (-1 : ℝ) else 0

omit [NeZero d] in
private theorem unflatten_add_flatTimeShiftDirection {n : ℕ}
    (u : Fin (n * (d + 1)) → ℝ) (t : ℝ) :
    (flattenCLEquivReal n (d + 1)).symm (u + t • flatTimeShiftDirection d n) =
      fun i => ((flattenCLEquivReal n (d + 1)).symm u i) - timeShiftVec d t := by
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [sub_eq_add_neg]
  · simp [flatTimeShiftDirection, timeShiftVec, hμ]

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_eq_unflatten_translate {n : ℕ}
    (t : ℝ) (f : SchwartzNPoint d n) :
    timeShiftSchwartzNPoint (d := d) t f =
      unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz (t • flatTimeShiftDirection d n)
          (flattenSchwartzNPoint (d := d) f)) := by
  ext x
  simp [SCV.translateSchwartz_apply, unflatten_add_flatTimeShiftDirection]

omit [NeZero d] in
private theorem hasCompactSupport_flattenSchwartzNPoint {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    HasCompactSupport
      ((flattenSchwartzNPoint (d := d) f :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) : (Fin (n * (d + 1)) → ℝ) → ℂ) := by
  simpa [flattenSchwartzNPoint] using
    hf.comp_homeomorph ((flattenCLEquivReal n (d + 1)).symm.toHomeomorph)

omit [NeZero d] in
private theorem tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t₀ : ℝ) :
    Filter.Tendsto (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t f) (nhds t₀)
      (nhds (timeShiftSchwartzNPoint (d := d) t₀ f)) := by
  let ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f
  have hψ : HasCompactSupport ((ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) :
      (Fin (n * (d + 1)) → ℝ) → ℂ) :=
    hasCompactSupport_flattenSchwartzNPoint (d := d) f hf
  have hη : Continuous (fun t : ℝ => t • flatTimeShiftDirection d n) :=
    continuous_id.smul continuous_const
  have hflat_full :
      Filter.Tendsto
        (fun s : Fin (n * (d + 1)) → ℝ => SCV.translateSchwartz s ψ)
        (nhds (t₀ • flatTimeShiftDirection d n))
        (nhds (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ)) :=
    SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ (t₀ • flatTimeShiftDirection d n)
  have hflat :
      Filter.Tendsto
        (fun t : ℝ => SCV.translateSchwartz (t • flatTimeShiftDirection d n) ψ)
        (nhds t₀)
        (nhds (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ)) :=
    hflat_full.comp (hη.tendsto t₀)
  have hunflat :
      Filter.Tendsto
        (fun t : ℝ =>
          unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t • flatTimeShiftDirection d n) ψ))
        (nhds t₀)
        (nhds
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ))) :=
    (((unflattenSchwartzNPoint (d := d) :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n).continuous).tendsto
      _).comp hflat
  simpa [ψ, timeShiftSchwartzNPoint_eq_unflatten_translate] using hunflat

omit [NeZero d] in
private theorem continuous_timeShiftSchwartzNPoint_of_isCompactSupport {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    Continuous (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t f) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  exact tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport (d := d) f hf t₀

omit [NeZero d] in
private theorem hasCompactSupport_timeShiftSchwartzNPoint {n : ℕ}
    (t : ℝ) (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (((timeShiftSchwartzNPoint (d := d) t f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) := by
  simpa [timeShiftSchwartzNPoint_apply] using
    hf.comp_homeomorph (translateNPointDomainHomeomorph (d := d) (n := n) (timeShiftVec d t))

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
    {n : ℕ} (t : ℝ) (ht : 0 ≤ t) (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((timeShiftSchwartzNPoint (d := d) t f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  intro x hx
  have hxpre :
      (fun i => x i - timeShiftVec d t) ∈
        tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_precomp_subset
      (f := ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (h := translateNPointDomain (d := d) (n := n) (timeShiftVec d t))
      (continuous_translateNPointDomain (d := d) (n := n) (timeShiftVec d t)) hx
  have hord := hf hxpre
  intro i
  constructor
  · have hi := (hord i).1
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t > 0 := by
      simpa [OrderedPositiveTimeRegion, htime] using hi
    linarith
  · intro j hij
    have hij' := (hord i).2 j hij
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t < x j 0 - t := by
      simpa [OrderedPositiveTimeRegion, htime] using hij'
    linarith

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_tsupport_subset_ordered_after_nonneg
    {n : ℕ} (t : ℝ) (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((timeShiftSchwartzNPoint (d := d) t f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆
      {x | ∀ i : Fin n, t < x i 0 ∧ ∀ j : Fin n, i < j → x i 0 < x j 0} := by
  intro x hx
  have hxpre :
      (fun i => x i - timeShiftVec d t) ∈
        tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_precomp_subset
      (f := ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (h := translateNPointDomain (d := d) (n := n) (timeShiftVec d t))
      (continuous_translateNPointDomain (d := d) (n := n) (timeShiftVec d t)) hx
  have hord := hf hxpre
  intro i
  constructor
  · have hi := (hord i).1
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : 0 < x i 0 - t := by
      simpa [OrderedPositiveTimeRegion, htime] using hi
    linarith
  · intro j hij
    have hij' := (hord i).2 j hij
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t < x j 0 - t := by
      simpa [OrderedPositiveTimeRegion, htime] using hij'
    linarith

omit [NeZero d] in
theorem timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
    {n : ℕ} (t : ℝ) (ht : 0 < t) (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((timeShiftSchwartzNPoint (d := d) t f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
    (d := d) t (le_of_lt ht) f hf

omit [NeZero d] in
theorem translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    {n : ℕ} (a : SpacetimeDim d) (ha0 : a 0 = 0) (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((translateSchwartzNPoint (d := d) a f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  intro x hx
  have hxpre :
      (fun i => x i - a) ∈
        tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_precomp_subset
      (f := ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (h := translateNPointDomain (d := d) (n := n) a)
      (continuous_translateNPointDomain (d := d) (n := n) a) hx
  have hord := hf hxpre
  intro i
  constructor
  · have hi := (hord i).1
    have : 0 < x i 0 - a 0 := by
      simpa [OrderedPositiveTimeRegion] using hi
    simpa [ha0] using this
  · intro j hij
    have hij' := (hord i).2 j hij
    have : x i 0 - a 0 < x j 0 - a 0 := by
      simpa [OrderedPositiveTimeRegion] using hij'
    simpa [ha0] using this

/-- If a head test is supported in the time slab `0 < τ_head < t`, then prepending it
to a tail shifted forward by `t` preserves the ordered positive-time support surface. -/
private theorem prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
    {n : ℕ} (t : ℝ) (f : SchwartzSpacetime d) (g : SchwartzNPoint d n)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t})
    (hg : tsupport ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((SchwartzMap.prependField f (timeShiftSchwartzNPoint (d := d) t g) :
      SchwartzNPoint d (n + 1)) : NPointDomain d (n + 1) → ℂ)) ⊆
      OrderedPositiveTimeRegion d (n + 1) := by
  exact SchwartzMap.prependField_tsupport_subset_orderedPositiveTimeRegion_of_barrier
    (d := d) (n := n) t f (timeShiftSchwartzNPoint (d := d) t g) hf
    (timeShiftSchwartzNPoint_tsupport_subset_ordered_after_nonneg
      (d := d) (n := n) t g hg)

/-- The time-shifted prependField test from the previous theorem is automatically
zero-diagonal, because its topological support lies in the ordered positive-time region. -/
private theorem prependField_timeShift_vanishesToInfiniteOrderOnCoincidence_of_head_barrier
    {n : ℕ} (t : ℝ) (f : SchwartzSpacetime d) (g : SchwartzNPoint d n)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t})
    (hg : tsupport ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.prependField f (timeShiftSchwartzNPoint (d := d) t g)) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.mpr ?_
  intro x hx hxcoin
  exact (not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion
    (prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
      (d := d) (n := n) t f g hf hg hx)) hxcoin

/-- Barrier-separated head-field insertion after Euclidean time shift stays inside the
honest positive-time OS Borchers algebra. This is the first operator-level object on the
direct OS kernel route: the support geometry is now packaged as an actual map, rather than
remaining implicit in individual shell computations. -/
def fieldActionTimeShiftPositiveTimeBorchers
    (h : SchwartzSpacetime d) (t : ℝ)
    (hh_barrier : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t}) :
    PositiveTimeBorchersSequence d → PositiveTimeBorchersSequence d :=
  fun F =>
    { toBorchersSequence :=
        Reconstruction.fieldOperatorAction h
          (timeShiftBorchers (d := d) t (F : BorchersSequence d))
      ordered_tsupport := by
        intro n
        cases n with
        | zero =>
            simp [Reconstruction.fieldOperatorAction_funcs_zero]
        | succ n =>
            simpa [Reconstruction.fieldOperatorAction_funcs_succ, timeShiftBorchers_funcs] using
              prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
                (d := d) (n := n) t h ((F : BorchersSequence d).funcs n)
                hh_barrier (F.ordered_tsupport n) }

@[simp] theorem fieldActionTimeShiftPositiveTimeBorchers_toBorchersSequence
    (h : SchwartzSpacetime d) (t : ℝ)
    (hh_barrier : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t})
    (F : PositiveTimeBorchersSequence d) :
    ((fieldActionTimeShiftPositiveTimeBorchers (d := d) h t hh_barrier F :
      PositiveTimeBorchersSequence d) : BorchersSequence d) =
      Reconstruction.fieldOperatorAction h
        (timeShiftBorchers (d := d) t (F : BorchersSequence d)) := rfl

private theorem continuousOn_os_pairing_term_timeShift_nonneg_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_pos : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hg_pos : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ)) :
    ContinuousOn (fun t : ℝ =>
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      (Set.Ici 0) := by
  rw [continuousOn_iff_continuous_restrict]
  let hterm : Set.Ici (0 : ℝ) → ZeroDiagonalSchwartz d (n + m) := fun t =>
    ⟨f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t.1 g),
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := n) (m := m) (f := f)
        (g := timeShiftSchwartzNPoint (d := d) t.1 g) hf_pos
        (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
          (d := d) t.1 t.2 g hg_pos)⟩
  have hshift :
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        timeShiftSchwartzNPoint (d := d) t.1 g) :=
    (continuous_timeShiftSchwartzNPoint_of_isCompactSupport (d := d) g hg_compact).comp
      continuous_subtype_val
  have hbase :
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t.1 g)) := by
    simpa [SchwartzNPoint.osConjTensorProduct] using
      (SchwartzMap.tensorProduct_continuous_right f.osConj).comp hshift
  have hterm_cont : Continuous hterm := by
    exact hbase.subtype_mk (fun t =>
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := n) (m := m) (f := f)
        (g := timeShiftSchwartzNPoint (d := d) t.1 g) hf_pos
        (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
          (d := d) t.1 t.2 g hg_pos))
  let hscalar : Set.Ici (0 : ℝ) → ℂ := fun t => OS.S (n + m) (hterm t)
  have hscalar_cont : Continuous hscalar := (OS.E0_tempered (n + m)).comp hterm_cont
  convert hscalar_cont using 1
  ext t
  simp [Set.restrict, hscalar, hterm]
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t.1 g))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := n) (m := m) (f := f)
        (g := timeShiftSchwartzNPoint (d := d) t.1 g) hf_pos
        (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
          (d := d) t.1 t.2 g hg_pos))]

private theorem continuousOn_os_pairing_term_timeShift_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_pos : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hg_pos : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ)) :
    ContinuousOn (fun t : ℝ =>
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      (Set.Ioi 0) := by
  exact (continuousOn_os_pairing_term_timeShift_nonneg_of_isCompactSupport
    (d := d) OS f g hf_pos hg_pos hg_compact).mono Set.Ioi_subset_Ici_self

omit [NeZero d] in
private theorem timeShift_preserves_ordered_positive_tsupport_nonneg (t : ℝ) (ht : 0 ≤ t)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    ∀ n,
      tsupport ((((timeShiftBorchers (d := d) t F).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  intro n
  exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
    (d := d) t ht (F.funcs n) (hF n)

omit [NeZero d] in
private theorem timeShift_preserves_ordered_positive_tsupport (t : ℝ) (ht : 0 < t)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    ∀ n,
      tsupport ((((timeShiftBorchers (d := d) t F).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  exact timeShift_preserves_ordered_positive_tsupport_nonneg
    (d := d) t (le_of_lt ht) F hF

/-- Positive Euclidean time translation on the honest OS Borchers algebra. -/
private def timeShiftPositiveTimeBorchers (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d where
  toBorchersSequence := timeShiftBorchers (d := d) t (F : BorchersSequence d)
  ordered_tsupport := by
    simpa using timeShift_preserves_ordered_positive_tsupport (d := d) t ht
      (F : BorchersSequence d) F.ordered_tsupport

omit [NeZero d] in
@[simp] private theorem timeShiftPositiveTimeBorchers_funcs (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    ((timeShiftPositiveTimeBorchers (d := d) t ht F : PositiveTimeBorchersSequence d) :
      BorchersSequence d).funcs n =
        timeShiftSchwartzNPoint (d := d) t ((F : BorchersSequence d).funcs n) :=
  rfl

omit [NeZero d] in
@[simp] private theorem timeShiftPositiveTimeBorchers_toBorchersSequence (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) :
    ((timeShiftPositiveTimeBorchers (d := d) t ht F : PositiveTimeBorchersSequence d) :
      BorchersSequence d) =
        timeShiftBorchers (d := d) t (F : BorchersSequence d) := rfl

omit [NeZero d] in
private theorem timeShiftPositiveTimeBorchers_hasCompactSupport (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    ∀ n,
      HasCompactSupport
        (((((timeShiftPositiveTimeBorchers (d := d) t ht F :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
  intro n
  simpa using
    hasCompactSupport_timeShiftSchwartzNPoint (d := d) t
      ((F : BorchersSequence d).funcs n) (hF_compact n)

omit [NeZero d] in
private theorem timeShiftPositiveTimeBorchers_comp_funcs (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) :
    ∀ n,
      ((timeShiftPositiveTimeBorchers (d := d) s hs
          (timeShiftPositiveTimeBorchers (d := d) t ht F) : PositiveTimeBorchersSequence d) :
        BorchersSequence d).funcs n =
          ((timeShiftPositiveTimeBorchers (d := d) (s + t) (add_pos hs ht) F :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n := by
  intro n
  ext x
  simp
  congr
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeShiftVec]
    ring
  · simp [timeShiftVec, hμ]

private theorem continuousOn_OSInnerProduct_right_timeShift_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (F G : BorchersSequence d)
    (hF_pos : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG_pos : ∀ n, tsupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG_compact : ∀ n,
      HasCompactSupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    ContinuousOn (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
      (Set.Ioi 0) := by
  have hEq :
      Set.EqOn
        (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
        (fun t : ℝ => OSInnerProductN d OS.S F (timeShiftBorchers (d := d) t G)
          (F.bound + 1) (G.bound + 1))
        (Set.Ioi 0) := by
    intro t _
    refine OSInnerProduct_eq_extended d OS.S OS.E0_linear F
      (timeShiftBorchers (d := d) t G) (F.bound + 1) (G.bound + 1) le_rfl ?_
    exact le_rfl
  have hN :
      ContinuousOn
        (fun t : ℝ => OSInnerProductN d OS.S F (timeShiftBorchers (d := d) t G)
          (F.bound + 1) (G.bound + 1))
        (Set.Ioi 0) := by
    unfold OSInnerProductN
    refine continuousOn_finset_sum (Finset.range (F.bound + 1)) ?_
    intro n hn
    refine continuousOn_finset_sum (Finset.range (G.bound + 1)) ?_
    intro m hm
    simpa [timeShiftBorchers_funcs] using
      continuousOn_os_pairing_term_timeShift_of_isCompactSupport
        (d := d) OS (f := F.funcs n) (g := G.funcs m)
        (hf_pos := hF_pos n) (hg_pos := hG_pos m) (hg_compact := hG_compact m)
  exact hN.congr hEq.symm

private theorem continuousOn_OSInnerProduct_right_timeShift_nonneg_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (F G : BorchersSequence d)
    (hF_pos : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG_pos : ∀ n, tsupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG_compact : ∀ n,
      HasCompactSupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    ContinuousOn (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
      (Set.Ici 0) := by
  have hEq :
      Set.EqOn
        (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
        (fun t : ℝ => OSInnerProductN d OS.S F (timeShiftBorchers (d := d) t G)
          (F.bound + 1) (G.bound + 1))
        (Set.Ici 0) := by
    intro t _
    refine OSInnerProduct_eq_extended d OS.S OS.E0_linear F
      (timeShiftBorchers (d := d) t G) (F.bound + 1) (G.bound + 1) le_rfl ?_
    exact le_rfl
  have hN :
      ContinuousOn
        (fun t : ℝ => OSInnerProductN d OS.S F (timeShiftBorchers (d := d) t G)
          (F.bound + 1) (G.bound + 1))
        (Set.Ici 0) := by
    unfold OSInnerProductN
    refine continuousOn_finset_sum (Finset.range (F.bound + 1)) ?_
    intro n hn
    refine continuousOn_finset_sum (Finset.range (G.bound + 1)) ?_
    intro m hm
    simpa [timeShiftBorchers_funcs] using
      continuousOn_os_pairing_term_timeShift_nonneg_of_isCompactSupport
        (d := d) OS (f := F.funcs n) (g := G.funcs m)
        (hf_pos := hF_pos n) (hg_pos := hG_pos m) (hg_compact := hG_compact m)
  exact hN.congr hEq.symm

private theorem tendsto_OSInnerProduct_right_timeShift_nhdsWithin_zero_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (F G : BorchersSequence d)
    (hF_pos : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG_pos : ∀ n, tsupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG_compact : ∀ n,
      HasCompactSupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    Filter.Tendsto (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (OSInnerProduct d OS.S F G)) := by
  have hcont :
      ContinuousWithinAt
        (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
        (Set.Ici 0) 0 :=
    (continuousOn_OSInnerProduct_right_timeShift_nonneg_of_isCompactSupport
      (d := d) OS F G hF_pos hG_pos hG_compact) 0 (by simp)
  have h0 :
      OSInnerProduct d OS.S F (timeShiftBorchers (d := d) 0 G) =
        OSInnerProduct d OS.S F G := by
    refine OSInnerProduct_congr_right d OS.S OS.E0_linear F
      (timeShiftBorchers (d := d) 0 G) G ?_
    intro n
    ext x
    simp
    congr
    ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  rw [ContinuousWithinAt, h0] at hcont
  exact hcont.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

private theorem OSInnerProduct_right_timeShift_zero
    (OS : OsterwalderSchraderAxioms d) (F G : BorchersSequence d) :
    OSInnerProduct d OS.S F (timeShiftBorchers (d := d) 0 G) =
      OSInnerProduct d OS.S F G := by
  refine OSInnerProduct_congr_right d OS.S OS.E0_linear F
    (timeShiftBorchers (d := d) 0 G) G ?_
  intro n
  ext x
  simp
  congr
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeShiftVec]
  · simp [timeShiftVec, hμ]

omit [NeZero d] in
private theorem timeReflection_add_timeShiftVec (x : SpacetimeDim d) (t : ℝ) :
    timeReflection d (x + timeShiftVec d t) = timeReflection d x - timeShiftVec d t := by
  funext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeReflection, timeShiftVec]
    ring
  · simp [timeReflection, timeShiftVec, hμ]

/-- Pointwise form of a right-block Euclidean time shift inside the OS tensor
product. Shifting the right Schwartz factor by `t` is the same as evaluating the
unshifted tensor product on the combined configuration whose last block is
translated by `- timeShiftVec d t`, while the first block stays fixed. -/
theorem osConjTensorProduct_timeShift_eq_tailShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      (f.osConjTensorProduct g)
        (fun i => if h : n ≤ i.val then x i - timeShiftVec d t else x i) := by
  let y : NPointDomain d (n + m) :=
    fun i => if h : n ≤ i.val then x i - timeShiftVec d t else x i
  have hsplitFirst : splitFirst n m y = splitFirst n m x := by
    ext i μ
    have hi : ¬ n ≤ (Fin.castAdd m i).val := by
      simpa using (not_le_of_gt i.isLt)
    change (if n ≤ (Fin.castAdd m i).val then x (Fin.castAdd m i) - timeShiftVec d t
      else x (Fin.castAdd m i)) μ = x (Fin.castAdd m i) μ
    rw [if_neg hi]
  have hsplitLast :
      splitLast n m y = fun i => x (Fin.natAdd n i) - timeShiftVec d t := by
    ext i μ
    have hi : n ≤ (Fin.natAdd n i).val := by
      simp [Fin.natAdd]
    change (if n ≤ (Fin.natAdd n i).val then x (Fin.natAdd n i) - timeShiftVec d t
      else x (Fin.natAdd n i)) μ = (x (Fin.natAdd n i) - timeShiftVec d t) μ
    rw [if_pos hi]
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, timeShiftSchwartzNPoint_apply]
  rw [hsplitFirst, hsplitLast]
  rfl

private theorem shift_osConjTensorProduct_eq {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (s t : ℝ)
    (x : NPointDomain d (n + m)) :
    ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) s g)) x =
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))
      (fun i => x i + timeShiftVec d t) := by
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, timeShiftSchwartzNPoint_apply]
  congr
  · ext i μ
    symm
    simpa [timeReflectionN, splitFirst, sub_eq_add_neg] using
      congrArg (fun y : SpacetimeDim d => y μ)
        (timeReflection_add_timeShiftVec (d := d) (x := splitFirst n m x i) t)
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitLast, timeShiftVec, sub_eq_add_neg]
      ring
    · simp [splitLast, timeShiftVec, hμ, sub_eq_add_neg]

private theorem schwinger_shift_tensor_eq (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (s t : ℝ)
    (hleft : VanishesToInfiniteOrderOnCoincidence
      ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g)))
    (hright : VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g))) =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))) := by
  symm
  refine OS.E1_translation_invariant (n + m) (timeShiftVec d t)
    (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g)))
    (ZeroDiagonalSchwartz.ofClassical
      ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g))) ?_
  intro x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))) hright,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g))) hleft]
  exact shift_osConjTensorProduct_eq (d := d) f g s t x

private theorem OSInnerProduct_timeShift_eq (OS : OsterwalderSchraderAxioms d)
    (F G : BorchersSequence d) (s t : ℝ)
    (hleft : OSTensorAdmissible d (timeShiftBorchers (d := d) t F)
      (timeShiftBorchers (d := d) s G))
    (hright : OSTensorAdmissible d F
      (timeShiftBorchers (d := d) (t + s) G)) :
    OSInnerProduct d OS.S (timeShiftBorchers (d := d) t F) (timeShiftBorchers (d := d) s G) =
    OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t + s) G) := by
  unfold OSInnerProduct
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  simpa [timeShiftBorchers_funcs] using
    schwinger_shift_tensor_eq (d := d) OS (F.funcs n) (G.funcs m) s t
      (hleft n m) (hright n m)

private theorem OSTensorAdmissible_linearCombo_right {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ)
    (F : BorchersSequence d) (G : ι → BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d F (G i)) :
    OSTensorAdmissible d F (BorchersSequence.linearCombo s c G) := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    simpa [BorchersSequence.linearCombo] using (OSTensorAdmissible.zero_right (d := d) F)
  · intro a s ha ih hFG n m
    rw [BorchersSequence.linearCombo_insert (d := d) ha c G m,
      BorchersSequence.add_funcs, BorchersSequence.smul_funcs,
      SchwartzNPoint.osConjTensorProduct_add_right,
      SchwartzNPoint.osConjTensorProduct_smul_right]
    exact ((hFG a (Finset.mem_insert_self a s) n m).smul (c a)).add
      (ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi)) n m)

/-- The OS inner product distributes over `linearCombo` in the right argument. -/
private theorem OSInnerProduct_linearCombo_right (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (F : BorchersSequence d) (G : ι → BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d F (G i)) :
    OSInnerProduct d OS.S F (BorchersSequence.linearCombo s c G) =
      ∑ i ∈ s, c i • OSInnerProduct d OS.S F (G i) := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    rw [OSInnerProduct_congr_right (d := d) OS.S OS.E0_linear F
      (BorchersSequence.linearCombo ∅ c G) 0 (fun n => BorchersSequence.linearCombo_empty (d := d) c G n)]
    exact OSInnerProduct_zero_right (d := d) OS.S OS.E0_linear F
  · intro a s ha ih hFG
    rw [OSInnerProduct_congr_right (d := d) OS.S OS.E0_linear F
      (BorchersSequence.linearCombo (insert a s) c G)
      (c a • G a + BorchersSequence.linearCombo s c G)
      (fun n => BorchersSequence.linearCombo_insert (d := d) ha c G n)]
    rw [OSInnerProduct_add_right (d := d) OS.S OS.E0_linear F
      (c a • G a) (BorchersSequence.linearCombo s c G)]
    · rw [OSInnerProduct_smul_right (d := d) OS.S OS.E0_linear (c a) F (G a)]
      rw [ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi))]
      simp [Finset.sum_insert, ha, smul_eq_mul]
    · exact OSTensorAdmissible.smul_right (d := d)
        (hFG a (Finset.mem_insert_self a s)) (c a)
    · exact OSTensorAdmissible_linearCombo_right (d := d) s c F G
        (fun i hi => hFG i (Finset.mem_insert_of_mem hi))

private theorem OSTensorAdmissible_linearCombo_left {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ)
    (F : ι → BorchersSequence d) (G : BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d (F i) G) :
    OSTensorAdmissible d (BorchersSequence.linearCombo s c F) G := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    simpa [BorchersSequence.linearCombo] using (OSTensorAdmissible.zero_left (d := d) G)
  · intro a s ha ih hFG n m
    rw [BorchersSequence.linearCombo_insert (d := d) ha c F n,
      BorchersSequence.add_funcs, BorchersSequence.smul_funcs,
      SchwartzNPoint.osConjTensorProduct_add_left,
      SchwartzNPoint.osConjTensorProduct_smul_left]
    exact ((hFG a (Finset.mem_insert_self a s) n m).smul (starRingEnd ℂ (c a))).add
      (ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi)) n m)

/-- The OS inner product distributes over `linearCombo` in the left argument. -/
private theorem OSInnerProduct_linearCombo_left (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (F : ι → BorchersSequence d) (G : BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d (F i) G) :
    OSInnerProduct d OS.S (BorchersSequence.linearCombo s c F) G =
      ∑ i ∈ s, starRingEnd ℂ (c i) • OSInnerProduct d OS.S (F i) G := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    rw [OSInnerProduct_congr_left (d := d) OS.S OS.E0_linear
      (BorchersSequence.linearCombo ∅ c F) 0 G (fun n => BorchersSequence.linearCombo_empty (d := d) c F n)]
    exact OSInnerProduct_zero_left (d := d) OS.S OS.E0_linear G
  · intro a s ha ih hFG
    rw [OSInnerProduct_congr_left (d := d) OS.S OS.E0_linear
      (BorchersSequence.linearCombo (insert a s) c F)
      (c a • F a + BorchersSequence.linearCombo s c F) G
      (fun n => BorchersSequence.linearCombo_insert (d := d) ha c F n)]
    rw [OSInnerProduct_add_left (d := d) OS.S OS.E0_linear
      (c a • F a) (BorchersSequence.linearCombo s c F) G]
    · rw [OSInnerProduct_smul_left (d := d) OS.S OS.E0_linear (c a) (F a) G]
      rw [ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi))]
      simp [Finset.sum_insert, ha, smul_eq_mul]
    · exact OSTensorAdmissible.smul_left (d := d)
        (hFG a (Finset.mem_insert_self a s)) (c a)
    · exact OSTensorAdmissible_linearCombo_left (d := d) s c F G
        (fun i hi => hFG i (Finset.mem_insert_of_mem hi))

omit [NeZero d] in
private theorem timeShift_linearCombo_preserves_ordered_positive_tsupport {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    ∀ n,
      tsupport (((BorchersSequence.linearCombo s c
          (fun i => timeShiftBorchers (d := d) (t i) F)).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n := by
  classical
  revert ht
  refine Finset.induction_on s ?_ ?_
  · intro ht n
    simp [BorchersSequence.linearCombo]
  · intro a s ha ih ht n
    rw [BorchersSequence.linearCombo_insert (d := d) ha c
      (fun i => timeShiftBorchers (d := d) (t i) F) n]
    intro x hx
    have hx' :
        x ∈ tsupport ((((c a • timeShiftBorchers (d := d) (t a) F).funcs n :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ∪
          tsupport ((((BorchersSequence.linearCombo s c
            (fun i => timeShiftBorchers (d := d) (t i) F)).funcs n :
              SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
      have hx'' := (tsupport_add
        ((((c a • timeShiftBorchers (d := d) (t a) F).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((BorchersSequence.linearCombo s c
          (fun i => timeShiftBorchers (d := d) (t i) F)).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ))) hx
      simpa [BorchersSequence.add_funcs] using hx''
    rcases hx' with hxleft | hxright
    · have hxshift :
          x ∈ tsupport ((((timeShiftBorchers (d := d) (t a) F).funcs n :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
        exact (tsupport_smul_subset_right
          (fun _ : NPointDomain d n => c a)
          ((((timeShiftBorchers (d := d) (t a) F).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)))
          (by simpa [BorchersSequence.smul_funcs] using hxleft)
      exact timeShift_preserves_ordered_positive_tsupport (d := d) (t a)
        (ht a (Finset.mem_insert_self a s)) F hF n hxshift
    · exact ih (fun i hi => ht i (Finset.mem_insert_of_mem hi)) n hxright

/-- Positivity of the Euclidean time-shift kernel on the OS side.

    For any Borchers sequence `F` supported in positive Euclidean times, the
    Hankel kernel `K(s,t) = ⟪F, T_{s+t} F⟫_OS` is positive semidefinite on every
    finite collection of positive times. This is the core positivity input for
    the Laplace/spectral base-step route. -/
theorem OSInnerProduct_timeShift_kernel_nonneg (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s,
      starRingEnd ℂ (c i) * c j *
        OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t i + t j) F)).re := by
  let G : ι → BorchersSequence d := fun i => timeShiftBorchers (d := d) (t i) F
  let H : BorchersSequence d := BorchersSequence.linearCombo s c G
  have hGsupport : ∀ i ∈ s, ∀ n,
      tsupport (((G i).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    intro i hi
    simpa [G] using
      timeShift_preserves_ordered_positive_tsupport (d := d) (t i) (ht i hi) F hF
  have hHsupport : ∀ n,
      tsupport ((H.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    simpa [H, G] using
      timeShift_linearCombo_preserves_ordered_positive_tsupport
        (d := d) s c t ht F hF
  have hOuterAdm : ∀ i ∈ s, OSTensorAdmissible d (G i) H := by
    intro i hi
    exact OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (G i) H (hGsupport i hi) hHsupport
  have hPairAdm : ∀ i ∈ s, ∀ j ∈ s, OSTensorAdmissible d (G i) (G j) := by
    intro i hi j hj
    exact OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (G i) (G j) (hGsupport i hi) (hGsupport j hj)
  have hShiftAdm : ∀ i ∈ s, ∀ j ∈ s,
      OSTensorAdmissible d F (timeShiftBorchers (d := d) (t i + t j) F) := by
    intro i hi j hj
    exact OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) F (timeShiftBorchers (d := d) (t i + t j) F) hF
      (timeShift_preserves_ordered_positive_tsupport (d := d) (t i + t j)
        (by linarith [ht i hi, ht j hj]) F hF)
  have hpos : 0 ≤ (OSInnerProduct d OS.S H H).re :=
    OS.E2_reflection_positive H hHsupport
  have hExpandLeft :
      OSInnerProduct d OS.S H H =
        ∑ i ∈ s, starRingEnd ℂ (c i) * OSInnerProduct d OS.S (G i) H := by
    simpa [H, G, smul_eq_mul] using
      (OSInnerProduct_linearCombo_left (d := d) (OS := OS) (s := s) (c := c)
        (F := G) (G := H) hOuterAdm)
  have hExpandRight :
      ∀ i ∈ s, OSInnerProduct d OS.S (G i) H =
        ∑ j ∈ s, c j * OSInnerProduct d OS.S (G i) (G j) := by
    intro i hi
    simpa [H, G, smul_eq_mul] using
      (OSInnerProduct_linearCombo_right (d := d) (OS := OS) (s := s) (c := c)
        (F := G i) (G := G) (fun j hj => hPairAdm i hi j hj))
  have hEq :
      OSInnerProduct d OS.S H H =
        ∑ i ∈ s, ∑ j ∈ s,
          starRingEnd ℂ (c i) * c j *
            OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t i + t j) F) := by
    rw [hExpandLeft]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hExpandRight i hi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hshiftEq :
        OSInnerProduct d OS.S (G i) (G j) =
            OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t i + t j) F) := by
      simpa [G] using
          (OSInnerProduct_timeShift_eq (d := d) (OS := OS) (F := F) (G := F)
          (s := t j) (t := t i) (hleft := hPairAdm i hi j hj)
          (hright := hShiftAdm i hi j hj))
    rw [mul_assoc]
    rw [hshiftEq]
  rwa [hEq] at hpos

/-- Positive Euclidean time translation descends to the honest OS quotient. -/
private theorem timeShiftPositiveTimeBorchers_respects_equiv
    (OS : OsterwalderSchraderAxioms d) (t : ℝ) (ht : 0 < t)
    (F G : PositiveTimeBorchersSequence d)
    (hFG : osBorchersSetoid OS F G) :
    osBorchersSetoid OS
      (timeShiftPositiveTimeBorchers (d := d) t ht F)
      (timeShiftPositiveTimeBorchers (d := d) t ht G) := by
  let A : PositiveTimeBorchersSequence d := F - G
  have hA :
      PositiveTimeBorchersSequence.osInner OS A A = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS A A hFG
  have hshift :
      PositiveTimeBorchersSequence.osInner OS
          (timeShiftPositiveTimeBorchers (d := d) t ht A)
          (timeShiftPositiveTimeBorchers (d := d) t ht A) =
        PositiveTimeBorchersSequence.osInner OS A
          (timeShiftPositiveTimeBorchers (d := d) (t + t) (add_pos ht ht) A) := by
    unfold PositiveTimeBorchersSequence.osInner
    simpa [timeShiftPositiveTimeBorchers] using
      (OSInnerProduct_timeShift_eq (d := d) (OS := OS)
        (F := (A : BorchersSequence d)) (G := (A : BorchersSequence d))
        (s := t) (t := t)
        (hleft := PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
          (timeShiftPositiveTimeBorchers (d := d) t ht A)
          (timeShiftPositiveTimeBorchers (d := d) t ht A))
        (hright := PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
          A (timeShiftPositiveTimeBorchers (d := d) (t + t) (add_pos ht ht) A)))
  have hshift_zero :
      PositiveTimeBorchersSequence.osInner OS
          (timeShiftPositiveTimeBorchers (d := d) t ht A)
          (timeShiftPositiveTimeBorchers (d := d) t ht A) = 0 := by
    rw [hshift]
    exact PositiveTimeBorchersSequence.null_osInner_zero OS A
      (timeShiftPositiveTimeBorchers (d := d) (t + t) (add_pos ht ht) A) hFG
  show (PositiveTimeBorchersSequence.osInner OS
      ((timeShiftPositiveTimeBorchers (d := d) t ht F) -
        (timeShiftPositiveTimeBorchers (d := d) t ht G))
      ((timeShiftPositiveTimeBorchers (d := d) t ht F) -
        (timeShiftPositiveTimeBorchers (d := d) t ht G))).re = 0
  have hfuncs :
      ∀ n,
        ((((timeShiftPositiveTimeBorchers (d := d) t ht F) -
            (timeShiftPositiveTimeBorchers (d := d) t ht G) :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          (((timeShiftPositiveTimeBorchers (d := d) t ht A :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simp [A, BorchersSequence.sub_funcs]
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS
          ((timeShiftPositiveTimeBorchers (d := d) t ht F) -
            (timeShiftPositiveTimeBorchers (d := d) t ht G))
          ((timeShiftPositiveTimeBorchers (d := d) t ht F) -
            (timeShiftPositiveTimeBorchers (d := d) t ht G)) =
        PositiveTimeBorchersSequence.osInner OS
          (timeShiftPositiveTimeBorchers (d := d) t ht A)
          (timeShiftPositiveTimeBorchers (d := d) t ht A) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, hshift_zero]
  simp

/-- The honest Euclidean time-shift operator on the OS quotient. -/
private def osTimeShift (OS : OsterwalderSchraderAxioms d) (t : ℝ) (ht : 0 < t) :
    OSPreHilbertSpace OS → OSPreHilbertSpace OS :=
  Quotient.map (timeShiftPositiveTimeBorchers (d := d) t ht)
    (fun F G hFG => timeShiftPositiveTimeBorchers_respects_equiv
      (d := d) OS t ht F G hFG)

private theorem osTimeShift_semigroup (OS : OsterwalderSchraderAxioms d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ∀ x : OSPreHilbertSpace OS,
      osTimeShift (d := d) OS s hs (osTimeShift (d := d) OS t ht x) =
        osTimeShift (d := d) OS (s + t) (add_pos hs ht) x := by
  intro x
  induction x using Quotient.inductionOn with
  | h F =>
    exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _
      (timeShiftPositiveTimeBorchers_comp_funcs (d := d) s t hs ht F)

/-- The honest Euclidean time-shift as a linear operator on the OS quotient. -/
private def osTimeShiftLinear (OS : OsterwalderSchraderAxioms d) (t : ℝ) (ht : 0 < t) :
    OSPreHilbertSpace OS →ₗ[ℂ] OSPreHilbertSpace OS where
  toFun := osTimeShift (d := d) OS t ht
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with
    | h F =>
      induction y using Quotient.inductionOn with
      | h G =>
        exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
          simp [BorchersSequence.add_funcs])
  map_smul' := by
    intro c x
    induction x using Quotient.inductionOn with
    | h F =>
      exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
        simp [BorchersSequence.smul_funcs])

private theorem osTimeShiftLinear_semigroup (OS : OsterwalderSchraderAxioms d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (osTimeShiftLinear (d := d) OS s hs).comp (osTimeShiftLinear (d := d) OS t ht) =
      osTimeShiftLinear (d := d) OS (s + t) (add_pos hs ht) := by
  ext x
  exact osTimeShift_semigroup (d := d) OS s t hs ht x

private theorem osTimeShiftLinear_inner_eq (OS : OsterwalderSchraderAxioms d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x y : OSPreHilbertSpace OS) :
    @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        ((osTimeShiftLinear (d := d) OS t ht) x)
        ((osTimeShiftLinear (d := d) OS s hs) y) =
      @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((osTimeShiftLinear (d := d) OS (t + s) (add_pos ht hs)) y) := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      change PositiveTimeBorchersSequence.osInner OS
          (timeShiftPositiveTimeBorchers (d := d) t ht F)
          (timeShiftPositiveTimeBorchers (d := d) s hs G) =
        PositiveTimeBorchersSequence.osInner OS F
          (timeShiftPositiveTimeBorchers (d := d) (t + s) (add_pos ht hs) G)
      unfold PositiveTimeBorchersSequence.osInner
      simpa [timeShiftPositiveTimeBorchers] using
        (OSInnerProduct_timeShift_eq (d := d) (OS := OS)
          (F := (F : BorchersSequence d)) (G := (G : BorchersSequence d))
          (s := s) (t := t)
          (hleft := PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
            (timeShiftPositiveTimeBorchers (d := d) t ht F)
            (timeShiftPositiveTimeBorchers (d := d) s hs G))
          (hright := PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
            F (timeShiftPositiveTimeBorchers (d := d) (t + s) (add_pos ht hs) G)))

private theorem osTimeShiftLinear_positive (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    0 ≤ RCLike.re
      (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((osTimeShiftLinear (d := d) OS t ht) x)) := by
  let hhalf : 0 < t / 2 := by linarith
  have hnonneg :
      0 ≤ RCLike.re
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          ((osTimeShiftLinear (d := d) OS (t / 2) hhalf) x)
          ((osTimeShiftLinear (d := d) OS (t / 2) hhalf) x)) :=
    OSPreHilbertSpace.inner_re_nonneg OS ((osTimeShiftLinear (d := d) OS (t / 2) hhalf) x)
  rw [osTimeShiftLinear_inner_eq (d := d) (OS := OS)
      (s := t / 2) (t := t / 2) hhalf hhalf x x] at hnonneg
  simpa using hnonneg

private theorem osTimeShiftLinear_kernel_nonneg (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (τ : ι → Set.Ioi (0 : ℝ)) (x : OSPreHilbertSpace OS) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s,
      starRingEnd ℂ (c i) * c j *
        @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((osTimeShiftLinear (d := d) OS ((τ i : ℝ) + (τ j : ℝ))
            (add_pos (τ i).2 (τ j).2)) x)).re := by
  induction x using Quotient.inductionOn with
  | h F =>
    simpa [osTimeShiftLinear, osTimeShift, timeShiftPositiveTimeBorchers] using
      (OSInnerProduct_timeShift_kernel_nonneg (d := d) (OS := OS)
        (s := s) (c := c) (t := fun i => (τ i : ℝ))
        (ht := fun i hi => (τ i).2) (F := (F : BorchersSequence d)) F.ordered_tsupport)

private theorem osTimeShiftLinear_kernel_im_zero (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (τ : ι → Set.Ioi (0 : ℝ)) (x : OSPreHilbertSpace OS) :
    (∑ i ∈ s, ∑ j ∈ s,
      starRingEnd ℂ (c i) * c j *
        @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((osTimeShiftLinear (d := d) OS ((τ i : ℝ) + (τ j : ℝ))
            (add_pos (τ i).2 (τ j).2)) x)).im = 0 := by
  let y : OSPreHilbertSpace OS :=
    ∑ i ∈ s, c i • ((osTimeShiftLinear (d := d) OS (τ i) (τ i).2) x)
  have hEq :
      (∑ i ∈ s, ∑ j ∈ s,
        starRingEnd ℂ (c i) * c j *
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            x ((osTimeShiftLinear (d := d) OS ((τ i : ℝ) + (τ j : ℝ))
              (add_pos (τ i).2 (τ j).2)) x)) =
      @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS) y y := by
    symm
    unfold y
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_smul_left, inner_smul_right]
    rw [osTimeShiftLinear_inner_eq (d := d) (OS := OS)
      (s := (τ j : ℝ)) (t := (τ i : ℝ)) (hs := (τ j).2) (ht := (τ i).2) (x := x) (y := x)]
    ring
  rw [hEq]
  simpa using (inner_self_im (𝕜 := ℂ) y)

private theorem osTimeShiftLinear_kernel_real_nonneg (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (τ : ι → Set.Ioi (0 : ℝ)) (x : OSPreHilbertSpace OS) :
    let q := ∑ i ∈ s, ∑ j ∈ s,
      starRingEnd ℂ (c i) * c j *
        @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((osTimeShiftLinear (d := d) OS ((τ i : ℝ) + (τ j : ℝ))
            (add_pos (τ i).2 (τ j).2)) x)
    q.im = 0 ∧ 0 ≤ q.re := by
  refine ⟨osTimeShiftLinear_kernel_im_zero (d := d) (OS := OS) s c τ x,
    osTimeShiftLinear_kernel_nonneg (d := d) (OS := OS) s c τ x⟩

private theorem tendsto_inner_osTimeShiftLinear_nhdsWithin_zero_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        if ht : 0 < t then
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS)
            ((osTimeShiftLinear (d := d) OS t ht) (⟦G⟧ : OSPreHilbertSpace OS))
        else
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS) (⟦G⟧ : OSPreHilbertSpace OS))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          (⟦F⟧ : OSPreHilbertSpace OS) (⟦G⟧ : OSPreHilbertSpace OS))) := by
  have hraw :
      Filter.Tendsto
        (fun t : ℝ =>
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) t (G : BorchersSequence d)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OSInnerProduct d OS.S (F : BorchersSequence d) (G : BorchersSequence d))) :=
    tendsto_OSInnerProduct_right_timeShift_nhdsWithin_zero_of_isCompactSupport
      (d := d) OS (F := (F : BorchersSequence d)) (G := (G : BorchersSequence d))
      F.ordered_tsupport G.ordered_tsupport hG_compact
  have hEq :
      Filter.EventuallyEq
        (nhdsWithin 0 (Set.Ioi 0))
        (fun t : ℝ =>
          if ht : 0 < t then
            @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              (⟦F⟧ : OSPreHilbertSpace OS)
              ((osTimeShiftLinear (d := d) OS t ht) (⟦G⟧ : OSPreHilbertSpace OS))
          else
            @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              (⟦F⟧ : OSPreHilbertSpace OS) (⟦G⟧ : OSPreHilbertSpace OS))
        (fun t : ℝ =>
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) t (G : BorchersSequence d))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos : 0 < t := ht
    simp [hpos, osTimeShiftLinear, osTimeShift, PositiveTimeBorchersSequence.osInner]
  simpa [PositiveTimeBorchersSequence.osInner, OSPreHilbertSpace.inner_eq] using
    (Filter.Tendsto.congr' hEq.symm hraw)

/-- Nelson reflection identity on the honest OS quotient:
`‖T(t)x‖² = Re ⟪x, T(2t)x⟫`. This is the algebraic starting point of the
multiple-reflection contraction argument. -/
private theorem osTimeShiftLinear_norm_sq_eq_re_inner_double
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ^ 2 =
      RCLike.re
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht)) x)) := by
  calc
    ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ^ 2 =
        RCLike.re
          (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            ((osTimeShiftLinear (d := d) OS t ht) x)
            ((osTimeShiftLinear (d := d) OS t ht) x)) := by
          simpa using
            (inner_self_eq_norm_sq (𝕜 := ℂ) ((osTimeShiftLinear (d := d) OS t ht) x)).symm
    _ = RCLike.re
          (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            x ((osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht)) x)) := by
          rw [osTimeShiftLinear_inner_eq (d := d) (OS := OS)
            (s := t) (t := t) ht ht x x]

/-- First multiple-reflection estimate on the honest OS quotient. The remaining
contraction step is to combine this recursion with a large-time polynomial bound
coming from `OSLinearGrowthCondition`. -/
private theorem osTimeShiftLinear_multipleReflection_ineq
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ^ 2 ≤
      ‖x‖ * ‖(osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht)) x‖ := by
  calc
    ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ^ 2 =
        RCLike.re
          (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            x ((osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht)) x)) :=
      osTimeShiftLinear_norm_sq_eq_re_inner_double (d := d) OS t ht x
    _ ≤ ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht)) x)‖ :=
      RCLike.re_le_norm _
    _ ≤ ‖x‖ * ‖(osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht)) x‖ :=
      norm_inner_le_norm _ _

private theorem exists_norm_osTimeShiftLinear_le_polynomial_of_repr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
      ‖(osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)‖ ≤
        C * t ^ lgc.sobolev_index := by
  obtain ⟨C0, hC0_nonneg, hC0⟩ :=
    exists_norm_OSInnerProduct_right_timeShift_le_polynomial (d := d) OS lgc F F
  let C : ℝ := C0 * (2 : ℝ) ^ lgc.sobolev_index + 1
  refine ⟨C, by
    dsimp [C]
    positivity, ?_⟩
  intro t ht1 ht
  have ht0 : 0 ≤ t := by linarith
  have h2t_ge : 1 ≤ t + t := by linarith
  let y : OSPreHilbertSpace OS :=
    (osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)
  have hsq :
      ‖y‖ ^ 2 ≤ C0 * (t + t) ^ lgc.sobolev_index := by
    calc
      ‖y‖ ^ 2 =
          RCLike.re
            (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              (⟦F⟧ : OSPreHilbertSpace OS)
              ((osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht))
                (⟦F⟧ : OSPreHilbertSpace OS))) := by
            simpa [y] using
              osTimeShiftLinear_norm_sq_eq_re_inner_double (d := d) OS t ht
                (⟦F⟧ : OSPreHilbertSpace OS)
      _ ≤ ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS)
            ((osTimeShiftLinear (d := d) OS (t + t) (add_pos ht ht))
              (⟦F⟧ : OSPreHilbertSpace OS))‖ :=
          RCLike.re_le_norm _
      _ = ‖OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) (t + t) (F : BorchersSequence d))‖ := by
          simp [PositiveTimeBorchersSequence.osInner, OSPreHilbertSpace.inner_eq,
            osTimeShiftLinear, osTimeShift, timeShiftPositiveTimeBorchers]
      _ ≤ C0 * (t + t) ^ lgc.sobolev_index := hC0 (t + t) h2t_ge
  have hsq' :
      ‖y‖ ^ 2 ≤ (C0 * (2 : ℝ) ^ lgc.sobolev_index) * t ^ lgc.sobolev_index := by
    calc
      ‖y‖ ^ 2 ≤ C0 * (t + t) ^ lgc.sobolev_index := hsq
      _ = C0 * ((2 : ℝ) ^ lgc.sobolev_index * t ^ lgc.sobolev_index) := by
          rw [show t + t = (2 : ℝ) * t by ring, mul_pow]
      _ = (C0 * (2 : ℝ) ^ lgc.sobolev_index) * t ^ lgc.sobolev_index := by
          ring
  have hone : 1 ≤ t ^ lgc.sobolev_index := one_le_pow₀ ht1
  calc
    ‖(osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)‖ = ‖y‖ := by
      rfl
    _ ≤ ‖y‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖y‖ - (1 / 2 : ℝ))]
    _ ≤ (C0 * (2 : ℝ) ^ lgc.sobolev_index) * t ^ lgc.sobolev_index + t ^ lgc.sobolev_index := by
      nlinarith [hsq', hone]
    _ = C * t ^ lgc.sobolev_index := by
      dsimp [C]
      ring

private theorem exists_norm_osTimeShiftLinear_le_polynomial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSPreHilbertSpace OS) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
      ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ≤ C * t ^ lgc.sobolev_index := by
  induction x using Quotient.inductionOn with
  | h F =>
      simpa using
        exists_norm_osTimeShiftLinear_le_polynomial_of_repr (d := d) OS lgc F

private theorem osTimeShiftLinear_contraction
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ≤ ‖x‖ := by
  obtain ⟨C, hC_pos, hgrowth⟩ :=
    exists_norm_osTimeShiftLinear_le_polynomial (d := d) OS lgc x
  let N : ℝ → ℝ := fun s =>
    if hs : 0 < s then ‖(osTimeShiftLinear (d := d) OS s hs) x‖ else ‖x‖
  have hD : SCV.MultipleReflection.HasDoublingBound N := by
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      simp [N, hs]
    · simp [N]
    · intro s hs
      have hs2 : 0 < 2 * s := by linarith
      simpa [N, hs, hs2, two_mul] using
        osTimeShiftLinear_multipleReflection_ineq (d := d) OS s hs x
  have hbound : ∀ T, 1 ≤ T → N T ≤ C * T ^ (lgc.sobolev_index : ℝ) := by
    intro T hT
    have hT_pos : 0 < T := by linarith
    have h := hgrowth T hT hT_pos
    simpa [N, hT_pos, Real.rpow_natCast] using h
  have hcontr := SCV.MultipleReflection.contraction_of_doubling_and_growth
    N hD C lgc.sobolev_index hC_pos (by positivity) hbound t ht
  simpa [N, ht] using hcontr

private def euclideanSemigroup_of_OSLinearGrowthCondition
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    EuclideanSemigroup OS where
  T := fun t ht => osTimeShiftLinear (d := d) OS t ht
  semigroup := fun s t hs ht => osTimeShiftLinear_semigroup (d := d) OS s t hs ht
  contraction := fun t ht x => osTimeShiftLinear_contraction (d := d) OS lgc t ht x
  positive := fun t ht x => osTimeShiftLinear_positive (d := d) OS t ht x

/-- The Hilbert completion of the honest OS pre-Hilbert quotient. -/
abbrev OSHilbertSpace (OS : OsterwalderSchraderAxioms d) :=
  UniformSpace.Completion (OSPreHilbertSpace OS)

private local instance instSemiringOSHilbertEnd (OS : OsterwalderSchraderAxioms d) :
    Semiring (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) :=
  ContinuousLinearMap.semiring

private local instance instAlgebraRealOSHilbertEnd (OS : OsterwalderSchraderAxioms d) :
    Algebra ℝ (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) :=
  ContinuousLinearMap.algebra

/-- The positive Euclidean shift as a bounded operator on the OS pre-Hilbert
space. -/
private noncomputable def osTimeShiftContinuous
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    OSPreHilbertSpace OS →L[ℂ] OSPreHilbertSpace OS :=
  (osTimeShiftLinear (d := d) OS t ht).mkContinuous 1 (fun x => by
    simpa using osTimeShiftLinear_contraction (d := d) OS lgc t ht x)

@[simp] private theorem osTimeShiftContinuous_apply
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    osTimeShiftContinuous (d := d) OS lgc t ht x =
      osTimeShiftLinear (d := d) OS t ht x := rfl

/-- The positive Euclidean shift extended to the Hilbert completion. -/
noncomputable def osTimeShiftHilbert
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  (UniformSpace.Completion.toComplL.comp (osTimeShiftContinuous (d := d) OS lgc t ht)).extend
    UniformSpace.Completion.toComplL

private theorem osTimeShiftHilbert_coe
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    osTimeShiftHilbert (d := d) OS lgc t ht (x : OSHilbertSpace OS) =
      ((osTimeShiftLinear (d := d) OS t ht x : OSPreHilbertSpace OS) : OSHilbertSpace OS) := by
  exact ContinuousLinearMap.extend_eq _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _) x

theorem osTimeShiftHilbert_contraction
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) (x : OSHilbertSpace OS) :
    ‖osTimeShiftHilbert (d := d) OS lgc t ht x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_le (osTimeShiftHilbert (d := d) OS lgc t ht).continuous.norm continuous_norm
  · intro a
    rw [osTimeShiftHilbert_coe (d := d) OS lgc t ht a,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact osTimeShiftLinear_contraction (d := d) OS lgc t ht a

private theorem osTimeShiftHilbert_semigroup
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    osTimeShiftHilbert (d := d) OS lgc (s + t) (add_pos hs ht) =
      (osTimeShiftHilbert (d := d) OS lgc s hs).comp
        (osTimeShiftHilbert (d := d) OS lgc t ht) :=
  ContinuousLinearMap.extend_unique _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _)
    ((osTimeShiftHilbert (d := d) OS lgc s hs).comp
      (osTimeShiftHilbert (d := d) OS lgc t ht)) (by
        ext x
        change
          osTimeShiftHilbert (d := d) OS lgc s hs
              ((osTimeShiftHilbert (d := d) OS lgc t ht)
                (x : OSHilbertSpace OS)) =
            (((osTimeShiftContinuous (d := d) OS lgc (s + t) (add_pos hs ht) x) :
              OSPreHilbertSpace OS) : OSHilbertSpace OS)
        rw [osTimeShiftHilbert_coe (d := d) OS lgc t ht x]
        change
          osTimeShiftHilbert (d := d) OS lgc s hs
              (((osTimeShiftLinear (d := d) OS t ht x) : OSPreHilbertSpace OS) :
                OSHilbertSpace OS) =
            (((osTimeShiftLinear (d := d) OS (s + t) (add_pos hs ht) x) :
              OSPreHilbertSpace OS) : OSHilbertSpace OS)
        rw [osTimeShiftHilbert_coe (d := d) OS lgc s hs
          ((osTimeShiftLinear (d := d) OS t ht x) : OSPreHilbertSpace OS)]
        congr 1
        exact congrArg (fun f => f x)
          (osTimeShiftLinear_semigroup (d := d) OS s t hs ht))

private theorem osTimeShiftLinear_apply_inner_self_real_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    let q := @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
      ((osTimeShiftLinear (d := d) OS t ht) x) x
    q.im = 0 ∧ 0 ≤ q.re := by
  let hhalf : 0 < t / 2 := by linarith
  have hEq :
      @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((osTimeShiftLinear (d := d) OS t ht) x) =
      @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        ((osTimeShiftLinear (d := d) OS (t / 2) hhalf) x)
        ((osTimeShiftLinear (d := d) OS (t / 2) hhalf) x) := by
    simpa [show t / 2 + t / 2 = t by ring] using
      (osTimeShiftLinear_inner_eq (d := d) (OS := OS)
        (s := t / 2) (t := t / 2) hhalf hhalf x x).symm
  have him0 :
      (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((osTimeShiftLinear (d := d) OS t ht) x)).im = 0 := by
    rw [hEq]
    simpa using inner_self_im (𝕜 := ℂ)
      ((osTimeShiftLinear (d := d) OS (t / 2) hhalf) x)
  have hre0 :
      0 ≤ (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        x ((osTimeShiftLinear (d := d) OS t ht) x)).re := by
    rw [hEq]
    simpa using inner_self_nonneg (𝕜 := ℂ)
      (x := (osTimeShiftLinear (d := d) OS (t / 2) hhalf) x)
  constructor
  · simpa [him0] using
      (inner_im_symm (𝕜 := ℂ)
        ((osTimeShiftLinear (d := d) OS t ht) x) x)
  · have hre :
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          ((osTimeShiftLinear (d := d) OS t ht) x) x).re =
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x ((osTimeShiftLinear (d := d) OS t ht) x)).re := by
      simpa using
        (inner_re_symm (𝕜 := ℂ)
          ((osTimeShiftLinear (d := d) OS t ht) x) x)
    rw [hre]
    exact hre0

private theorem osTimeShiftHilbert_apply_inner_self_real_nonneg
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) (x : OSHilbertSpace OS) :
    let q := @inner ℂ (OSHilbertSpace OS) inferInstance
      ((osTimeShiftHilbert (d := d) OS lgc t ht) x) x
    q.im = 0 ∧ 0 ≤ q.re := by
  let T := osTimeShiftHilbert (d := d) OS lgc t ht
  let good : Set (OSHilbertSpace OS) := {
      x | let q := @inner ℂ (OSHilbertSpace OS) inferInstance (T x) x
        ; q.im = 0 ∧ 0 ≤ q.re }
  have hgood_closed : IsClosed good := by
    let qfun : OSHilbertSpace OS → ℂ := fun x =>
      @inner ℂ (OSHilbertSpace OS) inferInstance (T x) x
    have hqfun : Continuous qfun := T.continuous.inner continuous_id
    have him :
        IsClosed {x : OSHilbertSpace OS | (qfun x).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp hqfun) continuous_const
    have hre :
        IsClosed {x : OSHilbertSpace OS | 0 ≤ (qfun x).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp hqfun)
    have hEq :
        good = {x : OSHilbertSpace OS | (qfun x).im = 0} ∩
          {x : OSHilbertSpace OS | 0 ≤ (qfun x).re} := by
      ext y
      simp [good, qfun]
    rw [hEq]
    exact him.inter hre
  have hx : x ∈ good := by
    refine UniformSpace.Completion.induction_on x hgood_closed ?_
    intro a
    simpa [good, T, osTimeShiftHilbert_coe, UniformSpace.Completion.inner_coe] using
      (osTimeShiftLinear_apply_inner_self_real_nonneg (d := d) OS t ht a)
  exact hx

theorem osTimeShiftHilbert_isPositive
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    (osTimeShiftHilbert (d := d) OS lgc t ht).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hq := osTimeShiftHilbert_apply_inner_self_real_nonneg
    (d := d) OS lgc t ht x
  refine ⟨?_, hq.2⟩
  apply Complex.ext <;> simp [hq.1]

theorem osTimeShiftHilbert_isSelfAdjoint
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    IsSelfAdjoint (osTimeShiftHilbert (d := d) OS lgc t ht) :=
  (osTimeShiftHilbert_isPositive (d := d) OS lgc t ht).isSelfAdjoint

private theorem osTimeShiftHilbert_unbounded_isSelfAdjoint
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    (UnboundedOperator.ofContinuousLinearMap
      (osTimeShiftHilbert (d := d) OS lgc t ht)).IsSelfAdjoint
        (UnboundedOperator.ofContinuousLinearMap_isDenselyDefined
          (osTimeShiftHilbert (d := d) OS lgc t ht)) := by
  exact UnboundedOperator.isSelfAdjoint_ofContinuousLinearMap
    (osTimeShiftHilbert (d := d) OS lgc t ht)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc t ht)

private theorem osTimeShiftHilbert_unbounded_isPositive
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    (UnboundedOperator.ofContinuousLinearMap
      (osTimeShiftHilbert (d := d) OS lgc t ht)).IsPositive := by
  exact UnboundedOperator.isPositive_ofContinuousLinearMap
    (osTimeShiftHilbert (d := d) OS lgc t ht)
    (fun x => (osTimeShiftHilbert_isPositive (d := d) OS lgc t ht).re_inner_nonneg_left x)

theorem osTimeShiftHilbert_nonneg
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ osTimeShiftHilbert (d := d) OS lgc t ht := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact osTimeShiftHilbert_isPositive (d := d) OS lgc t ht

/-- The completed OS time-shift is a contraction in operator norm. -/
theorem osTimeShiftHilbert_norm_le_one
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    ‖osTimeShiftHilbert (d := d) OS lgc t ht‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simpa [one_mul] using osTimeShiftHilbert_contraction (d := d) OS lgc t ht x

/-- The spectrum of the completed OS time-shift is contained in `[0,1]`. -/
theorem spectrum_osTimeShiftHilbert_subset_Icc
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    spectrum ℝ (osTimeShiftHilbert (d := d) OS lgc t ht) ⊆ Set.Icc 0 1 := by
  intro x hx
  constructor
  · exact spectrum_nonneg_of_nonneg
      (osTimeShiftHilbert_nonneg (d := d) OS lgc t ht) hx
  · have hnorm_le :
        ‖osTimeShiftHilbert (d := d) OS lgc t ht‖ ≤ 1 :=
      osTimeShiftHilbert_norm_le_one (d := d) OS lgc t ht
    have hle_one :
        osTimeShiftHilbert (d := d) OS lgc t ht ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg
        (osTimeShiftHilbert (d := d) OS lgc t ht)
        (osTimeShiftHilbert_nonneg (d := d) OS lgc t ht)).1 hnorm_le
    have hspectrum_le :
        ∀ y ∈ spectrum ℝ (osTimeShiftHilbert (d := d) OS lgc t ht), y ≤ 1 :=
      (le_algebraMap_iff_spectrum_le
        (R := ℝ)
        (a := osTimeShiftHilbert (d := d) OS lgc t ht)
        (r := 1)
        (ha := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc t ht)).1
        (by
          show osTimeShiftHilbert (d := d) OS lgc t ht ≤
            algebraMap ℝ (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) 1
          simpa using hle_one)
    exact hspectrum_le x hx

private theorem osTimeShiftHilbert_reciprocal_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (hn : 0 < n) :
    osTimeShiftHilbert (d := d) OS lgc ((n : ℝ)⁻¹)
        (inv_pos.mpr (by exact_mod_cast hn)) =
      CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) ((n : ℝ≥0)⁻¹) := by
  simpa using ContinuousLinearMap.semigroup_reciprocal_eq_positive_qroot
    (T := fun t ht => osTimeShiftHilbert (d := d) OS lgc t ht)
    (hsemigroup := by
      intro s hs t ht
      simpa [show (HMul.hMul :
          (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) → _ → _) =
          ContinuousLinearMap.comp from rfl] using
        osTimeShiftHilbert_semigroup (d := d) OS lgc s t hs ht)
    (hnonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc)
    n hn

private theorem osTimeShiftHilbert_rational_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    osTimeShiftHilbert (d := d) OS lgc ((p : ℝ) * (q : ℝ)⁻¹)
        (mul_pos (by exact_mod_cast hp) (inv_pos.mpr (by exact_mod_cast hq))) =
      CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        ((p : ℝ≥0) * (q : ℝ≥0)⁻¹) := by
  simpa using ContinuousLinearMap.semigroup_rational_eq_positive_qroot
    (T := fun t ht => osTimeShiftHilbert (d := d) OS lgc t ht)
    (hsemigroup := by
      intro s hs t ht
      simpa [show (HMul.hMul :
          (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) → _ → _) =
          ContinuousLinearMap.comp from rfl] using
        osTimeShiftHilbert_semigroup (d := d) OS lgc s t hs ht)
    (hnonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc)
    p q hp hq

/-- For a contraction family indexed by positive times, scalar-kernel continuity
at `0⁺` implies strong continuity at `0⁺`. This is the direct endpoint argument
needed for the honest OS semigroup, and avoids the earlier `2t`/filter-plumbing
route. -/
private theorem tendsto_apply_nhdsWithin_zero_of_contraction_of_re_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : ∀ t : ℝ, 0 < t → E →ₗ[ℂ] E)
    (hcontr : ∀ t : ℝ, ∀ ht : 0 < t, ∀ x : E, ‖(T t ht) x‖ ≤ ‖x‖)
    (x : E)
    (hkernel :
      Filter.Tendsto
        (fun t : ℝ =>
          if ht : 0 < t then
            RCLike.re (@inner ℂ E _ x ((T t ht) x))
          else
            RCLike.re (@inner ℂ E _ x x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (RCLike.re (@inner ℂ E _ x x)))) :
    Filter.Tendsto
      (fun t : ℝ => if ht : 0 < t then (T t ht) x else x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds x) := by
  have hxnorm : RCLike.re (@inner ℂ E _ x x) = ‖x‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hδ : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  rw [Metric.tendsto_nhdsWithin_nhds] at hkernel
  obtain ⟨r, hr, hball⟩ := hkernel (ε ^ 2 / 2) hδ
  refine ⟨r, hr, ?_⟩
  intro t ht_pos ht_dist
  have hpos : 0 < t := ht_pos
  have hclose := hball ht_pos ht_dist
  simp [hpos, Real.dist_eq] at hclose
  have hgap :
      ‖x‖ ^ 2 - RCLike.re (@inner ℂ E _ x ((T t hpos) x)) < ε ^ 2 / 2 := by
    have hclose' :
        |RCLike.re (@inner ℂ E _ x ((T t hpos) x)) - (↑(‖x‖ ^ 2) : ℂ).re| < ε ^ 2 / 2 := by
      simpa [hpos] using hclose
    rcases abs_lt.mp hclose' with ⟨hleft, hright⟩
    have hleft' :
        -(ε ^ 2 / 2) < RCLike.re (@inner ℂ E _ x ((T t hpos) x)) - ‖x‖ ^ 2 := by
      have hcast : ((↑(‖x‖ ^ 2) : ℂ).re) = ‖x‖ ^ 2 := rfl
      nlinarith [hleft, hcast]
    nlinarith
  have hcontr_sq : ‖(T t hpos) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [hcontr t hpos x, norm_nonneg ((T t hpos) x), norm_nonneg x]
  have hexpand :
      ‖(T t hpos) x - x‖ ^ 2 =
        ‖(T t hpos) x‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ x ((T t hpos) x)) +
          ‖x‖ ^ 2 := by
    rw [@norm_sub_sq ℂ E _ _ _]
    have hsym :
        RCLike.re (@inner ℂ E _ ((T t hpos) x) x) =
          RCLike.re (@inner ℂ E _ x ((T t hpos) x)) := by
      simpa using inner_re_symm (𝕜 := ℂ) ((T t hpos) x) x
    linarith
  have hnsq : ‖(T t hpos) x - x‖ ^ 2 < ε ^ 2 := by
    calc
      ‖(T t hpos) x - x‖ ^ 2
        = ‖(T t hpos) x‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ x ((T t hpos) x)) +
            ‖x‖ ^ 2 := hexpand
      _ ≤ 2 * (‖x‖ ^ 2 - RCLike.re (@inner ℂ E _ x ((T t hpos) x))) := by
          linarith
      _ < 2 * (ε ^ 2 / 2) := by nlinarith
      _ = ε ^ 2 := by ring
  rw [dist_eq_norm]
  have hroot : ‖(T t hpos) x - x‖ < ε :=
    lt_of_pow_lt_pow_left₀ 2 hε.le (by simpa using hnsq)
  simpa [hpos] using hroot

private theorem continuousOn_inner_osTimeShiftLinear_nonneg_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    ContinuousOn
      (fun t : ℝ =>
        if ht : 0 < t then
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS)
            ((osTimeShiftLinear (d := d) OS t ht) (⟦G⟧ : OSPreHilbertSpace OS))
        else
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS) (⟦G⟧ : OSPreHilbertSpace OS))
      (Set.Ici 0) := by
  have hraw :
      ContinuousOn
        (fun t : ℝ =>
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) t (G : BorchersSequence d)))
        (Set.Ici 0) :=
    continuousOn_OSInnerProduct_right_timeShift_nonneg_of_isCompactSupport
      (d := d) OS (F := (F : BorchersSequence d)) (G := (G : BorchersSequence d))
      F.ordered_tsupport G.ordered_tsupport hG_compact
  have hEq :
      Set.EqOn
        (fun t : ℝ =>
          if ht : 0 < t then
            @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              (⟦F⟧ : OSPreHilbertSpace OS)
              ((osTimeShiftLinear (d := d) OS t ht) (⟦G⟧ : OSPreHilbertSpace OS))
          else
            @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              (⟦F⟧ : OSPreHilbertSpace OS) (⟦G⟧ : OSPreHilbertSpace OS))
        (fun t : ℝ =>
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) t (G : BorchersSequence d)))
        (Set.Ici 0) := by
    intro t ht
    have hnonneg : 0 ≤ t := ht
    by_cases hpos : 0 < t
    · simp [hpos, osTimeShiftLinear, osTimeShift, PositiveTimeBorchersSequence.osInner]
    · have ht0 : t = 0 := by linarith
      subst ht0
      simpa [hpos, PositiveTimeBorchersSequence.osInner, OSPreHilbertSpace.inner_eq] using
        (OSInnerProduct_right_timeShift_zero (d := d) (OS := OS)
          (F := (F : BorchersSequence d)) (G := (G : BorchersSequence d))).symm
  exact hraw.congr hEq

private theorem tendsto_osTimeShiftLinear_nhdsWithin_zero_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        if ht : 0 < t then
          (osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)
        else
          (⟦F⟧ : OSPreHilbertSpace OS))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (⟦F⟧ : OSPreHilbertSpace OS)) := by
  let x0 : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
  refine tendsto_apply_nhdsWithin_zero_of_contraction_of_re_inner
    (T := fun t ht => osTimeShiftLinear (d := d) OS t ht)
    (hcontr := fun t ht x => osTimeShiftLinear_contraction (d := d) OS lgc t ht x)
    (x := x0) ?_
  have hinner :=
    tendsto_inner_osTimeShiftLinear_nhdsWithin_zero_of_isCompactSupport
      (d := d) OS F F hF_compact
  have hre0 :
      Filter.Tendsto
        (fun t : ℝ =>
          Complex.re
            (if ht : 0 < t then
              @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
                x0
                ((osTimeShiftLinear (d := d) OS t ht) x0)
            else
              (↑(‖x0‖ ^ 2) : ℂ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((↑(‖x0‖ ^ 2) : ℂ).re)) := by
    simpa [x0, Function.comp] using
      (Complex.continuous_re.continuousAt.tendsto.comp hinner)
  have hEq :
      (fun t : ℝ =>
        Complex.re
          (if ht : 0 < t then
            @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              x0
              ((osTimeShiftLinear (d := d) OS t ht) x0)
          else
            (↑(‖x0‖ ^ 2) : ℂ))) =
      (fun t : ℝ =>
        if ht : 0 < t then
          RCLike.re
            (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
              x0
              ((osTimeShiftLinear (d := d) OS t ht) x0))
        else
            (↑(‖x0‖ ^ 2) : ℂ).re) := by
    funext t
    by_cases ht : 0 < t <;> simp [ht]
  rw [hEq] at hre0
  have hnorm :
      (↑(‖x0‖ ^ 2) : ℂ).re =
        RCLike.re
          (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS) x0 x0) := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x0).symm
  simpa [hnorm] using hre0

private theorem continuousOn_osTimeShiftLinear_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    ContinuousOn
      (fun t : ℝ =>
        if ht : 0 < t then
          (osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)
        else
          (⟦F⟧ : OSPreHilbertSpace OS))
      (Set.Ioi 0) := by
  intro t0 ht0
  have ht0_pos : 0 < t0 := ht0
  let x0 : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
  let f : ℝ → OSPreHilbertSpace OS := fun t =>
    if ht : 0 < t then
      (osTimeShiftLinear (d := d) OS t ht) x0
    else
      x0
  let κ : ℝ → ℝ := fun t =>
    if ht : 0 < t then
      RCLike.re
        (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          x0 ((osTimeShiftLinear (d := d) OS t ht) x0))
    else
      (↑(‖x0‖ ^ 2) : ℂ).re
  let dSq : ℝ → ℝ := fun t =>
    if ht : 0 < t then
      ‖(osTimeShiftLinear (d := d) OS t ht) x0 -
          (osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ ^ 2
    else
      0
  let h : ℝ → ℝ := fun t =>
    κ (t + t) - 2 * κ (t + t0) + κ (t0 + t0)
  have hκ :
      ContinuousOn κ (Set.Ici 0) := by
    refine (Complex.continuous_re.comp_continuousOn
      (continuousOn_inner_osTimeShiftLinear_nonneg_of_isCompactSupport
        (d := d) OS F F hF_compact)).congr ?_
    intro t ht
    have hnonneg : 0 ≤ t := ht
    by_cases hpos : 0 < t
    · simp [κ, x0, hpos]
    · have ht0 : t = 0 := by
        have hle : t ≤ 0 := by exact le_of_not_gt hpos
        exact le_antisymm hle hnonneg
      subst ht0
      simp [κ, x0]
  have hκ_tt :
      ContinuousAt κ (t0 + t0) := by
    have ht0_2 : 0 < t0 + t0 := add_pos ht0_pos ht0_pos
    rw [← continuousWithinAt_iff_continuousAt (Ici_mem_nhds ht0_2)]
    exact hκ (t0 + t0) ht0_2.le
  have hκ_double : ContinuousAt (fun t : ℝ => κ (t + t)) t0 := by
    have hadd : ContinuousAt (fun t : ℝ => t + t) t0 :=
      continuousAt_id.add continuousAt_id
    simpa [Function.comp] using
      (ContinuousAt.comp (f := fun t : ℝ => t + t) hκ_tt hadd)
  have hκ_shift : ContinuousAt (fun t : ℝ => κ (t + t0)) t0 := by
    have hadd : ContinuousAt (fun t : ℝ => t + t0) t0 :=
      continuousAt_id.add continuousAt_const
    simpa [Function.comp] using
      (ContinuousAt.comp (f := fun t : ℝ => t + t0) hκ_tt hadd)
  have hh_cont : ContinuousAt h t0 := by
    refine (hκ_double.sub ?_).add continuousAt_const
    exact continuousAt_const.mul hκ_shift
  have hh_zero : h t0 = 0 := by
    simp [h, κ, ht0_pos, add_pos ht0_pos ht0_pos]
    ring
  have hdSq_eq :
      Filter.EventuallyEq (nhdsWithin t0 (Set.Ioi 0)) dSq h := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have ht2 : 0 < t + t := add_pos htpos htpos
    have ht_t0 : 0 < t + t0 := add_pos htpos ht0_pos
    have ht0_2 : 0 < t0 + t0 := add_pos ht0_pos ht0_pos
    have hnorm_t : ‖(osTimeShiftLinear (d := d) OS t htpos) x0‖ ^ 2 = κ (t + t) := by
      calc
        ‖(osTimeShiftLinear (d := d) OS t htpos) x0‖ ^ 2 =
            RCLike.re
              (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
                ((osTimeShiftLinear (d := d) OS t htpos) x0)
                ((osTimeShiftLinear (d := d) OS t htpos) x0)) := by
                  simpa using
                    (inner_self_eq_norm_sq (𝕜 := ℂ)
                      ((osTimeShiftLinear (d := d) OS t htpos) x0)).symm
        _ = RCLike.re
              (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
                x0 ((osTimeShiftLinear (d := d) OS (t + t) ht2) x0)) := by
                  rw [osTimeShiftLinear_inner_eq (d := d) (OS := OS)
                    (s := t) (t := t) htpos htpos x0 x0]
        _ = κ (t + t) := by simp [κ, ht2]
    have hnorm_t0 :
        ‖(osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ ^ 2 = κ (t0 + t0) := by
      calc
        ‖(osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ ^ 2 =
            RCLike.re
              (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
                ((osTimeShiftLinear (d := d) OS t0 ht0_pos) x0)
                ((osTimeShiftLinear (d := d) OS t0 ht0_pos) x0)) := by
                  simpa using
                    (inner_self_eq_norm_sq (𝕜 := ℂ)
                      ((osTimeShiftLinear (d := d) OS t0 ht0_pos) x0)).symm
        _ = RCLike.re
              (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
                x0 ((osTimeShiftLinear (d := d) OS (t0 + t0) ht0_2) x0)) := by
                  rw [osTimeShiftLinear_inner_eq (d := d) (OS := OS)
                    (s := t0) (t := t0) ht0_pos ht0_pos x0 x0]
        _ = κ (t0 + t0) := by simp [κ, ht0_2]
    calc
      dSq t =
          ‖(osTimeShiftLinear (d := d) OS t htpos) x0 -
              (osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ ^ 2 := by
            simp [dSq, htpos]
      _ =
          ‖(osTimeShiftLinear (d := d) OS t htpos) x0‖ ^ 2 -
            2 * RCLike.re
              (@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
                ((osTimeShiftLinear (d := d) OS t htpos) x0)
                ((osTimeShiftLinear (d := d) OS t0 ht0_pos) x0)) +
            ‖(osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ ^ 2 := by
              rw [@norm_sub_sq ℂ (OSPreHilbertSpace OS) _ _ _]
      _ = κ (t + t) - 2 * κ (t + t0) + κ (t0 + t0) := by
            rw [hnorm_t,
              osTimeShiftLinear_inner_eq (d := d) (OS := OS)
                (s := t0) (t := t) ht0_pos htpos x0 x0,
              hnorm_t0]
            simp [κ, ht2, ht_t0, ht0_2]
  have hdSq_tendsto :
      Filter.Tendsto dSq (nhdsWithin t0 (Set.Ioi 0)) (nhds 0) := by
    have hh_tendsto :
        Filter.Tendsto h (nhdsWithin t0 (Set.Ioi 0)) (nhds 0) := by
      simpa [hh_zero] using hh_cont.continuousWithinAt.tendsto
    exact Filter.Tendsto.congr' hdSq_eq.symm hh_tendsto
  rw [ContinuousWithinAt]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [Metric.tendsto_nhdsWithin_nhds] at hdSq_tendsto
  obtain ⟨δ, hδ, hball⟩ := hdSq_tendsto (ε ^ 2) hε2
  refine ⟨δ, hδ, ?_⟩
  intro t ht_pos ht_dist
  have hti : 0 < t := ht_pos
  have hdSq_nonneg : 0 ≤ dSq t := by simp [dSq, hti]
  have hsquare :
      ‖(osTimeShiftLinear (d := d) OS t hti) x0 -
          (osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ ^ 2 < ε ^ 2 := by
    have hclose : dist (dSq t) 0 < ε ^ 2 := hball ht_pos ht_dist
    simpa [Real.dist_eq, abs_of_nonneg hdSq_nonneg, dSq, hti] using hclose
  have hnorm :
      ‖(osTimeShiftLinear (d := d) OS t hti) x0 -
          (osTimeShiftLinear (d := d) OS t0 ht0_pos) x0‖ < ε :=
    lt_of_pow_lt_pow_left₀ 2 hε.le (by simpa using hsquare)
  simpa [f, hti, ht0_pos, x0, dist_eq_norm] using hnorm

private theorem continuousOn_osTimeShiftHilbert_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    ContinuousOn
      (fun t : ℝ =>
        if ht : 0 < t then
          osTimeShiftHilbert (d := d) OS lgc t ht
            (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        else
          (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
      (Set.Ioi 0) := by
  let x0 : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
  let hcoe :
      ContinuousOn
        (fun t : ℝ =>
          (((if ht : 0 < t then
              (osTimeShiftLinear (d := d) OS t ht) x0
            else
              x0) : OSPreHilbertSpace OS) : OSHilbertSpace OS))
        (Set.Ioi 0) :=
    by
      let htoCompl :
          Continuous
            (fun y : OSPreHilbertSpace OS =>
              ((y : OSPreHilbertSpace OS) : OSHilbertSpace OS)) :=
        (UniformSpace.Completion.toComplL : OSPreHilbertSpace OS →L[ℂ] OSHilbertSpace OS).continuous
      exact htoCompl.comp_continuousOn
        (continuousOn_osTimeShiftLinear_of_isCompactSupport (d := d) OS F hF_compact)
  refine hcoe.congr ?_
  intro t ht
  have ht_pos : 0 < t := ht
  simp [x0, ht_pos, osTimeShiftHilbert_coe]

private theorem denseRange_posRatCast :
    DenseRange (fun q : {q : ℚ // 0 < (q : ℝ)} =>
      (⟨(q : ℝ), q.2⟩ : {r : ℝ // 0 < r})) := by
  intro x
  rcases x with ⟨x, hx⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU
  rw [isOpen_induced_iff] at hV_open
  obtain ⟨W, hW_open, hW_eq⟩ := hV_open
  have hxW : x ∈ W := by
    rw [← hW_eq] at hxV
    exact hxV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW_open x hxW
  have hlb_lt : max (x / 2) (x - ε) < x + ε := max_lt (by linarith) (by linarith)
  obtain ⟨q, hq_lb, hq_ub⟩ := exists_rat_btwn hlb_lt
  have hq_pos : (0 : ℝ) < q := lt_trans (lt_max_of_lt_left (by linarith)) hq_lb
  refine ⟨⟨q, hq_pos⟩, ?_, ⟨⟨q, hq_pos⟩, rfl⟩⟩
  apply hVU
  rw [← hW_eq]
  exact hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right (x / 2) (x - ε)])

private theorem pos_rat_as_nat_frac (q : ℚ) (hq : 0 < (q : ℝ)) :
    ∃ (p d : ℕ) (hp : 0 < p) (hd : 0 < d), (q : ℝ) = (↑p : ℝ) / (↑d : ℝ) := by
  have hq_pos : 0 < q := by exact_mod_cast hq
  have hnum : 0 < q.num := Rat.num_pos.mpr hq_pos
  refine ⟨q.num.toNat, q.den, ?_, q.den_pos, ?_⟩
  · omega
  · have h1 : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
    have h2 : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      rw [Rat.cast_def]
    rw [h2]
    congr 1
    exact_mod_cast h1.symm

private theorem osTimeShiftHilbert_eq_nnrpow_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    osTimeShiftHilbert (d := d) OS lgc t ht
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS) ) =
    CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) (Real.toNNReal t)
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) := by
  let x0 : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
  let x : OSHilbertSpace OS := (x0 : OSHilbertSpace OS)
  let g : {r : ℝ // 0 < r} → OSHilbertSpace OS := fun s =>
    osTimeShiftHilbert (d := d) OS lgc s.1 s.2 x
  let h : {r : ℝ // 0 < r} → OSHilbertSpace OS := fun s =>
    CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) (Real.toNNReal s.1) x
  have hg0 :
      ContinuousOn
        (fun t : ℝ =>
          if ht : 0 < t then
            osTimeShiftHilbert (d := d) OS lgc t ht x
          else
            x)
        (Set.Ioi 0) :=
    continuousOn_osTimeShiftHilbert_of_isCompactSupport (d := d) OS lgc F hF_compact
  have hg : Continuous g := by
    rw [continuousOn_iff_continuous_restrict] at hg0
    have hg1 : Continuous (fun s : {r : ℝ // 0 < r} =>
      if ht : 0 < (s : ℝ) then
        osTimeShiftHilbert (d := d) OS lgc (s : ℝ) ht x
      else
        x) := by
          simpa using hg0
    have hEqg :
        (fun s : {r : ℝ // 0 < r} =>
          if ht : 0 < (s : ℝ) then
            osTimeShiftHilbert (d := d) OS lgc (s : ℝ) ht x
          else
            x) = g := by
      funext s
      have hs : 0 < (s : ℝ) := s.2
      simp [g, hs]
    simpa [hEqg] using hg1
  have hh0 :
      ContinuousOn
        (fun t : ℝ =>
          CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) (Real.toNNReal t) x)
        (Set.Ioi 0) := by
    exact (ContinuousLinearMap.apply ℂ (OSHilbertSpace OS) x).continuous.comp_continuousOn
      (ContinuousLinearMap.continuousOn_nnrpow_posReal
        (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos))
  have hh : Continuous h := by
    rw [continuousOn_iff_continuous_restrict] at hh0
    change Continuous (fun s : {r : ℝ // 0 < r} =>
      CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) (Real.toNNReal (s : ℝ)) x) at hh0
    simpa [h] using hh0
  let fQ : {q : ℚ // 0 < (q : ℝ)} → {r : ℝ // 0 < r} := fun q =>
    ⟨(q : ℝ), q.2⟩
  have hcomp : g ∘ fQ = h ∘ fQ := by
    funext q
    rcases pos_rat_as_nat_frac q.1 q.2 with ⟨p, m, hp, hm, hq_eq⟩
    have hrat_pos : 0 < (p : ℝ) * (m : ℝ)⁻¹ := by
      exact mul_pos (show (0 : ℝ) < p by exact_mod_cast hp)
        (inv_pos.mpr (show (0 : ℝ) < m by exact_mod_cast hm))
    have hratio_eq : (q : ℝ) = (p : ℝ) * (m : ℝ)⁻¹ := by
      simpa [div_eq_mul_inv] using hq_eq
    have hsub :
        fQ q =
          ⟨(p : ℝ) * (m : ℝ)⁻¹,
            hrat_pos⟩ :=
      Subtype.ext hratio_eq
    calc
      g (fQ q) =
          g ⟨(p : ℝ) * (m : ℝ)⁻¹,
            hrat_pos⟩ := by
              exact congrArg g hsub
      _ =
          h ⟨(p : ℝ) * (m : ℝ)⁻¹,
            hrat_pos⟩ := by
              simpa [g, h, x, Real.toNNReal_of_nonneg (le_of_lt hrat_pos),
                div_eq_mul_inv] using
                congrArg (fun L => L x)
                  (osTimeShiftHilbert_rational_eq_nnrpow (d := d) OS lgc p m hp hm)
      _ = h (fQ q) := by
              exact (congrArg h hsub).symm
  have hall : g = h :=
    DenseRange.equalizer (f := fQ) denseRange_posRatCast hg hh hcomp
  exact congrFun hall ⟨t, ht⟩

private def osTimeShiftHilbertSpectralMeasureDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    MeasureTheory.Measure
      (spectrum ℝ (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)) :=
  ContinuousLinearMap.selfAdjointSpectralMeasureDiagonal
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    x

private theorem re_inner_nnrpow_osTimeShiftHilbert_eq_integral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) (t : ℝ) (ht : 0 < t) :
    Complex.re
      (@inner ℂ (OSHilbertSpace OS) _ x
        ((CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (Real.toNNReal t)) x)) =
      ∫ y, (y : ℝ) ^ t ∂(osTimeShiftHilbertSpectralMeasureDiagonal (d := d) OS lgc x) := by
  simpa [osTimeShiftHilbertSpectralMeasureDiagonal, Real.toNNReal_of_nonneg ht.le] using
    (ContinuousLinearMap.re_inner_nnrpow_eq_integral_selfAdjointSpectralMeasureDiagonal
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (x := x)
      (t := Real.toNNReal t)
      (by simpa using ht))

private def osTimeShiftHilbertSpectralMeasureDiagonalReal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) : MeasureTheory.Measure ℝ :=
  ContinuousLinearMap.selfAdjointSpectralMeasureDiagonalReal
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    x

private def osTimeShiftHilbertLaplaceMeasureDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) : MeasureTheory.Measure ℝ :=
  BochnerLaplaceBridge.laplaceMeasurePos
    (osTimeShiftHilbertSpectralMeasureDiagonalReal (d := d) OS lgc x)

private def osTimeShiftHilbertLaplaceValueDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) (t : ℝ) : ℂ :=
  (((∫ u, Real.exp (-t * u) ∂
      osTimeShiftHilbertLaplaceMeasureDiagonal (d := d) OS lgc x) : ℝ) : ℂ)

private def osTimeShiftHilbertLaplaceValueOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) (t : ℝ) : ℂ :=
  (1 / 4 : ℂ) *
    (osTimeShiftHilbertLaplaceValueDiagonal (d := d) OS lgc (x + y) t -
      osTimeShiftHilbertLaplaceValueDiagonal (d := d) OS lgc (x - y) t -
      Complex.I * osTimeShiftHilbertLaplaceValueDiagonal (d := d) OS lgc
        (x + Complex.I • y) t +
      Complex.I * osTimeShiftHilbertLaplaceValueDiagonal (d := d) OS lgc
        (x - Complex.I • y) t)

private theorem osTimeShiftHilbertLaplaceMeasureDiagonal_nonnegSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    osTimeShiftHilbertLaplaceMeasureDiagonal (d := d) OS lgc x (Set.Iio 0) = 0 := by
  haveI : MeasureTheory.IsFiniteMeasure
      (osTimeShiftHilbertSpectralMeasureDiagonalReal (d := d) OS lgc x) := by
    unfold osTimeShiftHilbertSpectralMeasureDiagonalReal
    infer_instance
  unfold osTimeShiftHilbertLaplaceMeasureDiagonal
  exact BochnerLaplaceBridge.laplaceMeasurePos_nonnegSupport
    (μ := osTimeShiftHilbertSpectralMeasureDiagonalReal (d := d) OS lgc x)
    (hsupp_le_one :=
      ContinuousLinearMap.selfAdjointSpectralMeasureDiagonalReal_Ioi_eq_zero_of_spectrum_subset_Icc
        (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (x := x)
        (spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos))

private theorem inner_osTimeShiftHilbert_eq_laplace_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      ((osTimeShiftHilbert (d := d) OS lgc t ht)
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))) =
      osTimeShiftHilbertLaplaceValueDiagonal (d := d) OS lgc
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) t := by
  rw [osTimeShiftHilbert_eq_nnrpow_of_isCompactSupport (d := d) OS lgc F hF_compact t ht]
  simpa [osTimeShiftHilbertLaplaceValueDiagonal, osTimeShiftHilbertLaplaceMeasureDiagonal,
    osTimeShiftHilbertSpectralMeasureDiagonalReal, Real.toNNReal_of_nonneg ht.le,
    mul_comm, mul_left_comm, mul_assoc] using
    (ContinuousLinearMap.inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (x := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (t := Real.toNNReal t)
      (by simpa using ht))

private theorem inner_osTimeShiftHilbert_offdiag_eq_laplace_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (F : PositiveTimeBorchersSequence d)
    (y : OSHilbertSpace OS)
    (hy : y = (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    @inner ℂ (OSHilbertSpace OS) _
      x
      ((osTimeShiftHilbert (d := d) OS lgc t ht) y) =
      osTimeShiftHilbertLaplaceValueOffdiag (d := d) OS lgc x y t := by
  subst y
  rw [osTimeShiftHilbert_eq_nnrpow_of_isCompactSupport (d := d) OS lgc F hF_compact t ht]
  simpa [osTimeShiftHilbertLaplaceValueOffdiag, osTimeShiftHilbertLaplaceValueDiagonal,
    osTimeShiftHilbertLaplaceMeasureDiagonal,
    osTimeShiftHilbertSpectralMeasureDiagonalReal, Real.toNNReal_of_nonneg ht.le,
    mul_comm, mul_left_comm, mul_assoc] using
    (ContinuousLinearMap.inner_nnrpow_eq_laplace_polarization
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x)
      (y := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
      (t := Real.toNNReal t)
      (by simpa using ht))

def osTimeShiftHilbertComplex
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (z : ℂ) : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  ContinuousLinearMap.spectralSemigroupComplex
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
    (spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
    z

theorem osTimeShiftHilbertComplex_inner_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) (z : ℂ) (hz : 0 < z.re) :
    @inner ℂ (OSHilbertSpace OS) _ x
      (osTimeShiftHilbertComplex (d := d) OS lgc z y) =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        x y z := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_inner_eq
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x) (y := y) (z := z) hz)

theorem differentiableOn_inner_osTimeShiftHilbertComplex
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) :
    DifferentiableOn ℂ
      (fun z => @inner ℂ (OSHilbertSpace OS) _ x
        (osTimeShiftHilbertComplex (d := d) OS lgc z y))
      {z : ℂ | 0 < z.re} := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_differentiableOn
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x) (y := y))

theorem continuousOn_osTimeShiftHilbertComplex
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ContinuousOn (fun z => osTimeShiftHilbertComplex (d := d) OS lgc z)
      {z : ℂ | 0 < z.re} := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_continuousOn
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos))

theorem continuousOn_osTimeShiftHilbertComplex_apply
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (y : OSHilbertSpace OS) :
    ContinuousOn (fun z => osTimeShiftHilbertComplex (d := d) OS lgc z y)
      {z : ℂ | 0 < z.re} := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_strongContinuousOn
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (y := y))

theorem continuousOn_osTimeShiftHilbertComplex_jointly
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ContinuousOn
      (fun p : ℂ × OSHilbertSpace OS =>
        osTimeShiftHilbertComplex (d := d) OS lgc p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_jointlyContinuousOn
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos))

theorem osTimeShiftHilbertComplex_norm_le
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (z : ℂ) (hz : 0 < z.re) :
    ‖osTimeShiftHilbertComplex (d := d) OS lgc z‖ ≤ 2 := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_norm_le
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (z := z) hz)

theorem osTimeShiftHilbertComplex_ofReal_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ) =
      CFC.nnrpow (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) (Real.toNNReal t) := by
  simpa [osTimeShiftHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_ofReal_eq_nnrpow
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (t := t) ht)

theorem osTimeShiftHilbertComplex_ofReal_eq_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) =
      (osTimeShiftHilbert (d := d) OS lgc t ht)
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) := by
  rw [osTimeShiftHilbertComplex_ofReal_eq_nnrpow (d := d) OS lgc t ht,
    osTimeShiftHilbert_eq_nnrpow_of_isCompactSupport (d := d) OS lgc F hF_compact t ht]

/-- The diagonal one-variable holomorphic extension of the OS time-shift matrix element. -/
private def osTimeShiftHilbertHolomorphicValueDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) (z : ℂ) : ℂ :=
  ContinuousLinearMap.selfAdjointSpectralLaplaceDiagonal
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    x z

/-- The polarized one-variable holomorphic extension of the OS time-shift matrix element. -/
private def osTimeShiftHilbertHolomorphicValueOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) (z : ℂ) : ℂ :=
  ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    x y z

private theorem osTimeShiftHilbertComplex_inner_eq_holomorphicValueOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) (z : ℂ) (hz : 0 < z.re) :
    @inner ℂ (OSHilbertSpace OS) _ x
      (osTimeShiftHilbertComplex (d := d) OS lgc z y) =
      osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc x y z := by
  simpa [osTimeShiftHilbertHolomorphicValueOffdiag] using
    osTimeShiftHilbertComplex_inner_eq (d := d) OS lgc x y z hz

private theorem differentiableOn_osTimeShiftHilbertHolomorphicValueDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    DifferentiableOn ℂ (osTimeShiftHilbertHolomorphicValueDiagonal (d := d) OS lgc x)
      {z : ℂ | 0 < z.re} := by
  simpa [osTimeShiftHilbertHolomorphicValueDiagonal] using
    (ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceDiagonal
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x))

private theorem differentiableOn_osTimeShiftHilbertHolomorphicValueOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) :
    DifferentiableOn ℂ (osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc x y)
      {z : ℂ | 0 < z.re} := by
  simpa [osTimeShiftHilbertHolomorphicValueOffdiag] using
    (ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceOffdiag
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x) (y := y))

private theorem continuousOn_osTimeShiftHilbertHolomorphicValueDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    ContinuousOn (osTimeShiftHilbertHolomorphicValueDiagonal (d := d) OS lgc x)
      {z : ℂ | 0 < z.re} :=
  (differentiableOn_osTimeShiftHilbertHolomorphicValueDiagonal
    (d := d) OS lgc x).continuousOn

private theorem continuousOn_osTimeShiftHilbertHolomorphicValueOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) :
    ContinuousOn (osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc x y)
      {z : ℂ | 0 < z.re} :=
  (differentiableOn_osTimeShiftHilbertHolomorphicValueOffdiag
    (d := d) OS lgc x y).continuousOn

private theorem osTimeShiftHilbertHolomorphicValueDiagonal_ofReal_eq_inner_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    osTimeShiftHilbertHolomorphicValueDiagonal (d := d) OS lgc
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        (t : ℂ) =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        ((osTimeShiftHilbert (d := d) OS lgc t ht)
          (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))) := by
  rw [osTimeShiftHilbert_eq_nnrpow_of_isCompactSupport (d := d) OS lgc F hF_compact t ht]
  simpa [osTimeShiftHilbertHolomorphicValueDiagonal, Real.toNNReal_of_nonneg ht.le] using
    (ContinuousLinearMap.selfAdjointSpectralLaplaceDiagonal_ofReal_eq_inner_nnrpow
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (x := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (t := t) ht)

private theorem osTimeShiftHilbertHolomorphicValueOffdiag_ofReal_eq_inner_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (F : PositiveTimeBorchersSequence d)
    (y : OSHilbertSpace OS)
    (hy : y = (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
    (hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc x y (t : ℂ) =
      @inner ℂ (OSHilbertSpace OS) _
        x
        ((osTimeShiftHilbert (d := d) OS lgc t ht) y) := by
  subst y
  rw [osTimeShiftHilbert_eq_nnrpow_of_isCompactSupport (d := d) OS lgc F hF_compact t ht]
  simpa [osTimeShiftHilbertHolomorphicValueOffdiag, Real.toNNReal_of_nonneg ht.le] using
    (ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag_ofReal_eq_inner_nnrpow
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hA_nonneg := osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x)
      (y := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
      (t := t) ht)

/-- Raw OS pairing version of the one-variable holomorphic extension for Euclidean time shift. -/
def OSInnerProductTimeShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (z : ℂ) : ℂ :=
  osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc
    (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
    (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) z

private theorem OSInnerProductTimeShiftHolomorphicValue_eq_inner_osTimeShiftHilbertComplex
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (z : ℂ) (hz : 0 < z.re) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G z =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        ((osTimeShiftHilbertComplex (d := d) OS lgc z)
          (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))) := by
  symm
  exact osTimeShiftHilbertComplex_inner_eq_holomorphicValueOffdiag
    (d := d) OS lgc
    (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
    (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
    z hz

/-- The one-variable OS time-shift holomorphic matrix element is exactly the
off-diagonal spectral Laplace transform of the self-adjoint contraction
`osTimeShiftHilbert ... 1` on the OS Hilbert space. This is the semigroup-side
spectral object behind the later two-point polarized Laplace criteria. -/
theorem OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (z : ℂ) (hz : 0 < z.re) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G z =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
        z := by
  rw [OSInnerProductTimeShiftHolomorphicValue_eq_inner_osTimeShiftHilbertComplex
    (d := d) OS lgc F G z hz]
  exact osTimeShiftHilbertComplex_inner_eq
    (d := d) OS lgc
    (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
    (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
    z hz

private theorem differentiableOn_OSInnerProductTimeShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G)
      {z : ℂ | 0 < z.re} := by
  simpa [OSInnerProductTimeShiftHolomorphicValue] using
    differentiableOn_osTimeShiftHilbertHolomorphicValueOffdiag
      (d := d) OS lgc
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))

/-- The semigroup matrix element is holomorphic on the right half-plane. This
is the one-variable OS input used when Wick-rotating into the two-point flat
tube witness. -/
theorem OSInnerProductTimeShiftHolomorphicValue_differentiableOn
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G)
      {z : ℂ | 0 < z.re} :=
  differentiableOn_OSInnerProductTimeShiftHolomorphicValue
    (d := d) OS lgc F G

private theorem continuousOn_OSInnerProductTimeShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    ContinuousOn (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G)
      {z : ℂ | 0 < z.re} := by
  simpa [OSInnerProductTimeShiftHolomorphicValue] using
    continuousOn_osTimeShiftHilbertHolomorphicValueOffdiag
      (d := d) OS lgc
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))

private theorem OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) t (G : BorchersSequence d)) := by
  rw [OSInnerProductTimeShiftHolomorphicValue]
  rw [osTimeShiftHilbertHolomorphicValueOffdiag_ofReal_eq_inner_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (x := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))
      (F := G)
      (y := (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)))
      (hy := rfl)
      (hF_compact := hG_compact)
      (t := t) ht]
  rw [osTimeShiftHilbert_coe (d := d) (OS := OS) (lgc := lgc) (t := t) (ht := ht)
      (x := (⟦G⟧ : OSPreHilbertSpace OS))]
  rw [UniformSpace.Completion.inner_coe]
  simp [osTimeShiftLinear, osTimeShift, PositiveTimeBorchersSequence.osInner,
    timeShiftPositiveTimeBorchers]

/-- Real Euclidean time shift of a concentrated OS tensor term. -/
private theorem OSInnerProduct_single_right_timeShift
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ) :
    OSInnerProduct d OS.S (BorchersSequence.single n f)
        (timeShiftBorchers (d := d) t (BorchersSequence.single m g)) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  have hshift_single :
      ∀ k,
        (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
          (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
    intro k
    by_cases hk : k = m
    · subst hk
      simp [BorchersSequence.single]
    · simp [BorchersSequence.single, hk]
  rw [OSInnerProduct_congr_right d OS.S OS.E0_linear
      (BorchersSequence.single n f)
      (timeShiftBorchers (d := d) t (BorchersSequence.single m g))
      (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g))
      hshift_single]
  simpa using
    (OSInnerProduct_single_single d OS.S OS.E0_linear n m f
      (timeShiftSchwartzNPoint (d := d) t g))

/-- Concentrated inserted-right-factor shell with a time-shifted tail, under the honest
ordered-support barrier hypotheses needed for the direct OS operator route. The result is
rewritten on an explicit zero-diagonal witness rather than `ofClassical`. -/
theorem osInner_single_fieldActionTimeShift_single_of_head_barrier
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (h : SchwartzSpacetime d) (t : ℝ)
    (hf_pos : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hh_barrier : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t})
    (hg_pos : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    PositiveTimeBorchersSequence.osInner OS
      (PositiveTimeBorchersSequence.single n f hf_pos)
      (fieldActionTimeShiftPositiveTimeBorchers (d := d) h t hh_barrier
        (PositiveTimeBorchersSequence.single m g hg_pos)) =
      OS.S (n + (m + 1))
        ⟨f.osConjTensorProduct (SchwartzMap.prependField h (timeShiftSchwartzNPoint (d := d) t g)),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
            (d := d) (n := n) (m := m + 1) (f := f)
            (g := SchwartzMap.prependField h (timeShiftSchwartzNPoint (d := d) t g))
            hf_pos
            (prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
              (d := d) (n := m) t h g hh_barrier hg_pos)⟩ := by
  let g' : SchwartzNPoint d m := timeShiftSchwartzNPoint (d := d) t g
  have hzero :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (SchwartzMap.prependField h g')) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := n) (m := m + 1) (f := f)
      (g := SchwartzMap.prependField h g') hf_pos
      (prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
        (d := d) (n := m) t h g hh_barrier hg_pos)
  have hshift_single :
      ∀ k,
        (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
          (BorchersSequence.single m g').funcs k := by
    intro k
    by_cases hk : k = m
    · subst hk
      simp [BorchersSequence.single, g', timeShiftBorchers_funcs]
    · simp [BorchersSequence.single, hk, g', timeShiftBorchers_funcs]
  have hfield_congr :
      OSInnerProduct d OS.S (BorchersSequence.single n f)
        (Reconstruction.fieldOperatorAction h
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g))) =
      OSInnerProduct d OS.S (BorchersSequence.single n f)
        (Reconstruction.fieldOperatorAction h (BorchersSequence.single m g')) := by
    refine OSInnerProduct_congr_right d OS.S OS.E0_linear
      (BorchersSequence.single n f)
      (Reconstruction.fieldOperatorAction h
        (timeShiftBorchers (d := d) t (BorchersSequence.single m g)))
      (Reconstruction.fieldOperatorAction h (BorchersSequence.single m g')) ?_
    intro k
    cases k with
    | zero =>
        simp [Reconstruction.fieldOperatorAction_funcs_zero]
    | succ k =>
        simpa [Reconstruction.fieldOperatorAction_funcs_succ] using
          congrArg (SchwartzMap.prependField h) (hshift_single k)
  have hmain :
      OSInnerProduct d OS.S (BorchersSequence.single n f)
        (Reconstruction.fieldOperatorAction h (BorchersSequence.single m g')) =
      OS.S (n + (m + 1))
        ⟨f.osConjTensorProduct (SchwartzMap.prependField h g'), hzero⟩ := by
    exact (OSInnerProduct_single_fieldOperatorAction_single
      (d := d) OS.S OS.E0_linear n m f g' h).trans
      (by rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := f.osConjTensorProduct (SchwartzMap.prependField h g')) hzero])
  unfold PositiveTimeBorchersSequence.osInner
  simpa [g', fieldActionTimeShiftPositiveTimeBorchers,
    PositiveTimeBorchersSequence.single_toBorchersSequence] using
    hfield_congr.trans hmain

private theorem OSInnerProduct_single_fieldOperatorAction_timeShift_right_of_head_barrier
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : SchwartzNPoint d n) (h : SchwartzSpacetime d) (t : ℝ)
    (hf_pos : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hh_barrier : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t})
    (G : PositiveTimeBorchersSequence d) :
    OSInnerProduct d OS.S (BorchersSequence.single n f)
      (Reconstruction.fieldOperatorAction h
        (timeShiftBorchers (d := d) t (G : BorchersSequence d))) =
      ∑ m ∈ Finset.range (((G : BorchersSequence d).bound + 1)),
        OS.S (n + (m + 1))
          ⟨f.osConjTensorProduct
              (SchwartzMap.prependField h
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
              (d := d) (n := n) (m := m + 1) (f := f)
              (g := SchwartzMap.prependField h
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m)))
              hf_pos
              (prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
                (d := d) (n := m) t h ((G : BorchersSequence d).funcs m)
                hh_barrier (G.ordered_tsupport m))⟩ := by
  unfold OSInnerProduct
  rw [BorchersSequence.single_bound, Finset.sum_range_succ]
  have hleft :
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range
            ((Reconstruction.fieldOperatorAction h
                (timeShiftBorchers (d := d) t (G : BorchersSequence d))).bound + 1),
          OS.S (i + j) (ZeroDiagonalSchwartz.ofClassical
            (((BorchersSequence.single n f).funcs i).osConjTensorProduct
              ((Reconstruction.fieldOperatorAction h
                (timeShiftBorchers (d := d) t (G : BorchersSequence d))).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hi)
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [BorchersSequence.single_funcs_ne hi_ne, SchwartzNPoint.osConjTensorProduct_zero_left,
      ZeroDiagonalSchwartz.ofClassical_zero, (OS.E0_linear _).map_zero]
  rw [hleft, zero_add, BorchersSequence.single_funcs_eq]
  rw [Reconstruction.fieldOperatorAction_bound]
  simp only [timeShiftBorchers]
  rw [Finset.sum_range_succ']
  simp only [Reconstruction.fieldOperatorAction_funcs_zero,
    SchwartzNPoint.osConjTensorProduct_zero_right, ZeroDiagonalSchwartz.ofClassical_zero,
    (OS.E0_linear _).map_zero, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  have hzero :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct
          (SchwartzMap.prependField h
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m)))) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := n) (m := m + 1) (f := f)
      (g := SchwartzMap.prependField h
        (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m)))
      hf_pos
      (prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
        (d := d) (n := m) t h ((G : BorchersSequence d).funcs m)
        hh_barrier (G.ordered_tsupport m))
  rw [Reconstruction.fieldOperatorAction_funcs_succ, timeShiftBorchers_funcs,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f.osConjTensorProduct
        (SchwartzMap.prependField h
          (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))
      hzero]

/-- With a concentrated left factor, barrier-separated shifted field insertion on an
arbitrary positive-time right Borchers vector expands as a finite sum of explicit
zero-diagonal Schwinger terms. This is the honest algebraic shell needed before any
boundedness or quotient-extension argument can begin. -/
theorem osInner_single_fieldActionTimeShift_of_head_barrier
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : SchwartzNPoint d n) (h : SchwartzSpacetime d) (t : ℝ)
    (hf_pos : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hh_barrier : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < t})
    (G : PositiveTimeBorchersSequence d) :
    PositiveTimeBorchersSequence.osInner OS
      (PositiveTimeBorchersSequence.single n f hf_pos)
      (fieldActionTimeShiftPositiveTimeBorchers (d := d) h t hh_barrier G) =
      ∑ m ∈ Finset.range (((G : BorchersSequence d).bound + 1)),
        OS.S (n + (m + 1))
          ⟨f.osConjTensorProduct
              (SchwartzMap.prependField h
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
              (d := d) (n := n) (m := m + 1) (f := f)
              (g := SchwartzMap.prependField h
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m)))
              hf_pos
              (prependField_timeShift_tsupport_subset_orderedPositiveTimeRegion_of_head_barrier
                (d := d) (n := m) t h ((G : BorchersSequence d).funcs m)
                hh_barrier (G.ordered_tsupport m))⟩ := by
  unfold PositiveTimeBorchersSequence.osInner
  simpa [fieldActionTimeShiftPositiveTimeBorchers,
    PositiveTimeBorchersSequence.single_toBorchersSequence] using
    OSInnerProduct_single_fieldOperatorAction_timeShift_right_of_head_barrier
      (d := d) OS f h t hf_pos hh_barrier G

/-- Real Euclidean time shift against a concentrated right factor reduces to a finite
sum over the left Borchers components. -/
private theorem OSInnerProduct_right_single_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (F : BorchersSequence d)
    {m : ℕ} (g : SchwartzNPoint d m) (t : ℝ) :
    OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t (BorchersSequence.single m g)) =
      ∑ n ∈ Finset.range (F.bound + 1),
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((F.funcs n).osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  have hshift_single :
      ∀ k,
        (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
          (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
    intro k
    by_cases hk : k = m
    · subst hk
      simp [BorchersSequence.single]
    · simp [BorchersSequence.single, hk]
  rw [OSInnerProduct_congr_right d OS.S OS.E0_linear F
      (timeShiftBorchers (d := d) t (BorchersSequence.single m g))
      (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g))
      hshift_single]
  unfold OSInnerProduct
  apply Finset.sum_congr rfl
  intro n hn
  rw [BorchersSequence.single_bound, Finset.sum_range_succ]
  have hright :
      ∑ j ∈ Finset.range m,
        OS.S (n + j) (ZeroDiagonalSchwartz.ofClassical
          ((F.funcs n).osConjTensorProduct
            ((BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
    rw [BorchersSequence.single_funcs_ne hj_ne, SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_zero, (OS.E0_linear _).map_zero]
  rw [hright, zero_add, BorchersSequence.single_funcs_eq]

/-- Simple-tensor specialization of the one-variable OS holomorphic bridge. -/
theorem OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (G := PositiveTimeBorchersSequence.single m g hg_ord)
      (hG_compact := by
        intro k
        by_cases hk : k = m
        · subst hk
          simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
        · have hzero :
            ((((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
                BorchersSequence d).funcs k : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) = 0 := by
            simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
              BorchersSequence.single, hk]
          rw [hzero]
          simpa using (HasCompactSupport.zero :
            HasCompactSupport (0 : NPointDomain d k → ℂ)))
      (t := t) ht]
  simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
    (OSInnerProduct_single_right_timeShift (d := d) OS f g t)

private theorem OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n (translateSchwartzNPoint (d := d) a f)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) a ha0 f hf_ord))
        (PositiveTimeBorchersSequence.single m (translateSchwartzNPoint (d := d) a g)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) a ha0 g hg_ord))
        (t : ℂ) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (t : ℂ) := by
  let hf_ord' :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a ha0 f hf_ord
  let hg_ord' :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a ha0 g hg_ord
  let hg_shift_ord :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t ht g hg_ord
  let hg_shift_ord' :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a ha0 (timeShiftSchwartzNPoint (d := d) t g) hg_shift_ord
  have hleft :
      VanishesToInfiniteOrderOnCoincidence
        ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
          (translateSchwartzNPoint (d := d) a (timeShiftSchwartzNPoint (d := d) t g))) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := n) (m := m)
      (f := translateSchwartzNPoint (d := d) a f)
      (g := translateSchwartzNPoint (d := d) a (timeShiftSchwartzNPoint (d := d) t g))
      hf_ord' hg_shift_ord'
  have hright :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := n) (m := m) (f := f)
      (g := timeShiftSchwartzNPoint (d := d) t g) hf_ord hg_shift_ord
  rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
      (d := d) (OS := OS) (lgc := lgc)
      (f := translateSchwartzNPoint (d := d) a f) (hf_ord := hf_ord')
      (g := translateSchwartzNPoint (d := d) a g) (hg_ord := hg_ord')
      (hg_compact := by
        simpa [translateSchwartzNPoint_apply] using
          hg_compact.comp_homeomorph
            (translateNPointDomainHomeomorph (d := d) (n := m) a))
      (t := t) ht,
    OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
      (d := d) (OS := OS) (lgc := lgc)
      (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) (t := t) ht,
    ← translateSchwartzNPoint_timeShiftSchwartzNPoint
      (d := d) (n := m) (a := a) (t := t) (f := g)]
  exact schwinger_translate_tensor_eq_of_spatial
    (d := d) OS a ha0 f (timeShiftSchwartzNPoint (d := d) t g) hleft hright

theorem OSInnerProductTimeShiftHolomorphicValue_single_translate_spatial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (z : ℂ) (hz : 0 < z.re) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n (translateSchwartzNPoint (d := d) a f)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) a ha0 f hf_ord))
        (PositiveTimeBorchersSequence.single m (translateSchwartzNPoint (d := d) a g)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) a ha0 g hg_ord))
        z =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        z := by
  let F₀ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n (translateSchwartzNPoint (d := d) a f)
      (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a ha0 f hf_ord)
  let G₀ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single m (translateSchwartzNPoint (d := d) a g)
      (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a ha0 g hg_ord)
  let F₁ : PositiveTimeBorchersSequence d := PositiveTimeBorchersSequence.single n f hf_ord
  let G₁ : PositiveTimeBorchersSequence d := PositiveTimeBorchersSequence.single m g hg_ord
  let H₀ : ℂ → ℂ := OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F₀ G₀
  let H₁ : ℂ → ℂ := OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F₁ G₁
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have hH₀_holo : DifferentiableOn ℂ H₀ U := by
    simpa [H₀, U, F₀, G₀] using
      differentiableOn_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc F₀ G₀
  have hH₁_holo : DifferentiableOn ℂ H₁ U := by
    simpa [H₁, U, F₁, G₁] using
      differentiableOn_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc F₁ G₁
  have h_freq : ∃ᶠ w in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ w = H₁ w := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hEq
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hEq
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      dsimp [H₀, H₁, F₀, G₀, F₁, G₁]
      exact OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial
        (d := d) (OS := OS) (lgc := lgc) a ha0 f hf_ord g hg_ord hg_compact (1 + ε) hpos
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  have hEq : Set.EqOn H₀ H₁ U := by
    exact identity_theorem_connected hU_open hU_conn H₀ H₁ hH₀_holo hH₁_holo
      (1 : ℂ) (by simp [U]) h_freq
  exact hEq hz

/-- One-variable holomorphic OS time-shift with a concentrated right factor. On positive
real points it recovers the explicit finite sum over the left Borchers components. -/
theorem OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    {m : ℕ}
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g)))) := by
  rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (F := F)
      (G := PositiveTimeBorchersSequence.single m g hg_ord)
      (hG_compact := by
        intro k
        by_cases hk : k = m
        · subst hk
          simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
        · have hzero :
            ((((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
                BorchersSequence d).funcs k : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) = 0 := by
            simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
              BorchersSequence.single, hk]
          rw [hzero]
          simpa using (HasCompactSupport.zero :
            HasCompactSupport (0 : NPointDomain d k → ℂ)))
      (t := t) ht]
  simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
    (OSInnerProduct_right_single_timeShift (d := d) (OS := OS)
      (F := (F : BorchersSequence d)) (g := g) (t := t))

/-- Finite-sum holomorphic expansion obtained by decomposing the right Borchers sequence
into its concentrated components. -/
private def OSInnerProductTimeShiftHolomorphicValueExpandRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) : ℂ → ℂ :=
  ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F
      (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
        (G.ordered_tsupport m))

private theorem differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ (OSInnerProductTimeShiftHolomorphicValueExpandRight
      (d := d) OS lgc F G) {z : ℂ | 0 < z.re} := by
  classical
  unfold OSInnerProductTimeShiftHolomorphicValueExpandRight
  exact DifferentiableOn.sum (u := Finset.range (((G : BorchersSequence d).bound) + 1))
    (A := fun m =>
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F
        (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m)))
    (s := {z : ℂ | 0 < z.re}) (fun m hm =>
      differentiableOn_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc F
        (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m)))

private theorem continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    ContinuousOn (OSInnerProductTimeShiftHolomorphicValueExpandRight
      (d := d) OS lgc F G) {z : ℂ | 0 < z.re} :=
  (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandRight
    (d := d) OS lgc F G).continuousOn

private theorem OSInnerProductTimeShiftHolomorphicValueExpandRight_ofReal_eq_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandRight (d := d) OS lgc F G (t : ℂ) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) t (G : BorchersSequence d)) := by
  classical
  rw [OSInnerProduct]
  rw [Finset.sum_comm]
  unfold OSInnerProductTimeShiftHolomorphicValueExpandRight
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
    (d := d) (OS := OS) (lgc := lgc) (F := F)
    (g := ((G : BorchersSequence d).funcs m))
    (hg_ord := G.ordered_tsupport m)
    (hg_compact := hG_compact m)
    (t := t) ht]

/-- Finite double-sum holomorphic expansion obtained by decomposing both Borchers
sequences into concentrated components. -/
def OSInnerProductTimeShiftHolomorphicValueExpandBoth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) : ℂ → ℂ :=
  ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
    ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))

theorem differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ (OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G) {z : ℂ | 0 < z.re} := by
  classical
  unfold OSInnerProductTimeShiftHolomorphicValueExpandBoth
  refine DifferentiableOn.sum
      (u := Finset.range (((F : BorchersSequence d).bound) + 1))
      (A := fun n =>
        ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n))
            (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
              (G.ordered_tsupport m)))
      (s := {z : ℂ | 0 < z.re}) ?_
  intro n hn
  refine DifferentiableOn.sum
      (u := Finset.range (((G : BorchersSequence d).bound) + 1))
      (A := fun m =>
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m)))
      (s := {z : ℂ | 0 < z.re}) ?_
  intro m hm
  exact differentiableOn_OSInnerProductTimeShiftHolomorphicValue
    (d := d) OS lgc
    (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
      (F.ordered_tsupport n))
    (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
      (G.ordered_tsupport m))

theorem continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    ContinuousOn (OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G) {z : ℂ | 0 < z.re} :=
  (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
    (d := d) OS lgc F G).continuousOn

theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G (t : ℂ) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) t (G : BorchersSequence d)) := by
  classical
  rw [OSInnerProduct]
  unfold OSInnerProductTimeShiftHolomorphicValueExpandBoth
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm
  simpa [timeShiftBorchers_funcs] using
    (OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
      (d := d) (OS := OS) (lgc := lgc)
      (f := ((F : BorchersSequence d).funcs n))
      (hf_ord := F.ordered_tsupport n)
      (g := ((G : BorchersSequence d).funcs m))
      (hg_ord := G.ordered_tsupport m)
      (hg_compact := hG_compact m)
      (t := t) ht)

private theorem inner_osTimeShiftLinear_isSemigroupPDKernel_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d)
    (_hF_compact : ∀ n,
      HasCompactSupport (((
        F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    SCV.IsSemigroupPDKernel
      (fun t : ℝ =>
        if ht : 0 < t then
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS)
            ((osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS))
        else
          @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            (⟦F⟧ : OSPreHilbertSpace OS) (⟦F⟧ : OSPreHilbertSpace OS)) := by
  intro ι _ _ c τ
  have hτpos : ∀ i j : ι, 0 < ((τ i : ℝ) + (τ j : ℝ)) := by
    intro i j
    exact add_pos (τ i).2 (τ j).2
  simpa [SCV.IsSemigroupPDKernel, hτpos] using
    (osTimeShiftLinear_kernel_real_nonneg (d := d) (OS := OS)
      (s := Finset.univ) (c := c) (τ := τ) (x := (⟦F⟧ : OSPreHilbertSpace OS)))

end
