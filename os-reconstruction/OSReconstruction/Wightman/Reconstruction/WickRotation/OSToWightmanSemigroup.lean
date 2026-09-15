/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.SchwartzNPointFlatten
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanE0FiniteSeminorm
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesSCV
import OSReconstruction.SCV.DistributionalUniqueness
import Init
import OSReconstruction.SCV.LaplaceHolomorphic
import OSReconstruction.SCV.MultipleReflection
import OSReconstruction.vNA.Bochner.SemigroupRoots
import OSReconstruction.vNA.Spectral.ComplexSemigroup
import OSReconstruction.vNA.Spectral.SelfAdjointFunctionalViaRMK
import OSReconstruction.vNA.Unbounded.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder






















open scoped Classical NNReal
open BigOperators Finset

set_option backward.isDefEq.respectTransparency false

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]


/-- Phase 2: The Euclidean time translation semigroup.

    For t > 0, define the operator T(t) on the Hilbert space by:
      T(t) [f](τ₁,...,τₙ) = [f(τ₁ + t,..., τₙ + t)]

    On the honest Euclidean quotient `OSPreHilbertSpace OS`, this gives a
    target contraction semigroup with:
    - T(s)T(t) = T(s+t)
    - ‖T(t)‖ ≤ 1 (the extra positivity/contractivity input needed to force
      nonnegative spectral support)
    - T(t) → I as t → 0⁺ (strong continuity, from E0)

    For the concrete OS time shift below, the half-shift identity proves
    positivity of the bounded Hilbert operator `osTimeShiftHilbert`, and
    Mathlib's complex polarization criterion then gives self-adjointness.  The
    bare `EuclideanSemigroup` record is only a contraction/kernel package; it is
    not used by itself as a generic self-adjointness API.

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
  simpa [one_mul, dist_eq_norm] using le_of_eq (congrArg norm hsub)

omit [NeZero d] in
private theorem translateNPointDomain_hasTemperateGrowth (a : SpacetimeDim d) {n : ℕ} :
    Function.HasTemperateGrowth (translateNPointDomain (d := d) (n := n) a) := by
  let c : NPointDomain d n := fun _ => -a
  have hconst : Function.HasTemperateGrowth (fun _ : NPointDomain d n => c) :=
    Function.HasTemperateGrowth.const c
  have hid : Function.HasTemperateGrowth (fun x : NPointDomain d n => x) := by
    change Function.HasTemperateGrowth (id : NPointDomain d n → NPointDomain d n)
    exact (ContinuousLinearMap.id ℝ (NPointDomain d n)).hasTemperateGrowth
  change Function.HasTemperateGrowth ((fun x : NPointDomain d n => x) + fun _ => c)
  exact hid.add hconst

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
    change iteratedFDeriv ℝ l (fun z => f.toFun (z + a)) x = _
    exact iteratedFDeriv_comp_add_right (f := f.toFun) l a x
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by
        congr 1
        ext i μ
        simp [a]
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  have hC0 : ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ ≤ SchwartzMap.seminorm ℝ 0 l f := by
    change ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ ≤ _
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

/-- Every Schwartz seminorm of a reflected translated OS test kernel grows
polynomially with degree equal to its weight index. -/
private theorem exists_seminorm_osConjTensorProduct_timeShift_le_polynomial
    (p l : ℕ) {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ p l
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) ≤
        C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
  let A0 : ℕ → ℝ := fun i => 2 * SchwartzMap.seminorm ℝ 0 (l - i) g
  let Ap : ℕ → ℝ := fun i =>
    2 ^ (p - 1) *
      (SchwartzMap.seminorm ℝ p (l - i) g + SchwartzMap.seminorm ℝ 0 (l - i) g)
  let C : ℝ :=
    2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℝ p i f * A0 i + SchwartzMap.seminorm ℝ 0 i f * Ap i)
  refine ⟨C, by positivity, ?_⟩
  intro t
  let ρ : ℝ := ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖
  have hρ_nonneg : 0 ≤ ρ := norm_nonneg _
  have hpow_one : 1 ≤ (1 + ρ) ^ p := by
    exact one_le_pow₀ (by linarith)
  have hpow_ρ : ρ ^ p ≤ (1 + ρ) ^ p := by
    exact pow_le_pow_left₀ hρ_nonneg (by linarith) p
  have hshift0 :
      ∀ i ∈ Finset.range (l + 1),
        SchwartzMap.seminorm ℝ 0 (l - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          A0 i * (1 + ρ) ^ p := by
    intro i hi
    have hbase :
        SchwartzMap.seminorm ℝ 0 (l - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          2 * SchwartzMap.seminorm ℝ 0 (l - i) g := by
      simpa [two_mul, ρ, A0] using seminorm_timeShiftSchwartzNPoint_le
        (d := d) 0 (l - i) t g
    have hA0_nonneg : 0 ≤ A0 i := by
      dsimp [A0]
      positivity
    calc
      SchwartzMap.seminorm ℝ 0 (l - i) (timeShiftSchwartzNPoint (d := d) t g)
        ≤ A0 i := by simpa [A0] using hbase
      _ ≤ A0 i * (1 + ρ) ^ p := by
        simpa [one_mul] using mul_le_mul_of_nonneg_left hpow_one hA0_nonneg
  have hshiftP :
      ∀ i ∈ Finset.range (l + 1),
        SchwartzMap.seminorm ℝ p (l - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          Ap i * (1 + ρ) ^ p := by
    intro i hi
    have hbase :
        SchwartzMap.seminorm ℝ p (l - i) (timeShiftSchwartzNPoint (d := d) t g) ≤
          2 ^ (p - 1) *
            (SchwartzMap.seminorm ℝ p (l - i) g +
              ρ ^ p * SchwartzMap.seminorm ℝ 0 (l - i) g) := by
      simpa [ρ] using seminorm_timeShiftSchwartzNPoint_le
        (d := d) p (l - i) t g
    have hp_nonneg : 0 ≤ SchwartzMap.seminorm ℝ p (l - i) g := by positivity
    have h0_nonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 (l - i) g := by positivity
    calc
      SchwartzMap.seminorm ℝ p (l - i) (timeShiftSchwartzNPoint (d := d) t g)
        ≤ 2 ^ (p - 1) *
            (SchwartzMap.seminorm ℝ p (l - i) g +
              ρ ^ p * SchwartzMap.seminorm ℝ 0 (l - i) g) := hbase
      _ ≤ 2 ^ (p - 1) *
            ((1 + ρ) ^ p * SchwartzMap.seminorm ℝ p (l - i) g +
              (1 + ρ) ^ p * SchwartzMap.seminorm ℝ 0 (l - i) g) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine add_le_add ?_ ?_
        · simpa [one_mul, mul_comm] using
            (mul_le_mul_of_nonneg_right hpow_one hp_nonneg)
        · exact mul_le_mul_of_nonneg_right hpow_ρ h0_nonneg
      _ = Ap i * (1 + ρ) ^ p := by
        dsimp [Ap]
        ring
  have htensor :=
    SchwartzMap.tensorProduct_seminorm_le (p := p) (l := l) f.osConj
      (timeShiftSchwartzNPoint (d := d) t g)
  calc
    SchwartzMap.seminorm ℝ p l
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
      = SchwartzMap.seminorm ℝ p l
          (f.osConj.tensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
            rfl
    _ ≤ 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℝ p i f.osConj *
            SchwartzMap.seminorm ℝ 0 (l - i) (timeShiftSchwartzNPoint (d := d) t g) +
          SchwartzMap.seminorm ℝ 0 i f.osConj *
            SchwartzMap.seminorm ℝ p (l - i) (timeShiftSchwartzNPoint (d := d) t g)) := htensor
    _ ≤ 2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℝ p i f * A0 i * (1 + ρ) ^ p +
          SchwartzMap.seminorm ℝ 0 i f * Ap i * (1 + ρ) ^ p) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
      intro i hi
      have hfP : SchwartzMap.seminorm ℝ p i f.osConj ≤ SchwartzMap.seminorm ℝ p i f :=
        SchwartzNPoint.seminorm_osConj_le (d := d) p i f
      have hf0 : SchwartzMap.seminorm ℝ 0 i f.osConj ≤ SchwartzMap.seminorm ℝ 0 i f :=
        SchwartzNPoint.seminorm_osConj_le (d := d) 0 i f
      have hchoose_nonneg : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
      apply mul_le_mul_of_nonneg_left ?_ hchoose_nonneg
      refine add_le_add ?_ ?_
      · calc
          SchwartzMap.seminorm ℝ p i f.osConj *
              SchwartzMap.seminorm ℝ 0 (l - i) (timeShiftSchwartzNPoint (d := d) t g)
            ≤ SchwartzMap.seminorm ℝ p i f *
                SchwartzMap.seminorm ℝ 0 (l - i) (timeShiftSchwartzNPoint (d := d) t g) := by
                  exact mul_le_mul_of_nonneg_right hfP (by positivity)
          _ ≤ SchwartzMap.seminorm ℝ p i f * (A0 i * (1 + ρ) ^ p) := by
                  exact mul_le_mul_of_nonneg_left (hshift0 i hi) (by positivity)
          _ = SchwartzMap.seminorm ℝ p i f * A0 i * (1 + ρ) ^ p := by
                  ring
      · calc
          SchwartzMap.seminorm ℝ 0 i f.osConj *
              SchwartzMap.seminorm ℝ p (l - i) (timeShiftSchwartzNPoint (d := d) t g)
            ≤ SchwartzMap.seminorm ℝ 0 i f *
                SchwartzMap.seminorm ℝ p (l - i) (timeShiftSchwartzNPoint (d := d) t g) := by
                  exact mul_le_mul_of_nonneg_right hf0 (by positivity)
          _ ≤ SchwartzMap.seminorm ℝ 0 i f * (Ap i * (1 + ρ) ^ p) := by
                  exact mul_le_mul_of_nonneg_left (hshiftP i hi) (by positivity)
          _ = SchwartzMap.seminorm ℝ 0 i f * Ap i * (1 + ρ) ^ p := by
                  ring
    _ = C * (1 + ρ) ^ p := by
      dsimp [C]
      have hsum :
          ∑ i ∈ Finset.range (l + 1),
              ↑(l.choose i) *
                (SchwartzMap.seminorm ℝ p i f * A0 i * (1 + ρ) ^ p +
                  SchwartzMap.seminorm ℝ 0 i f * Ap i * (1 + ρ) ^ p) =
            (∑ i ∈ Finset.range (l + 1),
                ↑(l.choose i) *
                  (SchwartzMap.seminorm ℝ p i f * A0 i +
                    SchwartzMap.seminorm ℝ 0 i f * Ap i)) * (1 + ρ) ^ p := by
        calc
          ∑ i ∈ Finset.range (l + 1),
              ↑(l.choose i) *
                (SchwartzMap.seminorm ℝ p i f * A0 i * (1 + ρ) ^ p +
                  SchwartzMap.seminorm ℝ 0 i f * Ap i * (1 + ρ) ^ p)
            = ∑ i ∈ Finset.range (l + 1),
                (↑(l.choose i) *
                  (SchwartzMap.seminorm ℝ p i f * A0 i +
                    SchwartzMap.seminorm ℝ 0 i f * Ap i)) * (1 + ρ) ^ p := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
          _ = (∑ i ∈ Finset.range (l + 1),
                ↑(l.choose i) *
                  (SchwartzMap.seminorm ℝ p i f * A0 i +
                    SchwartzMap.seminorm ℝ 0 i f * Ap i)) * (1 + ρ) ^ p := by
                  rw [Finset.sum_mul]
      rw [hsum]
      ring
    _ = C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
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

/-- Ordinary E0 gives a finite, pairing-dependent polynomial degree for each
ordered positive-time Schwinger pairing. -/
private theorem exists_norm_os_pairing_term_timeShift_le_polynomial
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_pos : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hg_pos : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m) :
    ∃ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))‖ ≤
        C * (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
  obtain ⟨indices, COS, hCOS, hOS⟩ :=
    OSReconstruction.exists_zeroDiagonalSchwinger_finsetSeminormBound OS (n + m)
  let p : ℕ := indices.sup fun j : ℕ × ℕ => j.1
  let Cterm : ℕ × ℕ → ℝ := fun j =>
    Classical.choose
      (exists_seminorm_osConjTensorProduct_timeShift_le_polynomial
        (d := d) j.1 j.2 f g)
  have hCterm (j : ℕ × ℕ) :
      0 ≤ Cterm j ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ j.1 j.2
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g)) ≤
          Cterm j *
            (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ j.1 := by
    exact Classical.choose_spec
      (exists_seminorm_osConjTensorProduct_timeShift_le_polynomial
        (d := d) j.1 j.2 f g)
  let Csemi : ℝ := ∑ j ∈ indices, Cterm j
  have hCsemi : 0 ≤ Csemi := by
    exact Finset.sum_nonneg fun j _ => (hCterm j).1
  refine ⟨p, COS * Csemi, mul_nonneg hCOS hCsemi, ?_⟩
  intro t ht
  have hzero :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := n) (m := m) (f := f)
      (g := timeShiftSchwartzNPoint (d := d) t g) hf_pos
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg_aux
        (d := d) t ht g hg_pos)
  have hsemi :
      indices.sup
          (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) ≤
        Csemi *
          (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro j hj
    calc
      SchwartzMap.seminorm ℂ j.1 j.2
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) =
          SchwartzMap.seminorm ℝ j.1 j.2
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := rfl
      _ ≤ Cterm j *
          (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ j.1 :=
        (hCterm j).2 t
      _ ≤ Cterm j *
          (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
        apply mul_le_mul_of_nonneg_left _ (hCterm j).1
        exact pow_le_pow_right₀
          (le_add_of_nonneg_right (norm_nonneg _))
          (Finset.le_sup (f := fun j : ℕ × ℕ => j.1) hj)
      _ ≤ Csemi *
          (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Finset.single_le_sum (fun j _ => (hCterm j).1) hj
  calc
    ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))‖
      = ‖OS.S (n + m)
          ⟨f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g), hzero⟩‖ := by
            rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
              (f := f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) hzero]
    _ ≤ COS * indices.sup
          (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
      hOS ⟨f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g), hzero⟩
    _ ≤ COS *
          (Csemi *
            (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p) :=
      mul_le_mul_of_nonneg_left hsemi hCOS
    _ = (COS * Csemi) *
          (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
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

/-- Ordinary E0 gives a polynomial bound for each fixed pair of positive-time
Borchers vectors by maximizing their finitely many Schwinger degrees. -/
theorem exists_norm_OSInnerProduct_right_timeShift_le_polynomial
    (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    ∃ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d) t (G : BorchersSequence d))‖ ≤
        C * t ^ p := by
  let I : Finset ℕ := Finset.range ((F : BorchersSequence d).bound + 1)
  let J : Finset ℕ := Finset.range ((G : BorchersSequence d).bound + 1)
  choose degree Cterm hCterm_nonneg hCterm_bound using
    fun n m =>
      exists_norm_os_pairing_term_timeShift_le_polynomial
        (d := d) OS
        ((F : BorchersSequence d).funcs n)
        ((G : BorchersSequence d).funcs m)
        (F.ordered_tsupport n) (G.ordered_tsupport m)
  have hCterm :
      ∀ n m, 0 ≤ Cterm n m ∧
        ∀ t : ℝ, 0 ≤ t →
          ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
              (((F : BorchersSequence d).funcs n).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))‖ ≤
            Cterm n m *
              (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^
                degree n m := by
    intro n m
    exact ⟨hCterm_nonneg n m, hCterm_bound n m⟩
  let p : ℕ := (I.product J).sup fun j : ℕ × ℕ => degree j.1 j.2
  have hdegree {n m : ℕ} (hn : n ∈ I) (hm : m ∈ J) :
      degree n m ≤ p := by
    exact Finset.le_sup
      (f := fun j : ℕ × ℕ => degree j.1 j.2)
      (show (n, m) ∈ I.product J from Finset.mem_product.mpr ⟨hn, hm⟩)
  let D : ℕ → ℝ := fun m =>
    (1 + ‖(fun _ : Fin m => timeShiftVec d 1 : NPointDomain d m)‖) ^ p
  let C : ℝ := ∑ n ∈ I, ∑ m ∈ J, Cterm n m * D m
  refine ⟨p, C, by
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
              degree n m := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum ?_
          intro m hm
          exact (hCterm n m).2 t ht0
    _ ≤ ∑ n ∈ I, ∑ m ∈ J,
          Cterm n m *
            (1 + ‖(fun _ : Fin m => timeShiftVec d t : NPointDomain d m)‖) ^ p := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum ?_
          intro m hm
          apply mul_le_mul_of_nonneg_left _ (hCterm n m).1
          exact pow_le_pow_right₀
            (le_add_of_nonneg_right (norm_nonneg _))
            (hdegree hn hm)
    _ ≤ ∑ n ∈ I, ∑ m ∈ J, Cterm n m * (D m * t ^ p) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum ?_
          intro m hm
          have hCnonneg : 0 ≤ Cterm n m := (hCterm n m).1
          have hpoly :=
            one_add_norm_timeShiftConfig_pow_le (d := d) (m := m)
              (s := p) t ht
          simpa [D] using mul_le_mul_of_nonneg_left hpoly hCnonneg
    _ = ∑ n ∈ I, ∑ m ∈ J, (Cterm n m * D m) * t ^ p := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
    _ = C * t ^ p := by
          calc
            ∑ n ∈ I, ∑ m ∈ J, (Cterm n m * D m) * t ^ p
              = ∑ n ∈ I, (∑ m ∈ J, Cterm n m * D m) * t ^ p := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  rw [← Finset.sum_mul]
            _ = (∑ n ∈ I, ∑ m ∈ J, Cterm n m * D m) * t ^ p := by
                  rw [← Finset.sum_mul]
            _ = C * t ^ p := by
                  rfl

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
            rw [Reconstruction.fieldOperatorAction_funcs_zero]
            have hzero :
                (⇑(0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) = 0 := by
              funext x
              rfl
            rw [hzero, tsupport_zero]
            exact Set.empty_subset _
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

theorem continuousOn_os_pairing_term_timeShift_nonneg_of_isCompactSupport
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
    change Continuous (fun t : Set.Ici (0 : ℝ) =>
      SchwartzMap.tensorProduct f.osConj (timeShiftSchwartzNPoint (d := d) t.1 g))
    exact (SchwartzMap.tensorProduct_continuous_right f.osConj).comp hshift
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
  simpa using congrArg (OS.S (n + m))
    (ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t.1 g))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := n) (m := m) (f := f)
        (g := timeShiftSchwartzNPoint (d := d) t.1 g) hf_pos
        (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
          (d := d) t.1 t.2 g hg_pos)))

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
def timeShiftPositiveTimeBorchers (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d where
  toBorchersSequence := timeShiftBorchers (d := d) t (F : BorchersSequence d)
  ordered_tsupport := by
    simpa using timeShift_preserves_ordered_positive_tsupport (d := d) t ht
      (F : BorchersSequence d) F.ordered_tsupport

/-- Nonnegative Euclidean time translation on the honest OS Borchers algebra.

This endpoint-inclusive variant is needed in the OS-II split construction:
the sum of the time differences strictly before or after the selected
coordinate can be `0`, while the positive-time support condition is still
preserved. -/
def timeShiftNonnegPositiveTimeBorchers (t : ℝ) (ht : 0 ≤ t)
    (F : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d where
  toBorchersSequence := timeShiftBorchers (d := d) t (F : BorchersSequence d)
  ordered_tsupport := by
    simpa using timeShift_preserves_ordered_positive_tsupport_nonneg (d := d) t ht
      (F : BorchersSequence d) F.ordered_tsupport

omit [NeZero d] in
@[simp] theorem timeShiftPositiveTimeBorchers_funcs (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    ((timeShiftPositiveTimeBorchers (d := d) t ht F : PositiveTimeBorchersSequence d) :
      BorchersSequence d).funcs n =
        timeShiftSchwartzNPoint (d := d) t ((F : BorchersSequence d).funcs n) :=
  rfl

omit [NeZero d] in
@[simp] theorem timeShiftNonnegPositiveTimeBorchers_funcs (t : ℝ) (ht : 0 ≤ t)
    (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    ((timeShiftNonnegPositiveTimeBorchers (d := d) t ht F : PositiveTimeBorchersSequence d) :
      BorchersSequence d).funcs n =
        timeShiftSchwartzNPoint (d := d) t ((F : BorchersSequence d).funcs n) :=
  rfl

omit [NeZero d] in
@[simp] theorem timeShiftPositiveTimeBorchers_toBorchersSequence (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) :
    ((timeShiftPositiveTimeBorchers (d := d) t ht F : PositiveTimeBorchersSequence d) :
      BorchersSequence d) =
        timeShiftBorchers (d := d) t (F : BorchersSequence d) := rfl

omit [NeZero d] in
@[simp] theorem timeShiftNonnegPositiveTimeBorchers_toBorchersSequence
    (t : ℝ) (ht : 0 ≤ t) (F : PositiveTimeBorchersSequence d) :
    ((timeShiftNonnegPositiveTimeBorchers (d := d) t ht F :
      PositiveTimeBorchersSequence d) : BorchersSequence d) =
        timeShiftBorchers (d := d) t (F : BorchersSequence d) := rfl

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

/-- Euclidean time-translation covariance of the OS pairing: a time shift on
the left Borchers vector can be transferred to the right vector as part of the
combined positive time shift, provided the relevant tensor products are
admissible. -/
theorem OSInnerProduct_timeShift_eq (OS : OsterwalderSchraderAxioms d)
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
def osTimeShift (OS : OsterwalderSchraderAxioms d) (t : ℝ) (ht : 0 < t) :
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
def osTimeShiftLinear (OS : OsterwalderSchraderAxioms d) (t : ℝ) (ht : 0 < t) :
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
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    ∃ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
      ‖(osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)‖ ≤
        C * t ^ p := by
  obtain ⟨p, C0, hC0_nonneg, hC0⟩ :=
    exists_norm_OSInnerProduct_right_timeShift_le_polynomial (d := d) OS F F
  let C : ℝ := C0 * (2 : ℝ) ^ p + 1
  refine ⟨p, C, by
    dsimp [C]
    positivity, ?_⟩
  intro t ht1 ht
  have ht0 : 0 ≤ t := by linarith
  have h2t_ge : 1 ≤ t + t := by linarith
  let y : OSPreHilbertSpace OS :=
    (osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)
  have hsq :
      ‖y‖ ^ 2 ≤ C0 * (t + t) ^ p := by
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
      _ ≤ C0 * (t + t) ^ p := hC0 (t + t) h2t_ge
  have hsq' :
      ‖y‖ ^ 2 ≤ (C0 * (2 : ℝ) ^ p) * t ^ p := by
    calc
      ‖y‖ ^ 2 ≤ C0 * (t + t) ^ p := hsq
      _ = C0 * ((2 : ℝ) ^ p * t ^ p) := by
          rw [show t + t = (2 : ℝ) * t by ring, mul_pow]
      _ = (C0 * (2 : ℝ) ^ p) * t ^ p := by
          ring
  have hone : 1 ≤ t ^ p := one_le_pow₀ ht1
  calc
    ‖(osTimeShiftLinear (d := d) OS t ht) (⟦F⟧ : OSPreHilbertSpace OS)‖ = ‖y‖ := by
      rfl
    _ ≤ ‖y‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖y‖ - (1 / 2 : ℝ))]
    _ ≤ (C0 * (2 : ℝ) ^ p) * t ^ p + t ^ p := by
      nlinarith [hsq', hone]
    _ = C * t ^ p := by
      dsimp [C]
      ring

/-- Every OS quotient vector has some finite polynomial time-shift growth
degree, obtained from ordinary E0 for a chosen Borchers representative. -/
theorem exists_norm_osTimeShiftLinear_le_polynomial
    (OS : OsterwalderSchraderAxioms d)
    (x : OSPreHilbertSpace OS) :
    ∃ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
      ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ≤ C * t ^ p := by
  induction x using Quotient.inductionOn with
  | h F =>
      simpa using
        exists_norm_osTimeShiftLinear_le_polynomial_of_repr (d := d) OS F

private theorem osTimeShiftLinear_contraction
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    ‖(osTimeShiftLinear (d := d) OS t ht) x‖ ≤ ‖x‖ := by
  obtain ⟨p, C, hC_pos, hgrowth⟩ :=
    exists_norm_osTimeShiftLinear_le_polynomial (d := d) OS x
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
  have hbound : ∀ T, 1 ≤ T → N T ≤ C * T ^ (p : ℝ) := by
    intro T hT
    have hT_pos : 0 < T := by linarith
    have h := hgrowth T hT hT_pos
    simpa [N, hT_pos, Real.rpow_natCast] using h
  have hcontr := SCV.MultipleReflection.contraction_of_doubling_and_growth
    N hD C p hC_pos (by positivity) hbound t ht
  simpa [N, ht] using hcontr

/-- Ordinary fixed-arity E0 continuity and reflection positivity already give
the genuine OS contraction semigroup; no arity-uniform growth premise is used. -/
def euclideanSemigroup_of_OS
    (OS : OsterwalderSchraderAxioms d) :
    EuclideanSemigroup OS where
  T := fun t ht => osTimeShiftLinear (d := d) OS t ht
  semigroup := fun s t hs ht => osTimeShiftLinear_semigroup (d := d) OS s t hs ht
  contraction := fun t ht x => osTimeShiftLinear_contraction (d := d) OS t ht x
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
    simpa using osTimeShiftLinear_contraction (d := d) OS t ht x)

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

theorem osTimeShiftHilbert_coe
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
    exact osTimeShiftLinear_contraction (d := d) OS t ht a

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
  obtain hH | hH := subsingleton_or_nontrivial (OSHilbertSpace OS)
  · exfalso
    rw [spectrum.of_subsingleton (R := ℝ) (a := osTimeShiftHilbert (d := d) OS lgc t ht)] at hx
    exact hx
  · haveI : Nontrivial (OSHilbertSpace OS) := hH
    letI : NontrivialTopology (OSHilbertSpace OS) := inferInstance
    constructor
    · exact spectrum_nonneg_of_nonneg
        (osTimeShiftHilbert_nonneg (d := d) OS lgc t ht) hx
    · have hnorm_le :
          ‖osTimeShiftHilbert (d := d) OS lgc t ht‖ ≤ 1 :=
        osTimeShiftHilbert_norm_le_one (d := d) OS lgc t ht
      have hspectrum_le :
          ∀ y ∈ spectrum ℝ (osTimeShiftHilbert (d := d) OS lgc t ht), y ≤ 1 :=
        by
          intro y hy
          have hy_nonneg : 0 ≤ y :=
            spectrum_nonneg_of_nonneg
              (osTimeShiftHilbert_nonneg (d := d) OS lgc t ht) hy
          haveI : NormOneClass (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := inferInstance
          have hy_norm_le : ‖y‖ ≤ ‖osTimeShiftHilbert (d := d) OS lgc t ht‖ :=
            spectrum.norm_le_norm_of_mem hy
          have hy_le_norm : y ≤ ‖osTimeShiftHilbert (d := d) OS lgc t ht‖ := by
            rw [Real.norm_of_nonneg hy_nonneg] at hy_norm_le
            exact hy_norm_le
          exact hy_le_norm.trans hnorm_le
      exact hspectrum_le x hx

/-- The actual OS Hilbert time shift, constructed solely from the original
Euclidean axioms and the already proved E0 contraction estimate. -/
noncomputable def osTimeShiftHilbertOfOS
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) :
    OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  (UniformSpace.Completion.toComplL.comp
    ((osTimeShiftLinear (d := d) OS t ht).mkContinuous 1 (fun x => by
      simpa using osTimeShiftLinear_contraction (d := d) OS t ht x))).extend
    UniformSpace.Completion.toComplL

/-- The legacy growth-indexed Hilbert shift is definitionally the original-OS
operator; its extra growth argument contributes no mathematical content. -/
theorem osTimeShiftHilbert_eq_ofOS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (ht : 0 < t) :
    osTimeShiftHilbert (d := d) OS lgc t ht =
      osTimeShiftHilbertOfOS (d := d) OS t ht := by
  rfl

theorem osTimeShiftHilbertOfOS_coe
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSPreHilbertSpace OS) :
    osTimeShiftHilbertOfOS (d := d) OS t ht (x : OSHilbertSpace OS) =
      ((osTimeShiftLinear (d := d) OS t ht x : OSPreHilbertSpace OS) :
        OSHilbertSpace OS) := by
  exact ContinuousLinearMap.extend_eq _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _) x

theorem osTimeShiftHilbertOfOS_contraction
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSHilbertSpace OS) :
    ‖osTimeShiftHilbertOfOS (d := d) OS t ht x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_le
      (osTimeShiftHilbertOfOS (d := d) OS t ht).continuous.norm continuous_norm
  · intro a
    rw [osTimeShiftHilbertOfOS_coe (d := d) OS t ht a,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact osTimeShiftLinear_contraction (d := d) OS t ht a

private theorem osTimeShiftHilbertOfOS_apply_inner_self_real_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) (x : OSHilbertSpace OS) :
    let q := @inner ℂ (OSHilbertSpace OS) inferInstance
      ((osTimeShiftHilbertOfOS (d := d) OS t ht) x) x
    q.im = 0 ∧ 0 ≤ q.re := by
  let T := osTimeShiftHilbertOfOS (d := d) OS t ht
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
    simpa [good, T, osTimeShiftHilbertOfOS_coe,
      UniformSpace.Completion.inner_coe] using
      (osTimeShiftLinear_apply_inner_self_real_nonneg (d := d) OS t ht a)
  exact hx

/-- Reflection positivity makes the E0-only completed time shift positive. -/
theorem osTimeShiftHilbertOfOS_isPositive
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) :
    (osTimeShiftHilbertOfOS (d := d) OS t ht).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hq := osTimeShiftHilbertOfOS_apply_inner_self_real_nonneg
    (d := d) OS t ht x
  refine ⟨?_, hq.2⟩
  apply Complex.ext <;> simp [hq.1]

theorem osTimeShiftHilbertOfOS_isSelfAdjoint
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) :
    IsSelfAdjoint (osTimeShiftHilbertOfOS (d := d) OS t ht) :=
  (osTimeShiftHilbertOfOS_isPositive (d := d) OS t ht).isSelfAdjoint

theorem osTimeShiftHilbertOfOS_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ osTimeShiftHilbertOfOS (d := d) OS t ht := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact osTimeShiftHilbertOfOS_isPositive (d := d) OS t ht

theorem osTimeShiftHilbertOfOS_norm_le_one
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) :
    ‖osTimeShiftHilbertOfOS (d := d) OS t ht‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simpa [one_mul] using osTimeShiftHilbertOfOS_contraction (d := d) OS t ht x

/-- The positive spectral certificate needed for reconstruction follows from
ordinary OS data, without the degenerate legacy linear-growth record. -/
theorem spectrum_osTimeShiftHilbertOfOS_subset_Icc
    (OS : OsterwalderSchraderAxioms d)
    (t : ℝ) (ht : 0 < t) :
    spectrum ℝ (osTimeShiftHilbertOfOS (d := d) OS t ht) ⊆ Set.Icc 0 1 := by
  intro x hx
  obtain hH | hH := subsingleton_or_nontrivial (OSHilbertSpace OS)
  · exfalso
    rw [spectrum.of_subsingleton
      (R := ℝ) (a := osTimeShiftHilbertOfOS (d := d) OS t ht)] at hx
    exact hx
  · haveI : Nontrivial (OSHilbertSpace OS) := hH
    letI : NontrivialTopology (OSHilbertSpace OS) := inferInstance
    constructor
    · exact spectrum_nonneg_of_nonneg
        (osTimeShiftHilbertOfOS_nonneg (d := d) OS t ht) hx
    · have hnonneg : 0 ≤ x := spectrum_nonneg_of_nonneg
        (osTimeShiftHilbertOfOS_nonneg (d := d) OS t ht) hx
      haveI : NormOneClass (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) :=
        inferInstance
      have hnorm : ‖x‖ ≤ ‖osTimeShiftHilbertOfOS (d := d) OS t ht‖ :=
        spectrum.norm_le_norm_of_mem hx
      rw [Real.norm_of_nonneg hnonneg] at hnorm
      exact hnorm.trans (osTimeShiftHilbertOfOS_norm_le_one (d := d) OS t ht)

namespace OSReconstruction

/-- Complex spectral continuation of the original OS contraction, constructed
without the mathematically degenerate legacy growth record. -/
noncomputable def osiiOriginalOSHilbertComplex
    (OS : OsterwalderSchraderAxioms d) (z : Complex) :
    OSHilbertSpace OS →L[Complex] OSHilbertSpace OS :=
  ContinuousLinearMap.spectralSemigroupComplex
    (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
    (osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
    (osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
    (spectrum_osTimeShiftHilbertOfOS_subset_Icc (d := d) OS 1 one_pos)
    z

theorem differentiableOn_osiiOriginalOSHilbertComplex_inner
    (OS : OsterwalderSchraderAxioms d) (x y : OSHilbertSpace OS) :
    DifferentiableOn Complex
      (fun z => @inner Complex (OSHilbertSpace OS) inferInstance x
        (osiiOriginalOSHilbertComplex OS z y))
      {z : Complex | 0 < z.re} := by
  simpa [osiiOriginalOSHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_differentiableOn
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos)
      (x := x) (y := y))

theorem continuousOn_osiiOriginalOSHilbertComplex
    (OS : OsterwalderSchraderAxioms d) :
    ContinuousOn (osiiOriginalOSHilbertComplex OS)
      {z : Complex | 0 < z.re} := by
  unfold osiiOriginalOSHilbertComplex
  exact ContinuousLinearMap.spectralSemigroupComplex_continuousOn
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos)

theorem continuousOn_osiiOriginalOSHilbertComplex_apply
    (OS : OsterwalderSchraderAxioms d) (y : OSHilbertSpace OS) :
    ContinuousOn (fun z => osiiOriginalOSHilbertComplex OS z y)
      {z : Complex | 0 < z.re} := by
  simpa [osiiOriginalOSHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_strongContinuousOn
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos)
      (y := y))

theorem continuousOn_osiiOriginalOSHilbertComplex_jointly
    (OS : OsterwalderSchraderAxioms d) :
    ContinuousOn
      (fun p : Complex × OSHilbertSpace OS =>
        osiiOriginalOSHilbertComplex OS p.1 p.2)
      ({z : Complex | 0 < z.re} ×ˢ Set.univ) := by
  simpa [osiiOriginalOSHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_jointlyContinuousOn
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos))

theorem osiiOriginalOSHilbertComplex_norm_le
    (OS : OsterwalderSchraderAxioms d)
    (z : Complex) (hz : 0 < z.re) :
    ‖osiiOriginalOSHilbertComplex OS z‖ ≤ 2 := by
  simpa [osiiOriginalOSHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_norm_le
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos)
      (z := z) hz)

end OSReconstruction

private def osTimeShiftHilbertSpectralMeasureDiagonal
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    MeasureTheory.Measure
      (spectrum ℝ (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)) :=
  ContinuousLinearMap.selfAdjointSpectralMeasureDiagonal
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    x

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

private theorem differentiableOn_osTimeShiftHilbertHolomorphicValueOffdiag
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x y : OSHilbertSpace OS) :
    DifferentiableOn ℂ (osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc x y)
      {z : ℂ | 0 < z.re} := by
  unfold osTimeShiftHilbertHolomorphicValueOffdiag
  exact ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceOffdiag
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x) (y := y)

/-- Raw OS pairing version of the one-variable holomorphic extension for Euclidean time shift. -/
def OSInnerProductTimeShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (z : ℂ) : ℂ :=
  osTimeShiftHilbertHolomorphicValueOffdiag (d := d) OS lgc
    (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
    (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) z

/-- Monograph Vol IV Ch 2 Step 4 (lines 1078-1099): the one-variable OS
holomorphic matrix element is represented by the completed Hilbert-space
scalar product against the complex Euclidean time-shift.  This is the concrete
scalar-product identity used after the regularized `T_{k,ρ}` construction. -/
theorem OSInnerProductTimeShiftHolomorphicValue_eq_inner_osTimeShiftHilbertComplex
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

private theorem differentiableOn_OSInnerProductTimeShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G)
      {z : ℂ | 0 < z.re} := by
  unfold OSInnerProductTimeShiftHolomorphicValue
  exact differentiableOn_osTimeShiftHilbertHolomorphicValueOffdiag
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

section RotatedBoundaryValue

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end RotatedBoundaryValue

/-- Real Euclidean time shift of a concentrated OS tensor term. -/
theorem OSInnerProduct_single_right_timeShift
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

end
