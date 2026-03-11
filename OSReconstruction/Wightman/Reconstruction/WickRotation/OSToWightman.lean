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
import OSReconstruction.vNA.Unbounded.BoundedBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# OS to Wightman (E'→R')

Analytic continuation from Euclidean to Minkowski: given Schwinger functions
satisfying E0'-E4 (with the linear growth condition), reconstruct Wightman
functions satisfying R0-R5.

The critical point is that the Euclidean input is honest Schwinger data on the
zero-diagonal test space `°S`, while the Wightman output is a full tempered
distribution family on Schwartz space. That jump is the heart of OS
reconstruction; it must not be smuggled into the Euclidean hypothesis by
quietly assuming a full-Schwartz Schwinger theory from the start.

The proof proceeds through phases:
- Phase 2: Euclidean time translation semigroup
- Phase 3: Inductive analytic continuation (OS II, Theorem 4.1-4.2)
- Phase 4: Boundary values → tempered distributions
- Phase 5: Property transfer (OS axioms → Wightman axioms)
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
private theorem timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
    {n : ℕ} (t : ℝ) (ht : 0 < t) (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((timeShiftSchwartzNPoint (d := d) t f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg
    (d := d) t (le_of_lt ht) f hf

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
private abbrev OSHilbertSpace (OS : OsterwalderSchraderAxioms d) :=
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

/- Phase 3: Analytic continuation from Euclidean to Minkowski.

    The analytic continuation proceeds inductively. Starting from Schwinger functions
    S_n defined on Euclidean configurations, we extend to complex times.

    **Inductive structure** (OS II, Theorem 4.1):
    - A₀: S_k(ξ) is analytic on {ξ ∈ ℝ^k : ξⱼ > 0 for all j}
    - Aᵣ: S_k has analytic continuation to the region C_k^(r) ⊂ ℂ^k
      where r of the ξ-variables are complexified
    - After n = d + 1 steps, reach the full forward tube

    **Key estimate** (OS II, Theorem 4.2): At each step, the linear growth
    condition E0' provides the bounds needed for the continuation. -/

/-- The region C_k^(r) from OS II: the domain after r steps of analytic continuation.
    C_k^(0) = {ξ ∈ ℝ^k : Im = 0, ξᵢ₀ > 0} (positive real Euclidean domain)
    C_k^(r+1) = {z ∈ ℂ^{k(d+1)} : Im(z_i,μ - z_{i-1,μ}) > 0 for all i, μ ≤ r}
      (open forward tube in the first r+1 spacetime directions; no constraint on μ > r).

    **Key property**: For r ≥ 1, C_k^(r) is an OPEN subset of ℂ^{k(d+1)}
    (strict positivity of imaginary parts ⟹ open). This ensures `DifferentiableOn ℂ`
    on C_k^(r) is genuine holomorphicity, not a vacuous condition.

    **Note**: C_k^(d+1) is the tube over a positive orthant in difference
    coordinates, not yet the Wightman forward tube. The active reconstruction
    chain in this file no longer uses the old Bochner/orbit route, so we do not
    build further geometry on that path here.

    The regions are monotone in the reverse direction for `r ≥ 1`:
      C_k^(r+1) ⊆ C_k^(r),
    since each step adds one more imaginary-positivity constraint. Also
    `C_k^(0)` is disjoint from `C_k^(r)` for r ≥ 1 (`C_k^(0)` has Im = 0,
    while `C_k^(r)` requires Im > 0 in at least one direction). -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- Base: positive Euclidean domain (all Im = 0, Euclidean times positive)
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- Open forward tube in first r+1 spacetime directions;
    -- no constraint on remaining directions (μ > r), giving an open set.
    { z | ∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0 }

/-- Each individual coordinate positivity condition in the r+1 analytic continuation region
    defines an open set. This is the building block for `isOpen_analyticContinuationRegion_succ`. -/
private theorem isOpen_acr_coord {d k r : ℕ} (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      μ.val ≤ r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0 } := by
  by_cases hμ : μ.val ≤ r
  · by_cases hi : i.val = 0
    · have hcont : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im := by
        simpa using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
      simpa [hμ, hi] using isOpen_lt continuous_const hcont
    · let j : Fin k := ⟨i.val - 1, by omega⟩
      have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im := by
        simpa using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
      have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im := by
        simpa [j] using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j)))
      simpa [hμ, hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'
  · simp [hμ]

/-- For r ≥ 1, the analytic continuation region C_k^(r+1) is open. The strict imaginary-part
    positivity conditions are open conditions, and the region is a finite intersection of them. -/
theorem isOpen_analyticContinuationRegion_succ {d k r : ℕ} [NeZero d] :
    IsOpen (AnalyticContinuationRegion d k (r + 1)) := by
  suffices h :
      AnalyticContinuationRegion d k (r + 1) =
        ⋂ i : Fin k, ⋂ μ : Fin (d + 1),
          { z : Fin k → Fin (d + 1) → ℂ |
            μ.val ≤ r →
              let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
              (z i μ - prev μ).im > 0 } by
    rw [h]
    exact isOpen_iInter_of_finite (fun i : Fin k =>
      isOpen_iInter_of_finite (fun μ : Fin (d + 1) =>
        isOpen_acr_coord (d := d) (k := k) (r := r) i μ))
  ext z
  simp [AnalyticContinuationRegion]

private theorem differentiable_unflattenCfg_local (k d : ℕ) :
    Differentiable ℂ (BHW.unflattenCfg k d :
      (Fin (k * (d + 1)) → ℂ) → (Fin k → Fin (d + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  rw [differentiable_pi]
  intro μ
  simpa [BHW.unflattenCfg] using (differentiable_apply (finProdFinEquiv (i, μ)))

private theorem differentiable_fromDiffFlat_local (k d : ℕ) :
    Differentiable ℂ (BHW.fromDiffFlat k d) := by
  unfold BHW.fromDiffFlat
  exact (BHW.diffCoordEquiv k d).symm.differentiable.comp
    (differentiable_unflattenCfg_local k d)

private theorem differentiable_flattenCfg_local (k d : ℕ) :
    Differentiable ℂ (BHW.flattenCfg k d :
      (Fin k → Fin (d + 1) → ℂ) → (Fin (k * (d + 1)) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  let p : Fin k × Fin (d + 1) := finProdFinEquiv.symm i
  let projInner :
      (Fin k → Fin (d + 1) → ℂ) → (Fin (d + 1) → ℂ) := fun z => z p.1
  let evalInner :
      (Fin k → Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
    ContinuousLinearMap.proj (R := ℂ) p.1
  have hconst :
      Differentiable ℂ
        (fun _ : (Fin k → Fin (d + 1) → ℂ) =>
          (ContinuousLinearMap.proj (R := ℂ) p.2 :
            (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) :=
    differentiable_const _
  simpa [BHW.flattenCfg, p] using
    (hconst.clm_apply
      (by simpa [projInner, evalInner] using
        (differentiable_apply p.1 : Differentiable ℂ projInner)))

private theorem differentiable_toDiffFlat_local (k d : ℕ) :
    Differentiable ℂ (BHW.toDiffFlat k d) := by
  unfold BHW.toDiffFlat
  exact (differentiable_flattenCfg_local k d).comp
    (BHW.diffCoordEquiv k d).differentiable

/-! ### First-step region as a tube over positive time-differences -/

/-- The flattened cone for `C_k^(1)`: only the time-difference coordinates are
    constrained to have positive imaginary part. -/
private def FlatPositiveTimeDiffReal (k d : ℕ) : Set (Fin (k * (d + 1)) → ℝ) :=
  {u | ∀ i : Fin k, 0 < u (finProdFinEquiv (i, 0))}

private theorem isOpen_flatPositiveTimeDiffReal (k d : ℕ) :
    IsOpen (FlatPositiveTimeDiffReal k d) := by
  simp only [FlatPositiveTimeDiffReal, Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun i : Fin k =>
    isOpen_lt continuous_const (continuous_apply (finProdFinEquiv (i, 0))))

/-- `C_k^(1)` is exactly the tube over the positive time-difference cone in
    flattened difference coordinates. -/
private theorem acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff {d k : ℕ} [NeZero d]
    (z : Fin k → Fin (d + 1) → ℂ) :
    z ∈ AnalyticContinuationRegion d k 1 ↔
      BHW.toDiffFlat k d z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) := by
  constructor
  · intro hz
    change (fun i => ((BHW.toDiffFlat k d z) i).im) ∈ FlatPositiveTimeDiffReal k d
    intro i
    have htime : 0 < (BHW.diffCoordEquiv k d z i 0).im := by
      by_cases hi : i.val = 0
      · have h0 := hz i 0 (Nat.le_refl 0)
        have h0' : 0 < (z i 0).im := by
          simpa [hi] using h0
        simpa [BHW.diffCoordEquiv_apply, hi] using h0'
      · have h1 := hz i 0 (Nat.le_refl 0)
        have h1' : 0 < (z i 0 - z ⟨i.val - 1, by omega⟩ 0).im := by
          simpa [hi, Complex.sub_im, sub_pos] using h1
        simpa [BHW.diffCoordEquiv_apply, hi] using h1'
    simpa [FlatPositiveTimeDiffReal, BHW.toDiffFlat, BHW.flattenCfg] using htime
  · intro hz
    change (fun i => ((BHW.toDiffFlat k d z) i).im) ∈ FlatPositiveTimeDiffReal k d at hz
    simp only [AnalyticContinuationRegion, Set.mem_setOf_eq]
    intro i μ hμ
    have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
    subst hμ0
    have hflat : 0 < ((BHW.toDiffFlat k d z) (finProdFinEquiv (i, 0))).im :=
      hz i
    have hdiff : 0 < (BHW.diffCoordEquiv k d z i 0).im := by
      simpa [BHW.toDiffFlat, BHW.flattenCfg] using hflat
    by_cases hi : i.val = 0
    · simpa [BHW.diffCoordEquiv_apply, hi] using hdiff
    · have h1 : 0 < (z i 0 - z ⟨i.val - 1, by omega⟩ 0).im := by
        simpa [BHW.diffCoordEquiv_apply, hi] using hdiff
      simpa [hi, Complex.sub_im, sub_pos] using h1

/-- Transport holomorphicity on `C_k^(1)` to the positive-time-difference tube in
    flattened difference coordinates. -/
private theorem differentiableOn_toDiffFlat_of_acrone_holo {d k : ℕ} [NeZero d]
    (F : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (AnalyticContinuationRegion d k 1)) :
    DifferentiableOn ℂ (fun u : Fin (k * (d + 1)) → ℂ => F (BHW.fromDiffFlat k d u))
      (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) := by
  intro u hu
  have hz : BHW.fromDiffFlat k d u ∈ AnalyticContinuationRegion d k 1 := by
    have hu' : BHW.toDiffFlat k d (BHW.fromDiffFlat k d u) ∈
        SCV.TubeDomain (FlatPositiveTimeDiffReal k d) := by
      simpa [BHW.toDiffFlat_fromDiffFlat (n := k) (d := d) u] using hu
    exact (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff
      (d := d) (k := k) (BHW.fromDiffFlat k d u)).mpr hu'
  have hF_at : DifferentiableAt ℂ F (BHW.fromDiffFlat k d u) :=
    (hF_holo _ hz).differentiableAt
      ((isOpen_analyticContinuationRegion_succ (d := d) (k := k) (r := 0)).mem_nhds hz)
  exact (hF_at.comp u (by
    simpa [BHW.fromDiffFlat] using differentiable_fromDiffFlat_local k d u)).differentiableWithinAt

/-- Transport holomorphicity from the positive-time-difference tube in flattened
    difference coordinates back to `C_k^(1)`. -/
private theorem differentiableOn_of_toDiffFlat_acrone_holo {d k : ℕ} [NeZero d]
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d))) :
    DifferentiableOn ℂ (fun z : Fin k → Fin (d + 1) → ℂ => G (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  intro z hz
  have hu : BHW.toDiffFlat k d z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) :=
    (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff (d := d) (k := k) z).mp hz
  have hG_at : DifferentiableAt ℂ G (BHW.toDiffFlat k d z) :=
    (hG_holo _ hu).differentiableAt
      ((SCV.tubeDomain_isOpen (isOpen_flatPositiveTimeDiffReal k d)).mem_nhds hu)
  exact (hG_at.comp z (differentiable_toDiffFlat_local k d z)).differentiableWithinAt

/-- **Base step of analytic continuation (r = 0 → r = 1).**

    Produces the first genuinely holomorphic witness on `C_k^(1)` directly from the
    Schwinger functional `OS.S k`. This avoids introducing a separate "base-region
    kernel" on `C_k^(0)`, which would be a stronger and less natural object than the
    reconstruction chain actually needs.

    In the current file, `C_k^(1)` has already been identified as a tube domain over
    the positive time-difference cone in flattened difference coordinates via
    `acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff`. So the remaining
    content is not target-domain geometry.

    The real missing input is a spectral/Laplace representation theorem for the
    honest Euclidean time-translation semigroup on `OSPreHilbertSpace OS`: for fixed
    Euclidean quotient vectors, the scalar kernel
      `t ↦ ⟪x, T_t x⟫`
    should be representable as a Laplace transform of a finite measure on
    `[0, ∞)`. That one-sided support is exactly what feeds the 1D Paley-Wiener
    theorem on the positive time-difference tube.

    So this theorem is currently blocked by the positivity/spectral part of OS II
    (reflection positivity + Euclidean time translations -> positive-energy slice
    support), not by the tube-domain chart or the separate-to-joint holomorphicity
    mechanism.

    Ref: OS II, Section IV (base case of induction); Reed-Simon II, Section X.7;
    Streater-Wightman, §3.2-§3.3. -/
private theorem schwinger_continuation_base_step_of_flatWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)))
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d k),
      OS.S k f = ∫ x : NPointDomain d k,
        G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  let S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ := fun z => G (BHW.toDiffFlat k d z)
  refine ⟨S_ext, ?_, ?_⟩
  · simpa [S_ext] using
      differentiableOn_of_toDiffFlat_acrone_holo (d := d) (k := k) G hG_holo
  · intro f
    simpa [S_ext] using hG_euclid f

theorem schwinger_continuation_base_step {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  -- The SCV side now has both the 1D and product-half-plane Laplace theorems:
  -- `SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport` and
  -- `SCV.multivariateLaplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport`.
  -- So the genuine remaining gap is not half-plane holomorphicity or Osgood assembly,
  -- but the OS II semigroup/spectral step producing the required finite measure on
  -- `[0, ∞)` (or equivalent positive-energy matrix-element representation) for the
  -- flattened positive time-difference coordinates.
  obtain ⟨G, hG_holo, hG_euclid⟩ :
      ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
        DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) ∧
        (∀ (f : ZeroDiagonalSchwartz d k),
          OS.S k f = ∫ x : NPointDomain d k,
            G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
    sorry
  exact schwinger_continuation_base_step_of_flatWitness OS k G hG_holo hG_euclid

/-- **ξ-shift: the correct one-variable perturbation in the cumulative-sum structure.**

    In the cumulative-sum parametrization, the j-th new variable at level r is
      ξ[j] = z[j][r] - (if j = 0 then 0 else z[j-1][r])
    These k variables ξ[0], ..., ξ[k-1] are INDEPENDENT:
      C_k^(r+1) = C_k^(r) × UHP^k  (in the (z_base, ξ) parametrization).

    Moving ξ[j] by t (holding ξ[i] fixed for i ≠ j) requires shifting ALL z[i][r]
    for i ≥ j by +t simultaneously, since z[i][r] = ξ[0] + ... + ξ[i] (cumulative sum).

    WARNING: Updating only z[j][r] while keeping z[j+1][r],...,z[k-1][r] fixed changes
    BOTH ξ[j] (by +t) AND ξ[j+1] (by -t), which is NOT a single-variable extension.
    The test case in `test/acr_next_steps_test.lean` (d=1, k=2, r=1) confirms that a
    single-coordinate update can FAIL to land in ACR(r+1). -/
def xiShift {k d : ℕ} (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) : Fin k → Fin (d + 1) → ℂ :=
  fun i μ => if j.val ≤ i.val ∧ μ = r then z i μ + t else z i μ

/-- For r ≥ 1, the ξ-shift stays in C_k^(r). The shift only modifies column r,
    and C_k^(r) only constrains columns with μ.val ≤ r-1. -/
private theorem xiShift_stays_in_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (j : Fin k) (t : ℝ) :
    xiShift j ⟨r, hr⟩ z₀ (t : ℂ) ∈ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  intro i μ hμ
  have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) := by
    intro heq; have := congr_arg Fin.val heq; simp at this; omega
  -- xiShift is identity at μ ≠ ⟨r'+1, _⟩
  have h_eq : ∀ i' : Fin k, xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t i' μ = z₀ i' μ := by
    intro i'
    unfold xiShift
    split_ifs with h
    · exact absurd h.2 hμ_ne
    · rfl
  rw [h_eq i]
  have h_prev : (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t ⟨i.val - 1, by omega⟩) μ =
                (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else z₀ ⟨i.val - 1, by omega⟩) μ := by
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
  rw [h_prev]
  exact hz₀ i μ hμ

/-- For r ≥ 1, ACR(r+1) is a subset of ACR(r): adding more imaginary-positivity
    constraints gives a smaller domain. -/
private theorem acr_succ_subset {d k r : ℕ} [NeZero d] (hr : 0 < r) :
    AnalyticContinuationRegion d k (r + 1) ⊆ AnalyticContinuationRegion d k r := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  intro z hz
  simpa [AnalyticContinuationRegion] using
    (fun i μ hμ => hz i μ (Nat.le_trans hμ (Nat.le_succ _)))

/-- **Mixed one-slice continuation domain** for the r → r+1 inductive step.

    `OneSliceContinuationDomain d k r hr i₀` is the "intermediate" domain where:
    - all ACR(r) positivity constraints hold (Im-differences > 0 for μ < r), AND
    - the new cumulative-difference coordinate for particle `i₀` at level r also
      has positive imaginary part: Im(z[i₀][r] - prev[i₀][r]) > 0,
    - but the other new r-th differences (for i ≠ i₀) remain unconstrained.

    **Why this domain matters**: ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain i₀
    (proved by `iInter_oneSliceContinuationDomain_eq_acr_succ`). The full Paley-Wiener
    continuation argument extends S_prev to ONE slice at a time: for each i₀, extend
    in the ξ[i₀][r] direction using 1D Paley-Wiener to get a holomorphic function on
    `OneSliceContinuationDomain i₀`. Then assemble all k slice extensions via Osgood's
    theorem to get holomorphicity on ACR(r+1).

    Ref: OS II, Theorem 4.1; Vladimirov §26 -/
def OneSliceContinuationDomain (d k r : ℕ) [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) : Set (Fin k → Fin (d + 1) → ℂ) :=
  { z |
      (∀ i : Fin k, ∀ μ : Fin (d + 1), μ.val < r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0) ∧
      let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
      (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 }

/-- Individual coordinate positivity condition is open (helper). -/
private theorem diffImPos_isOpen' {d k : ℕ} [NeZero d]
    (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
      (z i μ - prev μ).im > 0 } := by
  by_cases hi : i.val = 0
  · simpa [hi] using isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
  · let j : Fin k := ⟨i.val - 1, by omega⟩
    have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j))
    have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i))
    simpa [hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'

/-- `OneSliceContinuationDomain` is open. -/
theorem isOpen_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    IsOpen (OneSliceContinuationDomain d k r hr i₀) := by
  have : OneSliceContinuationDomain d k r hr i₀ =
      (⋂ i : Fin k, ⋂ μ : Fin (d + 1),
        { z : Fin k → Fin (d + 1) → ℂ |
          μ.val < r →
            let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
            (z i μ - prev μ).im > 0 }) ∩
      { z : Fin k → Fin (d + 1) → ℂ |
        let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
        (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 } := by
    ext z; simp [OneSliceContinuationDomain]
  rw [this]
  apply (isOpen_iInter_of_finite fun i : Fin k =>
    isOpen_iInter_of_finite fun μ : Fin (d + 1) => ?_).inter (diffImPos_isOpen' i₀ ⟨r, hr⟩)
  by_cases hμ : μ.val < r
  · simpa [hμ] using diffImPos_isOpen' (d := d) (k := k) i μ
  · simp [hμ]

/-- ACR(r+1) ⊆ OneSliceContinuationDomain for each i₀. -/
theorem acr_succ_subset_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    AnalyticContinuationRegion d k (r + 1) ⊆ OneSliceContinuationDomain d k r hr i₀ := by
  intro z hz
  simp only [AnalyticContinuationRegion, OneSliceContinuationDomain, Set.mem_setOf_eq] at hz ⊢
  exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- OneSliceContinuationDomain ⊆ ACR(r) for r ≥ 1. -/
theorem oneSliceContinuationDomain_subset_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r) (i₀ : Fin k) :
    OneSliceContinuationDomain d k r hr i₀ ⊆ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  intro z hz
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  exact hz.1 i μ (by omega)

/-- ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain d k r hr i₀. -/
theorem iInter_oneSliceContinuationDomain_eq_acr_succ {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) :
    (⋂ i₀ : Fin k, OneSliceContinuationDomain d k r hr i₀) =
      AnalyticContinuationRegion d k (r + 1) := by
  ext z
  simp only [Set.mem_iInter, OneSliceContinuationDomain, AnalyticContinuationRegion,
    Set.mem_setOf_eq]
  constructor
  · intro h i μ hμ
    rcases Nat.lt_or_eq_of_le hμ with hlt | rfl
    · exact (h i).1 i μ hlt
    · exact (h i).2
  · intro hz i₀
    exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- Updating the i₀-th row's r-th entry to `prev₀ ⟨r,hr⟩ + w` (with Im(w) > 0)
    lands in `OneSliceContinuationDomain d k r hr i₀`. -/
theorem sliceUpdate_mem_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (i₀ : Fin k) {w : ℂ} (hw : 0 < w.im) :
    let prev₀ : Fin (d + 1) → ℂ :=
      if _ : i₀.val = 0 then 0 else z₀ ⟨i₀.val - 1, by omega⟩
    Function.update z₀ i₀
        (Function.update (z₀ i₀) ⟨r, hr⟩ (prev₀ ⟨r, hr⟩ + w))
      ∈ OneSliceContinuationDomain d k r hr i₀ := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  have hμ_ne : (⟨r' + 1, by omega⟩ : Fin (d + 1)) ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) →
      False := fun h => h rfl
  refine ⟨fun i μ hμ => ?_, ?_⟩
  · have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) :=
        fun heq => by simp [heq] at hμ
    have h_eq : ∀ j : Fin k, Function.update z₀ i₀
        (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
          ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
            else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w)) j μ = z₀ j μ := by
      intro j
      by_cases hj : j = i₀
      · subst hj; simp [hμ_ne]
      · simp [hj]
    rw [h_eq i]
    have h_prev_eq :
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
          else Function.update z₀ i₀
            (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
              ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
                else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w))
            ⟨i.val - 1, by omega⟩) μ =
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z₀ ⟨i.val - 1, by omega⟩) μ := by
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
    rw [h_prev_eq]
    exact hz₀ i μ (by omega)
  · by_cases hi0 : i₀.val = 0
    · simpa [sub_eq_add_neg, Function.update, hi0] using hw
    · have hprev_ne : (⟨i₀.val - 1, by omega⟩ : Fin k) ≠ i₀ :=
        fun heq => absurd (congrArg Fin.val heq)
          (Nat.ne_of_lt (Nat.sub_lt (Nat.pos_of_ne_zero hi0) one_pos))
      simpa [sub_eq_add_neg, Function.update, hi0, hprev_ne, add_assoc, add_left_comm, add_comm]
        using hw


/-- **Domain restriction lemma: ACR(r+1) ⊆ ACR(r) (r ≥ 1).**

    This is a RESTRICTION lemma, not the OS II continuation step. Because
    ACR(r+1) ⊆ ACR(r) for r ≥ 1, any function holomorphic on ACR(r) is also
    holomorphic on ACR(r+1) by restriction (S_ext := S_prev).

    **This is NOT the full OS II argument.** The true OS II inductive step for r ≥ 1
    would extend holomorphicity to `OneSliceContinuationDomain`, which lies strictly
    between ACR(r+1) and ACR(r): `ACR(r+1) ⊆ OneSlice ⊆ ACR(r)`. Since OneSlice ⊆ ACR(r),
    a restriction argument suffices for holomorphicity on OneSlice, but not for the
    Paley-Wiener boundary value behavior needed to assemble the full OS continuation.
    The genuinely non-trivial OS II step is the base case r=0→1 (handled by
    `schwinger_continuation_base_step`), where ACR(0) (Im=0) and ACR(1) (Im>0)
    are disjoint and a Laplace/Paley-Wiener argument is indispensable.

    Ref: OS II, Theorem 4.1 (the domain inclusions) -/
theorem restrict_holomorphic_to_acr_succ {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (_ : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z :=
  ⟨S_prev, hS_prev.mono (acr_succ_subset hr_pos), fun _ _ => rfl⟩


/-- **Inductive continuation for `r ≥ 1` (OS II, Theorem 4.1).**

    Once the base-step has produced a holomorphic witness on `C_k^(1)`, every further
    stage `C_k^(r+1) ⊆ C_k^(r)` is obtained by restriction. The genuinely non-trivial
    analytic continuation is therefore concentrated in `schwinger_continuation_base_step`;
    this theorem is only the monotonicity step for the nested domains.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem inductive_analytic_continuation {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (hr : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z := by
  exact restrict_holomorphic_to_acr_succ k r hr hr_pos S_prev hS_prev

/-! ### Full analytic continuation from Euclidean to forward tube

After the base step, the active reconstruction chain already produces a holomorphic
witness on `C_k^(1)`, and `ForwardTube d k ⊆ C_k^(1)`. So the forward-tube existence
statement used below no longer depends on the separate Bochner route from
`C_k^(d+1)`.

The older Bochner approach from `C_k^(d+1)` remains mathematically interesting, but
it is not part of the active OS→Wightman pipeline here. The naive
"common SO(d+1)-orbit of the positive orthant, then convex hull" story is false, so
that side development needs a different geometric input before it can be reinstated.

Ref: OS II, Sections IV-V; Vladimirov Section 20.2 -/

/-- The forward tube already lies inside the first-step continuation region `C_k^(1)`,
    since each forward-cone difference has positive time component. -/
private theorem forwardTube_subset_acr_one {d k : ℕ} [NeZero d] :
    ForwardTube d k ⊆ AnalyticContinuationRegion d k 1 := by
  intro z hz
  rw [forwardTube_eq_imPreimage] at hz
  simp only [ForwardConeAbs, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  have htime :
      0 <
        ((z i 0).im -
          ((if h : i.val = 0 then (0 : Fin (d + 1) → ℝ)
            else fun ν => (z ⟨i.val - 1, by omega⟩ ν).im) 0)) := (hz i).1
  subst hμ0
  have htime' :
      ((if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z ⟨i.val - 1, by omega⟩) 0).im <
        (z i 0).im := by
    by_cases hi : i.val = 0
    · simpa [hi, sub_pos] using htime
    · simpa [hi, sub_pos] using htime
  simpa [Complex.sub_im, sub_pos] using htime'

/-- Iterate analytic continuation from the base-step witness on `C_k^(1)` to `C_k^(d+1)`.

    The real analytic continuation starts at `r = 1`, not `r = 0`: the base-step
    theorem `schwinger_continuation_base_step` produces the first holomorphic witness
    on `ACR(1)` directly from the Schwinger functional. For `r ≥ 1`, all further steps
    are restrictions along the inclusions `ACR(r+1) ⊆ ACR(r)`.

    This avoids treating `ACR(0)` as an open complex holomorphic domain and removes
    the need for a separate pointwise "base-region kernel" theorem.

    Ref: OS II, Theorem 4.1 -/
theorem iterated_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_rep⟩ := schwinger_continuation_base_step OS lgc k
  -- Invariant for r ≥ 1: holomorphicity on ACR(r) and preservation of the
  -- Euclidean pairing identity with OS.S.
  let P : ℕ → Prop := fun s =>
    ∃ (S_r : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_r (AnalyticContinuationRegion d k (s + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_r (fun j => wickRotatePoint (x j)) * (f.1 x))
  have hP0 : P 0 := ⟨S₁, hS₁_hol, hS₁_rep⟩
  have hstep : ∀ s, s + 1 < d + 1 → P s → P (s + 1) := by
    intro s hs hPs
    have hs_pos : 0 < s + 1 := Nat.succ_pos s
    rcases hPs with ⟨S_r, hS_r_hol, hS_r_rep⟩
    exact ⟨S_r, hS_r_hol.mono (acr_succ_subset hs_pos), hS_r_rep⟩
  have hP_all : ∀ s, s + 1 ≤ d + 1 → P s := by
    intro s hsle
    induction s with
    | zero =>
        exact hP0
    | succ s ih =>
        have hslt : s + 1 < d + 1 := by omega
        have hsle' : s + 1 ≤ d + 1 := by omega
        exact hstep (s := s) hslt (ih hsle')
  rcases hP_all d (by simp) with ⟨S_ext, hS_ext_hol, hS_ext_rep⟩
  exact ⟨S_ext, hS_ext_hol, hS_ext_rep⟩

theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid⟩ := schwinger_continuation_base_step OS lgc k
  refine ⟨S₁, hS₁_hol.mono (forwardTube_subset_acr_one (d := d) (k := k)), hS₁_euclid⟩

private theorem differentiableOn_flatten_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n)) :
    DifferentiableOn ℂ (F ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.TubeDomain (ForwardConeFlat d n)) := by
  rw [← forwardTube_flatten_eq_tubeDomain]
  refine hF.comp (flattenCLEquiv n (d + 1)).symm.differentiableOn (fun w hw => ?_)
  obtain ⟨z, hz, rfl⟩ := hw
  convert hz using 1
  exact (flattenCLEquiv n (d + 1)).symm_apply_apply z

private theorem boundary_values_tempered_of_flatTempered {d : ℕ} [NeZero d]
    (n : ℕ)
    {F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F_analytic (ForwardTube d n))
    (hTempered : SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d n)
      (F_analytic ∘ (flattenCLEquiv n (d + 1)).symm)) :
    ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W f)) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F_analytic ∘ e.symm
  let pushforward : SchwartzNPoint d n →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm
  have hG_hol : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten_forwardTube hF_hol
  have hdist_lin :
      IsLinearMap ℂ hTempered.dist :=
    SCV.fourierLaplace_dist_isLinearMap_tempered
      (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n)
      (forwardConeFlat_nonempty d n)
      (forwardConeFlat_isCone d n)
      hG_hol hTempered
  let W : SchwartzNPoint d n →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun f => hTempered.dist (pushforward f)
          map_add' := fun f g => by
            rw [map_add]
            exact hdist_lin.map_add _ _
          map_smul' := fun c f => by
            rw [map_smul]
            exact hdist_lin.map_smul _ _ }
      cont := hTempered.dist_continuous.comp pushforward.continuous }
  refine ⟨W, ?_⟩
  intro f η hη
  have hηflat : eR η ∈ ForwardConeFlat d n :=
    ⟨η, (inForwardCone_iff_mem_forwardConeAbs η).mp hη, rfl⟩
  have hflat :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (hTempered.dist (pushforward f))) :=
    hTempered.boundary_value (pushforward f) (eR η) hηflat
  have hEq :
      (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
          G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))
      =
      (fun ε : ℝ =>
        ∫ y : NPointDomain d n,
          F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) * (f y)) := by
    funext ε
    rw [integral_flatten_change_of_variables n (d + 1)
      (fun x : Fin (n * (d + 1)) → ℝ =>
        G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))]
    congr 1
    ext y
    have hFarg :
        G (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I) =
          F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) := by
      change F_analytic (e.symm (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I)) =
        F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I)
      congr 1
      ext k μ
      have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
        simp [eR, flattenCLEquivReal_apply]
      have hηk : eR η (finProdFinEquiv (k, μ)) = η k μ := by
        simp [eR, flattenCLEquivReal_apply]
      rw [show (e.symm (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I)) k μ =
          (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I) (finProdFinEquiv (k, μ)) by
            simp [e, flattenCLEquiv_symm_apply]]
      simp [hyk, hηk]
    have hfarg : pushforward f (eR y) = f y := by
      simp [pushforward, eR]
    rw [hFarg, hfarg]
  rw [hEq] at hflat
  simpa [W, G, pushforward] using hflat

/-! ### Phase 4: Tempered boundary values

**Critical**: E0' (linear growth condition) is essential for temperedness.
Without growth control, boundary values might fail to be tempered
(the gap in OS I Lemma 8.8). E0' gives |W_n(f)| <= C_n * ||f||_{s,n}
where C_n has at most factorial growth.

Ref: OS II, Section VI -/

/--
The continuous-linear boundary-value witness is no longer the missing part of
Phase 4. Once the flattened continuation carries an honest tempered Fourier-Laplace
boundary-value package, `boundary_values_tempered_of_flatTempered` transports it
back to `NPointDomain` and constructs the required continuous linear functional.

So the remaining content here is exactly the theorem producing that honest tempered
flattened package for the specific `F_analytic` supplied by
`full_analytic_continuation`.
-/

theorem boundary_values_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- W_n is continuous (tempered distribution)
      Continuous W_n ∧
      -- W_n is linear
      IsLinearMap ℂ W_n ∧
      -- F_analytic is holomorphic on the forward tube
      DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
      -- Boundary values of F_analytic give W_n
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n f))) ∧
      -- Euclidean restriction of F_analytic gives S_n on the corrected OS test space.
      (∀ (f : ZeroDiagonalSchwartz d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x)) := by
  obtain ⟨F_analytic, hF_hol, hF_euclid⟩ := full_analytic_continuation OS lgc n
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ :=
    F_analytic ∘ (flattenCLEquiv n (d + 1)).symm
  have hG_hol : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten_forwardTube hF_hol
  -- Remaining content, now stated explicitly rather than hidden inside a structure:
  -- construct the flattened boundary distribution together with the two honest
  -- OS-II growth bounds. Those four fields are exactly what is needed to build
  -- `HasFourierLaplaceReprTempered` and hence the tempered Wightman boundary value.
  obtain ⟨Tflat, hTflat_cont, hBVflat, hpoly, hunif⟩ :
      ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ → ℂ),
        Continuous Tflat ∧
        (∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
            (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
            Filter.Tendsto (fun ε : ℝ =>
              ∫ x : Fin (n * (d + 1)) → ℝ,
                G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (Tflat f))) ∧
        (∀ (K : Set (Fin (n * (d + 1)) → ℝ)), IsCompact K → K ⊆ ForwardConeFlat d n →
          ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
            ∀ (x y : Fin (n * (d + 1)) → ℝ), y ∈ K →
              ‖G (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ ≤ C_bd * (1 + ‖x‖) ^ N) ∧
        (∀ (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
          ∃ (C_bd : ℝ) (N : ℕ) (δ : ℝ), C_bd > 0 ∧ δ > 0 ∧
            ∀ (x : Fin (n * (d + 1)) → ℝ) (ε : ℝ), 0 < ε → ε < δ →
              ‖G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖ ≤ C_bd * (1 + ‖x‖) ^ N) := by
    sorry
  let hTempered :
      SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d n) G :=
    SCV.exists_fourierLaplaceReprTempered
      (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n)
      (forwardConeFlat_nonempty d n)
      hG_hol hTflat_cont hBVflat hpoly hunif
  obtain ⟨W, hW_bv⟩ :=
    boundary_values_tempered_of_flatTempered (d := d) n hF_hol (by simpa [G] using hTempered)
  refine ⟨W, F_analytic, W.continuous, ?_, hF_hol, hW_bv, fun f => hF_euclid f⟩
  constructor
  · intro f g
    exact map_add W f g
  · intro c f
    exact map_smul W c f

/-! ### Constructing WightmanFunctions from OS Data

Each Wightman axiom is derived from the corresponding OS axiom via analytic
continuation. The helper lemmas below capture each derivation. -/

/-- The n-point Wightman distribution `W_n` extracted from `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, Continuous W_n ∧ IsLinearMap ℂ W_n ∧ ...`.
    This definition extracts `W_n` via `.choose` (the first existential witness).

    `W_n` is the tempered distributional boundary value of the analytically continued
    function `F_analytic` on the forward tube. It is continuous (tempered) and linear.

    Note: `boundary_values_tempered` is deferred in this file, so `bvt_W` and
    downstream properties remain contingent on that theorem. -/
def bvt_W (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    SchwartzNPoint d n → ℂ :=
  (boundary_values_tempered OS lgc n).choose

/-- The holomorphic function `F_analytic` on the forward tube, extracted from
    `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, ... ∧ DifferentiableOn ℂ F_analytic
    (ForwardTube d n) ∧ ...`. This definition extracts `F_analytic` via
    `.choose_spec.choose` (the second existential witness, nested inside the first).

    `F_analytic` is holomorphic on `ForwardTube d n`, its distributional boundary values
    recover `bvt_W` (the Wightman distribution), and its Euclidean restriction
    (via Wick rotation) recovers the Schwinger functions `OS.S n`.

    Note: `boundary_values_tempered` is deferred in this file, so `bvt_F` and
    downstream properties remain contingent on that theorem. -/
def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (boundary_values_tempered OS lgc n).choose_spec.choose

theorem bvt_W_continuous (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    Continuous (bvt_W OS lgc n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1

theorem bvt_F_holomorphic (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    DifferentiableOn ℂ (bvt_F OS lgc n) (ForwardTube d n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.1

theorem bvt_boundary_values (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n f)) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.1

theorem bvt_euclidean_restriction (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (f.1 x) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.2

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n

Each bvt_* property follows a three-step transfer:
1. OS axiom (E0-E4) gives a property of S_n
2. S_n = F_analytic ∘ wickRotate (Euclidean restriction) transfers to F_analytic
3. W_n = BV(F_analytic) (boundary value) transfers to W_n

The following helpers isolate the transfer steps as smaller sorry targets. -/

/-- E2R normalization: The 0-point BV is evaluation at the origin.

    For n = 0, the domain Fin 0 → Fin (d+1) → ℝ is a zero-dimensional space
    (a single point). The forward tube ForwardTube d 0 is all of the (trivial)
    domain. The analytic function F_analytic is a constant. The BV condition
    reduces to: the constant value times f(0) = W_0(f), so W_0(f) = c * f(0).
    Combining with the OS normalization (S_0 is normalized by the Euclidean
    restriction), we get c = 1, hence W_0(f) = f(0).

    This requires: (1) identifying the integral over the zero-dimensional space,
    (2) the OS normalization condition S_0(f) = f(0). -/
theorem bv_zero_point_is_evaluation (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W_0 : SchwartzNPoint d 0 → ℂ)
    (F_0 : (Fin 0 → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
      InForwardCone d 0 η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_0 f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f.1 x)) :
    ∀ f : SchwartzNPoint d 0, W_0 f = f 0 := by
  intro f
  let η0 : Fin 0 → Fin (d + 1) → ℝ := fun k => Fin.elim0 k
  have hη0 : InForwardCone d 0 η0 := by
    intro k
    exact Fin.elim0 k
  set I0 : ℂ := ∫ x : Fin 0 → Fin (d + 1) → ℝ,
      F_0 (fun k => wickRotatePoint (x k)) * (f x)
  have hconst :
      ∀ ε : ℝ,
        (∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) * (f x)) = I0 := by
    intro ε
    unfold I0
    congr 1
    ext x
    have hz : (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) =
        (fun k => wickRotatePoint (x k)) := by
      funext k
      exact Fin.elim0 k
    simp [hz]
  have hBV0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W_0 f)) := by
    simpa [hconst] using hBV f η0 hη0
  have hI0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I0) :=
    tendsto_const_nhds
  have hW0 : W_0 f = I0 :=
    tendsto_nhds_unique hBV0 hI0
  let f0 : ZeroDiagonalSchwartz d 0 := ⟨f, by
    intro k x hx
    rcases hx with ⟨i, _, _, _⟩
    exact Fin.elim0 i⟩
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f0 := by simpa [I0, f0] using (hEuclid f0).symm
    _ = f 0 := lgc.normalized_zero f0

/-- E2R translation: Translation invariance transfers from S_n (via E1) through
    the analytic continuation to the BV.

    The argument: E1 says S_n is translation-invariant. The Euclidean restriction
    shows F_analytic is translation-invariant at Euclidean points. By analytic
    continuation, F_analytic is translation-invariant on the forward tube. The BV
    limit preserves translation invariance. -/
theorem bv_translation_invariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_cont : Continuous W_n)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE1 : ∀ (a : SpacetimeDim d) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x i + a)) →
      OS.S n f = OS.S n g) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  -- Proof sketch: From hEuclid and hE1, F_n(wick(x)) = F_n(wick(x-a)) for all x, so F_n is
  -- invariant under the Euclidean shift wick_a = (i*a_0, a_1, ..., a_d).
  -- By distributional_uniqueness_forwardTube, F_n(z) = F_n(z - wick_a) on all of FT.
  -- The BV limit W_n(g) = lim ∫ F_n(x + iεη) f(x+a) dx = lim ∫ F_n(y - a + iεη) f(y) dy,
  -- and y - a + iεη = y - wick_a + iεη (up to the i*a_0 time component cancellation) — but
  -- this identification fails because a_0 ≠ i*a_0 (real vs imaginary time shift).
  -- Full proof requires the analytic continuation infrastructure (BHW + OS II Section VI).
  sorry

/-- E2R Lorentz: Lorentz covariance transfers from E1 (Euclidean rotation
    invariance) through BHW to the BV.

    The argument: E1 gives SO(d+1)-invariance of S_n. The analytic continuation
    extends this to SO(d+1,C)-invariance of F_analytic. The restricted Lorentz
    group SO+(1,d) embeds in SO(d+1,C) (Bargmann-Hall-Wightman), giving
    real Lorentz invariance of F_analytic. The BV preserves this invariance. -/
theorem bv_lorentz_covariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE1_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
      OS.S n f = OS.S n g) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  sorry

/-- E2R locality: Local commutativity transfers from E3 (permutation symmetry)
    + edge-of-the-wedge to the BV.

    The argument: E3 says S_n is permutation-symmetric. The Euclidean restriction
    shows F_analytic is permutation-symmetric at Euclidean points. By analytic
    continuation (Jost's theorem), this extends to the permuted extended tube.
    Edge-of-the-wedge at the boundary gives local commutativity of W_n. -/
theorem bv_local_commutativity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hE3 : ∀ (σ : Equiv.Perm (Fin n)) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
      OS.S n f = OS.S n g) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  sorry

/-- E2R positivity: Positive definiteness transfers from E2 (reflection positivity)
    through the Wick rotation.

    The argument: The Wightman inner product sum_{n,m} W_{n+m}(f*_n x f_m) is
    related to the OS inner product sum_{n,m} S_{n+m}(theta(f*_n) x f_m) by
    analytic continuation. E2 ensures the OS inner product is non-negative,
    hence the Wightman inner product is non-negative. -/
theorem bv_positive_definiteness_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_eq : ∀ n, W n = bvt_W OS lgc n)
    (hE2 : ∀ (F : BorchersSequence d),
      (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) →
      (OSInnerProduct d OS.S F F).re ≥ 0) :
    ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0 := by
  sorry

/-- E2R Hermiticity: Hermiticity of W_n from reality of Schwinger functions.

    The Schwinger functions are real-valued on real configurations. Under
    analytic continuation, this gives a Schwarz reflection principle for
    F_analytic. Taking BV, this yields the Hermiticity condition
    W_n(f~) = conj(W_n(f)). -/
theorem bv_hermiticity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  sorry

/-- S44: W_0 = 1 (normalization).
    The 0-point Schwinger function S_0 = 1 (OS normalization). Its analytic
    continuation is the constant function 1 on the (trivial) forward tube.
    The distributional BV of 1 is evaluation: W_0(f) = f(0). -/
theorem bvt_normalized (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsNormalized d (bvt_W OS lgc) := by
  intro f
  exact bv_zero_point_is_evaluation OS lgc
    (bvt_W OS lgc 0)
    (bvt_F OS lgc 0)
    (bvt_boundary_values OS lgc 0)
    (bvt_euclidean_restriction OS lgc 0)
    f

/-- S45: Translation invariance of W_n from E1. -/
theorem bvt_translation_invariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (bvt_W OS lgc) := by
  intro n a f g hfg
  exact bv_translation_invariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_W_continuous OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_translation_invariant n)
    a f g hfg

/-- S46: Lorentz covariance of W_n from E1 via BHW. -/
theorem bvt_lorentz_covariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (bvt_W OS lgc) := by
  intro n Λ f g hfg
  exact bv_lorentz_covariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_rotation_invariant n)
    Λ f g hfg

/-- S47: Local commutativity of W_n from E3 + edge-of-the-wedge. -/
theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bv_local_commutativity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (OS.E3_symmetric n)
    i j f g hsupp hswap

/-- S48: Positive definiteness of W_n from E2 (reflection positivity). -/
theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsPositiveDefinite d (bvt_W OS lgc) := by
  exact bv_positive_definiteness_transfer OS lgc
    (bvt_W OS lgc)
    (fun _ => rfl)
    OS.E2_reflection_positive

/-- S49: Hermiticity of W_n from reality of Schwinger functions. -/
theorem bvt_hermitian (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  intro n f g hfg
  exact bv_hermiticity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    f g hfg

/-- The cluster property (R4) for the reconstructed Wightman functions.

    The cluster property of the boundary value distributions W_n follows from the
    cluster property E4 of the Schwinger functions via analytic continuation.

    The proof lifts E4 (distributional cluster in Euclidean space) to the Minkowski
    boundary values using the boundary value correspondence: the spatial translations
    commute with the Wick rotation, so the Euclidean factorization at large spacelike
    separation passes to the Minkowski distributional boundary values.

    Ref: OS I (1973), Section 5; OS II (1975), Section VI -/
theorem bvt_cluster (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  sorry

/-- Given OS axioms with linear growth condition, construct the full collection
    of Wightman functions from the analytic continuation boundary values. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := bvt_W OS lgc
  linear := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.1
  tempered := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1
  normalized := bvt_normalized OS lgc
  translation_invariant := bvt_translation_invariant OS lgc
  lorentz_covariant := bvt_lorentz_covariant OS lgc
  spectrum_condition := by
    intro n
    have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
    exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
      h.2.2.1, h.2.2.2.1⟩
  locally_commutative := bvt_locally_commutative OS lgc
  positive_definite := bvt_positive_definite OS lgc
  hermitian := bvt_hermitian OS lgc
  cluster := bvt_cluster OS lgc

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    data.

    This is the honest Euclidean quotient:
    positive-time Borchers sequences modulo the null space of the OS inner
    product. It does not presuppose the reconstructed Wightman distributions.

    The linear growth condition is *not* part of this definition. It enters only
    later, at the analytic continuation stage needed to construct full tempered
    Wightman boundary values from the Euclidean OS data. -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d) :=
  OSPreHilbertSpace OS

/-! ### The Bridge Theorems -/

/-- **Theorem R→E**: Wightman functions produce the honest zero-diagonal
    Euclidean Schwinger family on `°S`.

    This is intentionally weaker than the OS-II full-Schwartz surface:
    the raw Wick-rotated pairing is only packaged on `ZeroDiagonalSchwartz`,
    together with continuity there and the Wick-rotation relation to the
    Wightman boundary values. No `OSLinearGrowthCondition` is assumed in this
    direction. -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  intro n
  -- Use the BHW extension F_ext as the zero-diagonal Wick-rotation witness.
  -- F_ext = BHW extension, holomorphic on PET (hence on the forward tube).
  -- Its boundary values agree with W_n since F_ext = W_analytic on the forward tube.
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · -- Boundary values: use bhw_distributional_boundary_values directly.
    -- The previous approach tried to show x + iεη ∈ ForwardTube, which is false
    -- due to coordinate convention mismatch (absolute vs difference coordinates).
    intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

/-- **Theorem E'→R'** (OS II surface): OS axioms together with the linear growth
    condition produce Wightman functions.

    This direction intentionally keeps the stronger OS-II hypothesis
    `OSLinearGrowthCondition`; it is the ingredient that repairs the OS-I gap
    in the reconstruction of tempered Wightman boundary values. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the honest zero-diagonal
      -- Schwinger family carried by `OS`.
      IsWickRotationPair OS.schwinger Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  -- The analytic continuation, boundary values, and euclidean restriction are
  -- exactly the fields constructed inside `boundary_values_tempered`.
  have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
  exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
    h.2.2.1, h.2.2.2.1, fun f => by
      simpa [OsterwalderSchraderAxioms.schwinger] using h.2.2.2.2 f⟩

/-! ### Wired Corollaries

The theorem wiring to canonical names now lives in
`Wightman/Reconstruction/Main.lean`. The `_full` theorems above remain the
implementation-level results used by that wiring layer. -/

end
