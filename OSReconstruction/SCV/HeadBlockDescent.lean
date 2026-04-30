/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.HeadFiberAntiderivDecay
import OSReconstruction.SCV.SchwartzPartialEval
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Head-block descent

This file starts the pure SCV quotient descent for head-translation-invariant
Schwartz functionals.  The checked content here is the one-coordinate descent
through `sliceIntegral`, using the completed head-fiber antiderivative package.
-/

noncomputable section

open scoped SchwartzMap Topology LineDeriv
open MeasureTheory SchwartzMap LineDeriv

namespace SCV

/-- A continuous Schwartz functional on `Fin (n + 1) → ℝ` is invariant under
translations of the distinguished head coordinate. -/
def IsHeadTranslationInvariantSchwartzCLM {n : ℕ}
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ a : ℝ, T.comp (translateSchwartzCLM (Fin.cons a 0)) = T

/-- Head-translation-invariant Schwartz functionals annihilate the head
directional derivative. -/
theorem map_lineDeriv_eq_zero_of_headTranslationInvariant {n : ℕ}
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (f : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    T (LineDeriv.lineDerivOp ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) f) = 0 := by
  let e0 : Fin (n + 1) → ℝ := Pi.single 0 1
  have hquot :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (translateSchwartz (t • e0) f - f)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (T (LineDeriv.lineDerivOp e0 f))) :=
    (T.continuous.tendsto (LineDeriv.lineDerivOp e0 f)).comp
      (tendsto_diffQuotient_translateSchwartz_zero f e0)
  have hzero :
      Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds 0) :=
    tendsto_const_nhds
  have he0 : ∀ t : ℝ, t • e0 = Fin.cons t 0 := by
    intro t
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [e0]
    · intro j
      simp [e0]
  have heq :
      (fun t : ℝ => T (t⁻¹ • (translateSchwartz (t • e0) f - f))) =
        fun _ => (0 : ℂ) := by
    funext t
    have htrans : T (translateSchwartz (t • e0) f) = T f := by
      have := congrArg
        (fun S : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ => S f)
        (hT t)
      simpa [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply, he0 t] using this
    rw [T.map_smul_of_tower, map_sub, sub_eq_zero.mpr htrans]
    simp
  have hzero' :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (translateSchwartz (t • e0) f - f)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa only [heq] using hzero
  exact tendsto_nhds_unique hquot hzero'

/-- A Schwartz test with zero head slice integral lies in the kernel of every
head-translation-invariant functional. -/
theorem map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant {n : ℕ}
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : sliceIntegral F = 0) :
    T F = 0 := by
  have hzero' : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0 := by
    intro y
    have hy := congrArg (fun G : SchwartzMap (Fin n → ℝ) ℂ => G y) hzero
    simpa [sliceIntegral_apply, sliceIntegralRaw] using hy
  have hderiv :
      LineDeriv.lineDerivOp ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)
        (headFiberAntideriv F hzero') = F :=
    lineDerivOp_headFiberAntideriv F hzero'
  rw [← hderiv]
  exact map_lineDeriv_eq_zero_of_headTranslationInvariant T hT
    (headFiberAntideriv F hzero')

/-- Two Schwartz tests with the same head slice integral are indistinguishable
to any head-translation-invariant functional. -/
theorem map_eq_of_sliceIntegral_eq_of_headTranslationInvariant {n : ℕ}
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (F G : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hFG : sliceIntegral F = sliceIntegral G) :
    T F = T G := by
  have hFG' : sliceIntegral (F - G) = 0 := by
    rw [sliceIntegral_sub, hFG, sub_self]
  have hsub : T (F - G) = 0 :=
    map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant T hT (F - G) hFG'
  exact sub_eq_zero.mp <| by simpa [map_sub] using hsub

/-- A concrete normalized one-dimensional Schwartz bump. -/
def normedUnitBumpSchwartz : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

set_option linter.unnecessarySimpa false in
/-- The concrete head bump has integral one. -/
theorem integral_normedUnitBumpSchwartz :
    ∫ x : ℝ, normedUnitBumpSchwartz x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have happly :
      (fun x : ℝ => normedUnitBumpSchwartz x) =
        fun x : ℝ => ((b.normed MeasureTheory.volume x : ℝ) : ℂ) := by
    funext x
    have hf_smooth : ContDiff ℝ (⊤ : ENat)
        (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) := by
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
    have hf_compact :
        HasCompactSupport (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) :=
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
    simpa [normedUnitBumpSchwartz, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

/-- Descend a head-translation-invariant functional to the tail Schwartz space by
prepending a fixed head cutoff. -/
def headTranslationDescentCLM {n : ℕ}
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
  T.comp (prependFieldCLMRight φ)

/-- If the head cutoff `φ` is normalized by `∫ φ = 1`, then a
head-translation-invariant functional factors through `sliceIntegral` via
`headTranslationDescentCLM T φ`. -/
theorem map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant {n : ℕ}
    (T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadTranslationInvariantSchwartzCLM T)
    (φ : SchwartzMap ℝ ℂ)
    (hφ : ∫ x : ℝ, φ x = 1)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    T F = headTranslationDescentCLM T φ (sliceIntegral F) := by
  refine map_eq_of_sliceIntegral_eq_of_headTranslationInvariant T hT F
    (prependField φ (sliceIntegral F)) ?_
  simpa [headTranslationDescentCLM, prependFieldCLMRight_apply] using
    (sliceIntegral_prependField_eq_self φ (sliceIntegral F) hφ).symm

/-- Reindex a finite Euclidean block `Fin a → ℝ` along an equality `a = b`. -/
abbrev castFinCLE {a b : ℕ} (h : a = b) : (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b => ℝ) (finCongr h)

/-- Reindex a Schwartz function along an equality of finite index sets. -/
abbrev reindexSchwartzFin {a b : ℕ} (h : a = b) :
    SchwartzMap (Fin a → ℝ) ℂ →L[ℂ] SchwartzMap (Fin b → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (castFinCLE h).symm

@[simp]
theorem reindexSchwartzFin_apply {a b : ℕ} (h : a = b)
    (F : SchwartzMap (Fin a → ℝ) ℂ) (x : Fin b → ℝ) :
    reindexSchwartzFin h F x = F ((castFinCLE h).symm x) :=
  rfl

@[simp]
theorem castFinCLE_symm_apply {a b : ℕ} (h : a = b)
    (x : Fin b → ℝ) (i : Fin a) :
    (castFinCLE h).symm x i = x ((finCongr h) i) :=
  rfl

@[simp]
theorem castFinCLE_apply {a b : ℕ} (h : a = b)
    (x : Fin a → ℝ) (i : Fin b) :
    castFinCLE h x i = x ((finCongr h).symm i) :=
  rfl

/-- Fix the tail block of a flat head/tail Schwartz map. -/
def fixedTailHeadSection {m n : ℕ}
    (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) (u : Fin n → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  schwartzPartialEval₂
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finAppendCLE m n)) F) u

@[simp]
theorem fixedTailHeadSection_apply {m n : ℕ}
    (F : SchwartzMap (Fin (m + n) → ℝ) ℂ)
    (u : Fin n → ℝ) (t : Fin m → ℝ) :
    fixedTailHeadSection F u t = F (Fin.append t u) := by
  change F (finAppendCLE m n (t, u)) = F (Fin.append t u)
  congr 1

@[simp]
theorem castFinCLE_symm_succ_add_cons_append {m n : ℕ}
    (x : ℝ) (s : Fin m → ℝ) (u : Fin n → ℝ) :
    (castFinCLE (Nat.succ_add m n)).symm (Fin.cons x (Fin.append s u)) =
      (Fin.append (Fin.cons x s) u : Fin ((m + 1) + n) → ℝ) := by
  ext i
  refine Fin.addCases (motive := fun i =>
    (castFinCLE (Nat.succ_add m n)).symm (Fin.cons x (Fin.append s u)) i =
      (Fin.append (Fin.cons x s) u : Fin ((m + 1) + n) → ℝ) i) ?_ ?_ i
  · intro j
    refine Fin.cases ?_ ?_ j
    · have hcast :
          (finCongr (Nat.succ_add m n)) (Fin.castAdd n (0 : Fin (m + 1))) = 0 := by
        apply Fin.ext
        simp
      rw [castFinCLE_symm_apply, hcast]
      simp
    · intro k
      have hcast :
          (finCongr (Nat.succ_add m n)) (Fin.castAdd n k.succ) =
            (Fin.castAdd n k).succ := by
        apply Fin.ext
        simp
      rw [castFinCLE_symm_apply, hcast]
      simp [Fin.append]
  · intro j
    have hcast :
        (finCongr (Nat.succ_add m n)) (Fin.natAdd (m + 1) j) =
          (Fin.natAdd m j).succ := by
      apply Fin.ext
      simp
      omega
    rw [castFinCLE_symm_apply, hcast]
    simp [Fin.append]

/-- The direct finite-dimensional `integrateHeadBlock` agrees with the
recursive one-head-at-a-time slice integral after the `Nat.succ_add` reindexing.
-/
theorem integrateHeadBlock_sliceIntegral_reindex {m n : ℕ}
    (F : SchwartzMap (Fin ((m + 1) + n) → ℝ) ℂ) :
    integrateHeadBlock (m := m) (n := n)
      (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) =
    integrateHeadBlock (m := m + 1) (n := n) F := by
  ext u
  have h := integral_sliceIntegralRaw (F := fixedTailHeadSection F u)
  simpa [integrateHeadBlock_apply_finAppend, sliceIntegral_apply, sliceIntegralRaw,
    fixedTailHeadSection_apply, reindexSchwartzFin_apply,
    castFinCLE_symm_succ_add_cons_append] using h

@[simp]
theorem headBlockShift_zero {m n : ℕ} :
    headBlockShift m n (0 : Fin m → ℝ) = 0 := by
  ext i
  refine Fin.addCases (motive := fun i =>
    headBlockShift m n (0 : Fin m → ℝ) i = (0 : Fin (m + n) → ℝ) i) ?_ ?_ i
  · intro j
    simp [headBlockShift]
  · intro j
    simp [headBlockShift]

private theorem integral_fin_zero (f : (Fin 0 → ℝ) → ℂ) :
    ∫ t : Fin 0 → ℝ, f t = f default := by
  rw [MeasureTheory.Measure.volume_pi_eq_dirac
    (ι := Fin 0) (α := fun _ => ℝ) (x := default)]
  simp

@[simp]
theorem finAppend_zero_castFinCLE {n : ℕ} (x : Fin (0 + n) → ℝ) :
    Fin.append (default : Fin 0 → ℝ) (castFinCLE (Nat.zero_add n) x) = x := by
  ext i
  refine Fin.addCases (motive := fun i =>
    Fin.append (default : Fin 0 → ℝ) (castFinCLE (Nat.zero_add n) x) i = x i) ?_ ?_ i
  · intro j
    exact Fin.elim0 j
  · intro j
    rw [Fin.append_right]
    have hcast : (finCongr (Nat.zero_add n)).symm j = Fin.natAdd 0 j := by
      apply Fin.ext
      simp
    rw [castFinCLE_apply, hcast]

theorem reindexSchwartzFin_translate_headBlockShift_succ
    {m n : ℕ} (a : Fin (m + 1) → ℝ)
    (F : SchwartzMap (Fin ((m + 1) + n) → ℝ) ℂ) :
    reindexSchwartzFin (Nat.succ_add m n)
        (translateSchwartz (headBlockShift (m + 1) n a) F) =
      translateSchwartz
        (Fin.cons (a 0) (headBlockShift m n (fun i => a i.succ)))
        (reindexSchwartzFin (Nat.succ_add m n) F) := by
  ext x
  have ha : (Fin.cons (a 0) (fun i : Fin m => a i.succ) : Fin (m + 1) → ℝ) = a := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp
  simp [reindexSchwartzFin_apply, translateSchwartz_apply, headBlockShift, ha]

theorem reindexSchwartzFin_symm_translate_headBlockShift
    {m n : ℕ} (a : Fin (m + 1) → ℝ)
    (F : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ) :
    reindexSchwartzFin (Nat.succ_add m n).symm
        (translateSchwartz
          (Fin.cons (a 0) (headBlockShift m n (fun i => a i.succ))) F) =
      translateSchwartz (headBlockShift (m + 1) n a)
        (reindexSchwartzFin (Nat.succ_add m n).symm F) := by
  let e := Nat.succ_add m n
  have hforward :=
    reindexSchwartzFin_translate_headBlockShift_succ
      (m := m) (n := n) (a := a)
      (F := reindexSchwartzFin e.symm F)
  have hback := congrArg (reindexSchwartzFin e.symm) hforward
  simpa [e] using hback.symm

theorem prependField_translate_headBlockShift
    {m n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (a : Fin m → ℝ) (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    prependField φ (translateSchwartz (headBlockShift m n a) F) =
      translateSchwartz (Fin.cons 0 (headBlockShift m n a))
        (prependField φ F) := by
  ext x
  rw [prependField_apply, translateSchwartz_apply,
    translateSchwartz_apply, prependField_apply]
  congr 1
  simp [Pi.add_apply]

/-- Descending through the first coordinate preserves translation invariance in
the remaining head block. -/
theorem headTranslationDescentCLM_headBlockInvariant
    {m n : ℕ}
    (T : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : ∀ a : Fin (m + 1) → ℝ,
      T.comp
          (translateSchwartzCLM
            (Fin.cons (a 0) (headBlockShift m n (fun i => a i.succ)))) =
        T) :
    IsHeadBlockTranslationInvariantSchwartzCLM
      (m := m) (n := n)
      (headTranslationDescentCLM T normedUnitBumpSchwartz) := by
  intro a
  ext F
  have htrans :
      headTranslationDescentCLM T normedUnitBumpSchwartz
          (translateSchwartz (headBlockShift m n a) F) =
        headTranslationDescentCLM T normedUnitBumpSchwartz F := by
    change T (prependField normedUnitBumpSchwartz
        (translateSchwartz (headBlockShift m n a) F)) =
      T (prependField normedUnitBumpSchwartz F)
    rw [prependField_translate_headBlockShift]
    have := congrArg
      (fun S : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ →L[ℂ] ℂ =>
        S (prependField normedUnitBumpSchwartz F))
      (hT (Fin.cons 0 a))
    simpa [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply] using this
  simp [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply] at htrans ⊢
  exact htrans

/-- A head-block-translation-invariant Schwartz functional depends only on the
direct finite-dimensional head-block integral. -/
theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
    {m n : ℕ}
    (T : SchwartzMap (Fin (m + n) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
    (F G : SchwartzMap (Fin (m + n) → ℝ) ℂ)
    (hFG : integrateHeadBlock (m := m) (n := n) F =
      integrateHeadBlock (m := m) (n := n) G) :
    T F = T G := by
  induction m with
  | zero =>
      have hFG' : F = G := by
        ext x
        have hx := congrArg
          (fun H : SchwartzMap (Fin n → ℝ) ℂ => H (castFinCLE (Nat.zero_add n) x)) hFG
        simp only [integrateHeadBlock_apply_finAppend] at hx
        rw [integral_fin_zero, integral_fin_zero] at hx
        rw [finAppend_zero_castFinCLE] at hx
        exact hx
      simp [hFG']
  | succ m ihm =>
      let T' :
          SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ →L[ℂ] ℂ :=
        T.comp (reindexSchwartzFin (Nat.succ_add m n).symm)
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      let G' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) G
      have hT'head :
          IsHeadTranslationInvariantSchwartzCLM T' := by
        intro a
        ext H
        change
          T (reindexSchwartzFin (Nat.succ_add m n).symm
            (translateSchwartz (Fin.cons a (0 : Fin (m + n) → ℝ)) H)) =
            T (reindexSchwartzFin (Nat.succ_add m n).symm H)
        have hreindex :
            reindexSchwartzFin (Nat.succ_add m n).symm
                (translateSchwartz (Fin.cons a (0 : Fin (m + n) → ℝ)) H) =
              translateSchwartz
                (headBlockShift (m + 1) n (Fin.cons a (fun _ : Fin m => (0 : ℝ))))
                (reindexSchwartzFin (Nat.succ_add m n).symm H) := by
          have hraw :=
            reindexSchwartzFin_symm_translate_headBlockShift
              (m := m) (n := n) (a := Fin.cons a (fun _ : Fin m => (0 : ℝ))) H
          have hshift : headBlockShift m n (fun _ : Fin m => (0 : ℝ)) = 0 := by
            exact headBlockShift_zero (m := m) (n := n)
          simpa [hshift] using hraw
        rw [hreindex]
        have := congrArg
          (fun S : SchwartzMap (Fin (m + 1 + n) → ℝ) ℂ →L[ℂ] ℂ =>
            S (reindexSchwartzFin (Nat.succ_add m n).symm H))
          (hT (Fin.cons a (fun _ : Fin m => (0 : ℝ))))
        simpa [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply] using this
      have hdesc :
          T' F' =
            headTranslationDescentCLM T' normedUnitBumpSchwartz (sliceIntegral F') := by
        simpa [T', F'] using
          map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
            T' hT'head normedUnitBumpSchwartz integral_normedUnitBumpSchwartz F'
      have hdescG :
          T' G' =
            headTranslationDescentCLM T' normedUnitBumpSchwartz (sliceIntegral G') := by
        simpa [T', G'] using
          map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
            T' hT'head normedUnitBumpSchwartz integral_normedUnitBumpSchwartz G'
      have hT'' :
          IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n)
            (headTranslationDescentCLM T' normedUnitBumpSchwartz) :=
        headTranslationDescentCLM_headBlockInvariant T' (by
          intro a
          ext H
          change
            T (reindexSchwartzFin (Nat.succ_add m n).symm
              (translateSchwartz
                (Fin.cons (a 0) (headBlockShift m n (fun i => a i.succ))) H)) =
              T (reindexSchwartzFin (Nat.succ_add m n).symm H)
          have hreindex :
              reindexSchwartzFin (Nat.succ_add m n).symm
                  (translateSchwartz
                    (Fin.cons (a 0) (headBlockShift m n (fun i => a i.succ))) H) =
                translateSchwartz
                  (headBlockShift (m + 1) n a)
                  (reindexSchwartzFin (Nat.succ_add m n).symm H) := by
            exact reindexSchwartzFin_symm_translate_headBlockShift
              (m := m) (n := n) (a := a) H
          rw [hreindex]
          have := congrArg
            (fun S : SchwartzMap (Fin (m + 1 + n) → ℝ) ℂ →L[ℂ] ℂ =>
              S (reindexSchwartzFin (Nat.succ_add m n).symm H))
            (hT a)
          simpa [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply] using this)
      have hSlices :
          integrateHeadBlock (m := m) (n := n) (sliceIntegral F') =
            integrateHeadBlock (m := m) (n := n) (sliceIntegral G') := by
        calc
          integrateHeadBlock (m := m) (n := n) (sliceIntegral F') =
              integrateHeadBlock (m := m + 1) (n := n) F := by
            simpa [F'] using integrateHeadBlock_sliceIntegral_reindex (m := m) (n := n) F
          _ = integrateHeadBlock (m := m + 1) (n := n) G := hFG
          _ = integrateHeadBlock (m := m) (n := n) (sliceIntegral G') := by
            simpa [G'] using (integrateHeadBlock_sliceIntegral_reindex (m := m) (n := n) G).symm
      have hIH :=
        ihm (T := headTranslationDescentCLM T' normedUnitBumpSchwartz) hT''
          (F := sliceIntegral F') (G := sliceIntegral G') hSlices
      have hFid :
          (reindexSchwartzFin (Nat.succ_add m n).symm) F' = F := by
        ext x
        change F (((castFinCLE (Nat.succ_add m n)).symm)
          (((castFinCLE (Nat.succ_add m n)).symm.symm) x)) = F x
        exact congrArg F ((castFinCLE (Nat.succ_add m n)).symm_apply_apply x)
      have hGid :
          (reindexSchwartzFin (Nat.succ_add m n).symm) G' = G := by
        ext x
        change G (((castFinCLE (Nat.succ_add m n)).symm)
          (((castFinCLE (Nat.succ_add m n)).symm.symm) x)) = G x
        exact congrArg G ((castFinCLE (Nat.succ_add m n)).symm_apply_apply x)
      calc
        T F = T' F' := by
          simp [T', hFid]
        _ = headTranslationDescentCLM T' normedUnitBumpSchwartz (sliceIntegral F') := hdesc
        _ = headTranslationDescentCLM T' normedUnitBumpSchwartz (sliceIntegral G') := hIH
        _ = T' G' := hdescG.symm
        _ = T G := by
          simp [T', hGid]

end SCV
