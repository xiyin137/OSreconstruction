/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.HeadFiberAntiderivDecay
import OSReconstruction.SCV.SchwartzPartialEval
import Mathlib.Analysis.Calculus.BumpFunction.Normed









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
    rfl
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

end SCV
