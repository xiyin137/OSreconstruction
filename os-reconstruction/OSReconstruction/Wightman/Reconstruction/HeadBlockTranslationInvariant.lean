/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.HeadTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import Init
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import Mathlib.Analysis.Calculus.BumpFunction.Normed

open scoped SchwartzMap

noncomputable section

namespace OSReconstruction

private def uncurryLinearEquivBlockLocal (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin n × Fin d → 𝕜) :=
  { (Equiv.curry (Fin n) (Fin d) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private def flattenLinearEquivBlockLocal (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin (n * d) → 𝕜) :=
  (uncurryLinearEquivBlockLocal n d 𝕜).trans
    (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

private def flattenCLEquivRealBlockLocal (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (flattenLinearEquivBlockLocal n d ℝ).toContinuousLinearEquiv

@[simp] private theorem flattenCLEquivRealBlockLocal_apply (n d : ℕ)
    (f : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    flattenCLEquivRealBlockLocal n d f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

private noncomputable def normedUnitBumpSchwartz : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

private theorem integral_normedUnitBumpSchwartz :
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
    change (hf_compact.toSchwartzMap hf_smooth) x = _
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

/-- A continuous Schwartz functional on `Fin (m + n) → ℝ` is head-block
translation invariant if translating only the first `m` coordinates leaves it
unchanged. -/
def IsHeadBlockTranslationInvariantSchwartzCLM {m n : ℕ}
    (T : SchwartzMap (Fin (m + n) → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ a : Fin m → ℝ, T.comp (SCV.translateSchwartzCLM (zeroTailBlockShift (m := m) (n := n) a)) = T

private theorem zeroTailBlockShift_zero {m n : ℕ} :
    zeroTailBlockShift (m := m) (n := n) (0 : Fin m → ℝ) = 0 := by
  induction m with
  | zero =>
      rfl
  | succ m ihm =>
      have hconszero :
          (Fin.cons 0 (zeroTailBlockShift (m := m) (n := n) (fun _ => 0)) :
              Fin (m + n + 1) → ℝ) = (fun _ => 0) := by
        funext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro k
          have ihm' : zeroTailBlockShift (m := m) (n := n) (fun _ => 0) = 0 := ihm
          exact congrFun ihm' k
      change zeroTailBlockShift (m := m + 1) (n := n) (fun _ => 0) = (fun _ => 0)
      rw [zeroTailBlockShift, hconszero]
      exact map_zero ((castFinCLE (Nat.succ_add m n)).symm)

private theorem reindexSchwartzFin_translate_zeroTailBlockShift_succ
    {m n : ℕ} (a : Fin (m + 1) → ℝ)
    (F : SchwartzMap (Fin ((m + 1) + n) → ℝ) ℂ) :
    reindexSchwartzFin (Nat.succ_add m n)
        (SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a) F) =
      SCV.translateSchwartz
        (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ)))
        (reindexSchwartzFin (Nat.succ_add m n) F) := by
  ext x
  simp [reindexSchwartzFin_apply, SCV.translateSchwartz_apply, zeroTailBlockShift]

private theorem reindexSchwartzFin_symm_translate_zeroTailBlockShift
    {m n : ℕ} (a : Fin (m + 1) → ℝ)
    (F : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ) :
    reindexSchwartzFin (Nat.succ_add m n).symm
        (SCV.translateSchwartz
          (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ))) F) =
      SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a)
        (reindexSchwartzFin (Nat.succ_add m n).symm F) := by
  let e := Nat.succ_add m n
  have hcancelF : reindexSchwartzFin e (reindexSchwartzFin e.symm F) = F := by
    ext x
    change F (((castFinCLE e).symm.symm) (((castFinCLE e).symm) x)) = F x
    simpa using congrArg F ((castFinCLE e).symm.apply_symm_apply x)
  have hforward :=
    reindexSchwartzFin_translate_zeroTailBlockShift_succ
      (m := m) (n := n) (a := a)
      (F := reindexSchwartzFin e.symm F)
  rw [hcancelF] at hforward
  have hback := congrArg (reindexSchwartzFin e.symm) hforward
  have hcancelTranslate :
      reindexSchwartzFin e.symm
          (reindexSchwartzFin e
            (SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a)
              (reindexSchwartzFin e.symm F))) =
        SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a)
          (reindexSchwartzFin e.symm F) := by
    ext x
    change
      SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a)
          (reindexSchwartzFin e.symm F)
          (((castFinCLE e).symm) (((castFinCLE e).symm.symm) x)) =
        SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a)
          (reindexSchwartzFin e.symm F) x
    simpa using congrArg
      (SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a)
        (reindexSchwartzFin e.symm F))
      ((castFinCLE e).symm.symm_apply_apply x)
  rw [hcancelTranslate] at hback
  exact hback.symm

private theorem prependField_translate_zeroTailBlockShift
    {m n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (a : Fin m → ℝ) (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    φ.prependField (SCV.translateSchwartz (zeroTailBlockShift (m := m) (n := n) a) F) =
      SCV.translateSchwartz (Fin.cons 0 (zeroTailBlockShift (m := m) (n := n) a))
        (φ.prependField F) := by
  ext x
  rw [SchwartzMap.prependField_apply, SCV.translateSchwartz_apply,
    SCV.translateSchwartz_apply, SchwartzMap.prependField_apply]
  congr 1
  simp [Pi.add_apply]

private theorem headTranslationDescentCLM_headBlockInvariant
    {m n : ℕ}
    (T : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : ∀ a : Fin (m + 1) → ℝ,
      T.comp
          (SCV.translateSchwartzCLM
            (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ)))) =
        T) :
    IsHeadBlockTranslationInvariantSchwartzCLM
      (m := m) (n := n)
      (headTranslationDescentCLM T normedUnitBumpSchwartz) := by
  intro a
  ext F
  have htrans :
      headTranslationDescentCLM T normedUnitBumpSchwartz
          (SCV.translateSchwartz (zeroTailBlockShift (m := m) (n := n) a) F) =
        headTranslationDescentCLM T normedUnitBumpSchwartz F := by
    change T (normedUnitBumpSchwartz.prependField
        (SCV.translateSchwartz (zeroTailBlockShift (m := m) (n := n) a) F)) =
      T (normedUnitBumpSchwartz.prependField F)
    rw [prependField_translate_zeroTailBlockShift]
    have := congrArg
      (fun S : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ →L[ℂ] ℂ =>
        S (normedUnitBumpSchwartz.prependField F))
      (hT (Fin.cons 0 a))
    simpa [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using this
  simp [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] at htrans ⊢
  exact htrans

/-- A head-block-translation-invariant Schwartz functional depends only on the
iterated head-block integral. This is the block version of the one-coordinate
factorization through `sliceIntegral`. -/
theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant
    {m n : ℕ}
    (T : SchwartzMap (Fin (m + n) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
    (F G : SchwartzMap (Fin (m + n) → ℝ) ℂ)
    (hFG : integrateHeadBlock (m := m) (n := n) F =
      integrateHeadBlock (m := m) (n := n) G) :
    T F = T G := by
  induction m with
  | zero =>
      change reindexSchwartzFin (Nat.zero_add n) F = reindexSchwartzFin (Nat.zero_add n) G at hFG
      have hFG' : F = G := by
        ext x
        have hx := congrArg
          (fun H : SchwartzMap (Fin n → ℝ) ℂ => H ((castFinCLE (Nat.zero_add n)) x)) hFG
        simpa [reindexSchwartzFin_apply] using hx
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
            (SCV.translateSchwartz (Fin.cons a 0) H)) =
            T (reindexSchwartzFin (Nat.succ_add m n).symm H)
        have hreindex :
            reindexSchwartzFin (Nat.succ_add m n).symm
                (SCV.translateSchwartz (Fin.cons a 0) H) =
              SCV.translateSchwartz
                (zeroTailBlockShift (m := m + 1) (n := n) (Fin.cons a 0))
                (reindexSchwartzFin (Nat.succ_add m n).symm H) := by
          have hzero :
              zeroTailBlockShift (m := m) (n := n) (fun _ => 0) = 0 := by
            exact zeroTailBlockShift_zero (m := m) (n := n)
          have hcons :
              (Fin.cons a (zeroTailBlockShift (m := m) (n := n) (fun _ => 0)) :
                  Fin (m + n + 1) → ℝ) =
                Fin.cons a 0 := by
            simp [hzero]
          rw [← hcons]
          convert
            reindexSchwartzFin_symm_translate_zeroTailBlockShift
              (m := m) (n := n) (a := Fin.cons a 0) H using 1 <;>
            simp [zeroTailBlockShift_zero (m := m) (n := n)]
        rw [hreindex]
        have := congrArg
          (fun S : SchwartzMap (Fin (m + 1 + n) → ℝ) ℂ →L[ℂ] ℂ =>
            S (reindexSchwartzFin (Nat.succ_add m n).symm H))
          (hT (Fin.cons a 0))
        simpa [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using this
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
              (SCV.translateSchwartz
                (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ))) H)) =
              T (reindexSchwartzFin (Nat.succ_add m n).symm H)
          have hreindex :
              reindexSchwartzFin (Nat.succ_add m n).symm
                  (SCV.translateSchwartz
                    (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ))) H) =
                SCV.translateSchwartz
                  (zeroTailBlockShift (m := m + 1) (n := n) a)
                  (reindexSchwartzFin (Nat.succ_add m n).symm H) := by
            simpa [zeroTailBlockShift] using
              reindexSchwartzFin_symm_translate_zeroTailBlockShift
                (m := m) (n := n) a H
          rw [hreindex]
          have := congrArg
            (fun S : SchwartzMap (Fin (m + 1 + n) → ℝ) ℂ →L[ℂ] ℂ =>
              S (reindexSchwartzFin (Nat.succ_add m n).symm H))
            (hT a)
          simpa [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using this)
      have hSlices :
          integrateHeadBlock (m := m) (n := n) (sliceIntegral F') =
            integrateHeadBlock (m := m) (n := n) (sliceIntegral G') := by
        simpa [integrateHeadBlock, F', G'] using hFG
      have hIH :=
        ihm (T := headTranslationDescentCLM T' normedUnitBumpSchwartz) hT''
          (F := sliceIntegral F') (G := sliceIntegral G') hSlices
      have hFid :
          (reindexSchwartzFin (Nat.succ_add m n).symm) F' = F := by
        ext x
        change F (((castFinCLE (Nat.succ_add m n)).symm) (((castFinCLE (Nat.succ_add m n)).symm.symm) x)) = F x
        simpa using congrArg F ((castFinCLE (Nat.succ_add m n)).symm_apply_apply x)
      have hGid :
          (reindexSchwartzFin (Nat.succ_add m n).symm) G' = G := by
        ext x
        change G (((castFinCLE (Nat.succ_add m n)).symm) (((castFinCLE (Nat.succ_add m n)).symm.symm) x)) = G x
        simpa using congrArg G ((castFinCLE (Nat.succ_add m n)).symm_apply_apply x)
      calc
        T F = T' F' := by
          simpa [T', hFid]
        _ = headTranslationDescentCLM T' normedUnitBumpSchwartz (sliceIntegral F') := hdesc
        _ = headTranslationDescentCLM T' normedUnitBumpSchwartz (sliceIntegral G') := hIH
        _ = T' G' := hdescG.symm
        _ = T G := by
          simpa [T', hGid]

end OSReconstruction
