/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSchwinger










open Complex Topology MeasureTheory Set
open scoped Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- The reflected product source after reversing its left block and
normalizing the arity to the Chapter V reduced-coordinate convention. -/
noncomputable def reflectedChronologicalSource
    (f : SchwartzNPoint d (k + 1)) :
    SchwartzNPoint d ((k + (k + 1)) + 1) :=
  reindexSchwartz (d := d)
    ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
      (finCongr (by omega)))
    (f.osConjTensorProduct f)

/-- The chronologically reordered reflected product of two independently
chosen positive-time sources. The first source supplies the reflected left
block and the second source supplies the right block. -/
noncomputable def mixedReflectedChronologicalSource
    (f g : SchwartzNPoint d (k + 1)) :
    SchwartzNPoint d ((k + (k + 1)) + 1) :=
  reindexSchwartz (d := d)
    ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
      (finCongr (by omega)))
    (f.osConjTensorProduct g)

private theorem osiiAxisPairLeftBlockReversePerm_involutive
    (n m : ℕ) (i : Fin (n + m)) :
    osiiAxisPairLeftBlockReversePerm n m
        (osiiAxisPairLeftBlockReversePerm n m i) =
      i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    simp

/-- Translation commutes with chronological reindexing for a mixed reflected
product just as it does for a diagonal reflected product. -/
theorem translate_mixedReflectedChronologicalSource
    (u : Fin (k + k) → ℝ)
    (f g : SchwartzNPoint d (k + 1)) :
    translateSchwartzConfiguration
        (reflectedReducedAbsoluteDisplacement (d := d) u)
        (mixedReflectedChronologicalSource f g) =
      reindexSchwartz (d := d)
        ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
          (finCongr (by omega)))
        (translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM
            (fun r : Fin k =>
              chronologicalTimeSourceDirection (d := d) r) u)
          (f.osConjTensorProduct g)) := by
  ext x
  simp only [translateSchwartzConfiguration_apply,
    mixedReflectedChronologicalSource, reindexSchwartz_apply]
  congr 1
  funext i μ
  change
    x (((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
      (finCongr (by omega))) i) μ +
        reflectedReducedAbsoluteDisplacement (d := d) u
          (((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega))) i) μ =
      x (((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
        (finCongr (by omega))) i) μ +
        reflectedSourceParameterDisplacementCLM
          (fun r : Fin k =>
            chronologicalTimeSourceDirection (d := d) r) u i μ
  congr 1
  simp only [reflectedReducedAbsoluteDisplacement]
  apply congrArg
    (fun j =>
      reflectedSourceParameterDisplacementCLM
        (fun r : Fin k =>
          chronologicalTimeSourceDirection (d := d) r) u j μ)
  change
    osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
        ((finCongr (by omega)).symm
          ((finCongr (by omega))
            (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1) i))) =
      i
  rw [Equiv.symm_apply_apply]
  exact
    osiiAxisPairLeftBlockReversePerm_involutive
      (k + 1) (k + 1) i

/-- A translated raw reflected product which is zero-diagonal remains
zero-diagonal after chronological reindexing. -/
theorem
    translate_mixedReflectedChronologicalSource_vanishes_of_raw
    (u : Fin (k + k) → ℝ)
    (f g : SchwartzNPoint d (k + 1))
    (hraw :
      VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM
            (fun r : Fin k =>
              chronologicalTimeSourceDirection (d := d) r) u)
          (f.osConjTensorProduct g))) :
    VanishesToInfiniteOrderOnCoincidence
      (translateSchwartzConfiguration
        (reflectedReducedAbsoluteDisplacement (d := d) u)
        (mixedReflectedChronologicalSource f g)) := by
  rw [translate_mixedReflectedChronologicalSource]
  exact
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      hraw
      ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
        (finCongr (by omega)))

private theorem schwinger_reindex_finCongr
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzNPoint d n) :
    OS.S m
        (ZeroDiagonalSchwartz.ofClassical
          (reindexSchwartz (d := d) (finCongr h) φ)) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical φ) := by
  subst m
  have hreindex :
      reindexSchwartz (d := d) (finCongr rfl) φ = φ := by
    ext x
    rfl
  rw [hreindex]

/-- E3 identifies the Schwinger value of a translated mixed reflected
product with that of its chronologically reordered source. -/
theorem mixedReflectedChronologicalSource_schwinger_eq_raw
    (OS : OsterwalderSchraderAxioms d)
    (u : Fin (k + k) → ℝ)
    (f g : SchwartzNPoint d (k + 1))
    (hraw :
      VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM
            (fun r : Fin k =>
              chronologicalTimeSourceDirection (d := d) r) u)
          (f.osConjTensorProduct g))) :
    OS.S ((k + (k + 1)) + 1)
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (reflectedReducedAbsoluteDisplacement (d := d) u)
            (mixedReflectedChronologicalSource f g))) =
      OS.S ((k + 1) + (k + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM
              (fun r : Fin k =>
                chronologicalTimeSourceDirection (d := d) r) u)
            (f.osConjTensorProduct g))) := by
  let raw :
      SchwartzNPoint d ((k + 1) + (k + 1)) :=
    translateSchwartzConfiguration
      (reflectedSourceParameterDisplacementCLM
        (fun r : Fin k =>
          chronologicalTimeSourceDirection (d := d) r) u)
      (f.osConjTensorProduct g)
  let e : Fin ((k + 1) + (k + 1)) ≃
      Fin ((k + (k + 1)) + 1) :=
    finCongr (by omega)
  let rawTarget : SchwartzNPoint d ((k + (k + 1)) + 1) :=
    reindexSchwartz (d := d) e raw
  let τ : Equiv.Perm (Fin ((k + (k + 1)) + 1)) :=
    e.symm.trans
      ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans e)
  have hrawTarget :
      VanishesToInfiniteOrderOnCoincidence rawTarget := by
    exact
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        hraw e
  have hnormalized :
      translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d) u)
          (mixedReflectedChronologicalSource f g) =
        reindexSchwartz (d := d) τ rawTarget := by
    rw [translate_mixedReflectedChronologicalSource]
    ext x
    simp [τ, rawTarget, raw, e, reindexSchwartz_apply]
  have hnorm :
      VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d) u)
          (mixedReflectedChronologicalSource f g)) := by
    rw [hnormalized]
    exact
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        hrawTarget τ
  let rawTargetZ :
      ZeroDiagonalSchwartz d ((k + (k + 1)) + 1) :=
    ⟨rawTarget, hrawTarget⟩
  let normalizedZ :
      ZeroDiagonalSchwartz d ((k + (k + 1)) + 1) :=
    ⟨translateSchwartzConfiguration
        (reflectedReducedAbsoluteDisplacement (d := d) u)
        (mixedReflectedChronologicalSource f g), hnorm⟩
  have hE3 :
      OS.S ((k + (k + 1)) + 1) rawTargetZ =
        OS.S ((k + (k + 1)) + 1) normalizedZ := by
    refine OS.E3_symmetric
      ((k + (k + 1)) + 1) τ rawTargetZ normalizedZ ?_
    intro x
    simpa [rawTargetZ, normalizedZ, hnormalized,
      reindexSchwartz_apply]
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes _ hnorm]
  rw [← hE3]
  change
    OS.S ((k + (k + 1)) + 1) (⟨rawTarget, hrawTarget⟩ :
        ZeroDiagonalSchwartz d ((k + (k + 1)) + 1)) =
      OS.S ((k + 1) + (k + 1))
        (ZeroDiagonalSchwartz.ofClassical raw)
  rw [← ZeroDiagonalSchwartz.ofClassical_of_vanishes
    rawTarget hrawTarget]
  exact
    schwinger_reindex_finCongr OS (by omega) raw

end OSIIChapterV
end OSReconstruction
