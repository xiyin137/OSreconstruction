import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAXiShift
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Witness-exposed version of the fixed-strip `xiShift` product-shell package.

This is the same common fixed-strip pairing as
`exists_common_fixed_strip_xiShift_productShell_pairing_local`, but it keeps the
actual flattened positive-time-difference witness `G` on the surface. This is
the natural entry point for the remaining analytic kernel-package seam in
Input A. -/
theorem exists_common_fixed_strip_xiShift_productShell_pairing_with_witness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ n,
        let xφ : OSHilbertSpace OS :=
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                  (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                    (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
              OSHilbertSpace OS))
        osSemigroupGroupMatrixElement (d := d) OS lgc xφ t (0 : Fin d → ℝ) =
          ∫ z : NPointDomain d 2,
            G (BHW.toDiffFlat 2 d
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                ((t : ℂ) * Complex.I))) *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1))) := by
  obtain ⟨G, hG_holo, hG_euclid⟩ := schwinger_continuation_base_step (d := d) OS lgc 2
  refine ⟨G, hG_holo, hG_euclid, ?_⟩
  intro n
  let Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ := fun z => G (BHW.toDiffFlat 2 d z)
  let φ : SchwartzSpacetime d := φ_seq n
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ (hφ_compact n) (hφ_neg n)
  let ψ : SchwartzSpacetime d := reflectedSchwartzSpacetime φ
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ (hφ_neg n)
  let hψ_pos :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d) ψ hψ_pos_time
  let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ (hφ_compact n)
  let xφ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            hφ_pos⟧)) : OSHilbertSpace OS))
  let xψ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
            hψ_pos⟧)) : OSHilbertSpace OS))
  have hx_eq_pre :
      (⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧ : OSPreHilbertSpace OS) =
        (⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
            hψ_pos⟧ : OSPreHilbertSpace OS) :=
    mk_single_osConj_onePoint_eq_mk_single_reflected_of_real_local
      (d := d) OS φ (hφ_real n) (hφ_compact n) (hφ_neg n)
  have hx_eq : xφ = xψ := by
    exact congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS)) hx_eq_pre
  calc
    osSemigroupGroupMatrixElement (d := d) OS lgc xφ t (0 : Fin d → ℝ)
        = @inner ℂ (OSHilbertSpace OS) _
            xφ
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) xφ) := by
              simpa [osSpatialTranslateHilbert_zero]
                using
                  (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                    (d := d) OS lgc xφ (0 : Fin d → ℝ) (0 : Fin d → ℝ) t ht)
    _ = @inner ℂ (OSHilbertSpace OS) _
          xφ
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) xψ) := by
            rw [hx_eq]
    _ =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          xφ xψ (t : ℂ) := by
            exact osTimeShiftHilbertComplex_inner_eq (d := d) OS lgc xφ xψ (t : ℂ) ht
    _ =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (φ (y 0) * ψ (y 1)) := by
              exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
                (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ)
                (hΨ_euclid := by
                  intro f
                  simpa [Ψ] using hG_euclid f)
                φ ψ hφ_pos hψ_pos hψ_compact t ht
    _ =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (φ (z 0) * ψ (z 0 + z 1)) := by
              simpa [ψ] using
                (integral_mul_twoPointProductLift_eq_centerShear
                  (d := d)
                  (Ψ := fun y : NPointDomain d 2 =>
                    Ψ (xiShift ⟨1, by omega⟩ 0
                      (fun i => wickRotatePoint (y i))
                      ((t : ℂ) * Complex.I)))
                  φ ψ)
    _ =
        ∫ z : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d
            (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I))) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) := by
              rfl

end OSReconstruction
