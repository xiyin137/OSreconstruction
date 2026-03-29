import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Bounds

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Splitting a positive Euclidean time into two equal dampings plus a residual
time rewrites the semigroup-group matrix element of `x` as the residual
matrix element of the damped vector `T(s)x`. This is the direct operator-side
factorization behind the fixed-strip VI.1 domination argument. -/
theorem osSemigroupGroupMatrixElement_eq_damped_vi1Damping_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (a : Fin d → ℝ)
    (s t : ℝ)
    (hs : 0 < s)
    (ht : 0 < t) :
    osSemigroupGroupMatrixElement (d := d) OS lgc x (s + t + s) a =
      osSemigroupGroupMatrixElement (d := d) OS lgc
        ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) x) t a := by
  let y : OSHilbertSpace OS :=
    (osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) x
  calc
    osSemigroupGroupMatrixElement (d := d) OS lgc x (s + t + s) a
        =
      @inner ℂ (OSHilbertSpace OS) _
        ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS (0 : Fin d → ℝ)) x))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((t + s : ℝ) : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
            simpa [add_assoc] using
              (osSemigroupGroupMatrixElement_eq_inner_timeShift_add
                (d := d) OS lgc x (0 : Fin d → ℝ) a s (t + s) hs (add_pos ht hs))
    _ =
      @inner ℂ (OSHilbertSpace OS) _
        y
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS a) y)) := by
            have hcomp :
                osTimeShiftHilbertComplex (d := d) OS lgc ((t + s : ℝ) : ℂ) =
                  (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)).comp
                    (osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) := by
              simpa [add_comm] using
                (osTimeShiftHilbertComplex_comp (d := d) OS lgc t s ht hs)
            have hcomm :=
              osSpatialTranslateHilbert_commutes_osTimeShiftHilbertComplex_ofReal
                (d := d) OS lgc a s hs
            have happ :
                (osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
                    ((osSpatialTranslateHilbert (d := d) OS a) x) =
                  (osSpatialTranslateHilbert (d := d) OS a)
                    ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) x) := by
              simpa [ContinuousLinearMap.comp_apply] using
                congrArg
                  (fun f : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS => f x) hcomm.symm
            rw [osSpatialTranslateHilbert_zero]
            rw [hcomp]
            simp only [ContinuousLinearMap.comp_apply]
            rw [happ]
            simp [y]
    _ =
      osSemigroupGroupMatrixElement (d := d) OS lgc y t a := by
        symm
        simpa [y, osSpatialTranslateHilbert_zero] using
          (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
            (d := d) OS lgc y (0 : Fin d → ℝ) a t ht)

/-- Quantitative fixed-strip bound: after damping by a positive Euclidean time
`s`, the original semigroup-group matrix element is bounded by the square norm
of the damped vector, uniformly in the residual time and all spatial
translations. -/
theorem osSemigroupGroupMatrixElement_norm_le_two_mul_damped_norm_sq_vi1Damping_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (a : Fin d → ℝ)
    (s t : ℝ)
    (hs : 0 < s)
    (ht : 0 < t) :
    ‖osSemigroupGroupMatrixElement (d := d) OS lgc x (s + t + s) a‖ ≤
      2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) x‖ ^ 2 := by
  rw [osSemigroupGroupMatrixElement_eq_damped_vi1Damping_local
    (d := d) OS lgc x a s t hs ht]
  exact
    osSemigroupGroupMatrixElement_norm_le_two_mul_norm_sq_vi1Bounds_local
      (d := d) OS lgc
      ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) x) t a ht

/-- Probe-specific direct OS corollary: on any positive-time point whose time
coordinate exceeds `2s`, the translated product-shell boundary integrand is
bounded by the damped probe norm at time `s`. This keeps the domination step on
the original VI.1 shell rather than the regularized one. -/
theorem translatedProductShell_boundary_norm_le_two_mul_damped_norm_sq_vi1Damping_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (ξ : SpacetimeDim d)
    (s : ℝ)
    (hs : 0 < s)
    (hgap : 0 < ξ 0 - (s + s)) :
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧)) : OSHilbertSpace OS))
    ‖if _hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
      else 0‖ ≤
      2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) xφ‖ ^ 2 := by
  let xφ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧)) : OSHilbertSpace OS))
  have hξ : 0 < ξ 0 := by
    linarith
  have htime : s + (ξ 0 - (s + s)) + s = ξ 0 := by
    ring
  rw [dif_pos hξ]
  rw [← osSemigroupGroupMatrixElement_eq_translatedProductShell_of_real_negative_probe_local
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξ hξ]
  have hbound :=
    osSemigroupGroupMatrixElement_norm_le_two_mul_damped_norm_sq_vi1Damping_local
      (d := d) OS lgc xφ (fun i => ξ (Fin.succ i)) s (ξ 0 - (s + s)) hs hgap
  simpa [xφ, htime] using hbound

/-- If the positive-time support of `h` lies above the fixed strip `ξ₀ > 2s`
and the damped probe vectors at time `s` are uniformly bounded, then the
translated product-shell boundary integrands are uniformly dominated by the
integrable weight `C * ‖h ξ‖`. This packages the DCT side of the direct OS
argument while leaving the genuine remaining work isolated in the uniform
damped-norm hypothesis. -/
theorem ae_norm_translatedProductShell_boundary_weight_le_of_uniform_damped_bound_vi1Damping_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d)
    (s C : ℝ)
    (hs : 0 < s)
    (hmargin : tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0})
    (hdamp : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) xφ‖ ^ 2 ≤ C) :
    ∀ n,
      ∀ᵐ ξ : SpacetimeDim d ∂volume,
        ‖((if _hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ))‖ ≤
          C * ‖((h : SchwartzSpacetime d) ξ)‖ := by
  intro n
  refine Filter.Eventually.of_forall ?_
  intro ξ
  by_cases hξmem :
      ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ)
  · have hgap : 0 < ξ 0 - (s + s) := by
      have hstrip : s + s < ξ 0 := hmargin hξmem
      linarith
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
          OSHilbertSpace OS))
    have hpt :
        ‖if _hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0‖ ≤
          2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) xφ‖ ^ 2 := by
      simpa [xφ] using
        translatedProductShell_boundary_norm_le_two_mul_damped_norm_sq_vi1Damping_local
          (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n) ξ s hs hgap
    have hdamp_n :
        2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) xφ‖ ^ 2 ≤ C := by
      simpa [xφ] using hdamp n
    calc
      ‖((if _hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ))‖
          =
        ‖(if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0)‖ * ‖((h : SchwartzSpacetime d) ξ)‖ := by
            rw [norm_mul]
      _ ≤ (2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) xφ‖ ^ 2) *
            ‖((h : SchwartzSpacetime d) ξ)‖ := by
              gcongr
      _ ≤ C * ‖((h : SchwartzSpacetime d) ξ)‖ := by
              exact mul_le_mul_of_nonneg_right hdamp_n (norm_nonneg _)
  · have hzero : ((h : SchwartzSpacetime d) ξ) = 0 := image_eq_zero_of_notMem_tsupport hξmem
    simp [hzero]

end OSReconstruction
