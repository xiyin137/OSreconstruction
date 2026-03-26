import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Public copy of the basic one-point positive-time support bridge needed for
the direct `k = 2` VI.1 orbit argument. -/
private theorem onePointToFin1_tsupport_orderedPositiveTime_vi1Bridge_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  have hv0 : v 0 ∈ tsupport (g : SpacetimeDim d → ℂ) := by
    exact
      tsupport_comp_subset_preimage (g : SpacetimeDim d → ℂ)
        (f := fun w : Fin 1 → SpacetimeDim d => w 0) (continuous_apply 0) hv
  exact Set.mem_setOf.mp (hg_pos hv0)

/-- Public reduced-domain version of the translated positive-time compactly
supported one-point test. -/
private def translatedPositiveTimeCompactSupport_vi1Bridge_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    positiveTimeCompactSupportSubmodule d := by
  let gξ : SchwartzSpacetime d := SCV.translateSchwartz (-ξ) g
  have hgξ_compact : HasCompactSupport (gξ : SpacetimeDim d → ℂ) := by
    simpa [gξ, Function.comp, SCV.translateSchwartz_apply] using
      hg_compact.comp_homeomorph (Homeomorph.addRight (-ξ))
  have hgξ_pos : tsupport (gξ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    intro x hx
    have hx' : x + (-ξ) ∈ tsupport (g : SpacetimeDim d → ℂ) := by
      exact tsupport_comp_subset_preimage (g : SpacetimeDim d → ℂ)
        (f := fun y : SpacetimeDim d => y + (-ξ))
        (Homeomorph.addRight (-ξ)).continuous hx
    have hgx := hg_pos hx'
    simpa using add_pos_of_pos_of_nonneg hξ (show 0 ≤ (x + -ξ) 0 from le_of_lt hgx)
  exact ⟨gξ, ⟨hgξ_pos, hgξ_compact⟩⟩

private theorem onePoint_osConjTensorProduct_apply_vi1Bridge_local
    (χ h : SchwartzSpacetime d) (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h)) y) =
      χ (y 0) * h (y 1) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      timeReflectionN, timeReflection_timeReflection]
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h)) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (onePointToFin1CLM d h)) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = χ (y 0) * h (y 1) := by
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast]

private theorem twoPointProductLift_vanishes_of_orderedPositiveTime_vi1Bridge_local
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    VanishesToInfiniteOrderOnCoincidence (twoPointProductLift χ h) := by
  have hh_ord :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1Bridge_local (d := d) h hh_pos
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ)).osConjTensorProduct
          (onePointToFin1CLM d h)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d)
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (g := onePointToFin1CLM d h)
      hχ_pos hh_ord
  have hprod_eq :
      (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ)).osConjTensorProduct
        (onePointToFin1CLM d h) =
        twoPointProductLift χ h := by
    ext x
    exact onePoint_osConjTensorProduct_apply_vi1Bridge_local χ h x
  simpa [hprod_eq] using hvanish

private def twoPointProductLiftPositiveZeroDiagCLM_vi1Bridge_local
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ZeroDiagonalSchwartz d 2 :=
  (((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
      ((onePointToFin1CLM d).comp (positiveTimeCompactSupportValCLM d))).codRestrict
      (zeroDiagonalSubmodule d 2)
      (fun h =>
        twoPointProductLift_vanishes_of_orderedPositiveTime_vi1Bridge_local
          (d := d) χ (h : SchwartzSpacetime d) hχ_pos h.property.1))

@[simp] private theorem twoPointProductLiftPositiveZeroDiagCLM_vi1Bridge_local_eq_ofClassical
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    twoPointProductLiftPositiveZeroDiagCLM_vi1Bridge_local (d := d) χ hχ_pos h =
      ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d)) := by
  let hvanish :=
    twoPointProductLift_vanishes_of_orderedPositiveTime_vi1Bridge_local
      (d := d) χ (h : SchwartzSpacetime d) hχ_pos h.property.1
  apply Subtype.ext
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := twoPointProductLift χ (h : SchwartzSpacetime d)) hvanish]
  rfl

/-- Public one-point Schwinger CLM for the direct `k = 2` VI.1 orbit route. It
evaluates the two-point Schwinger functional against `χ` on the left and a
positive-time compact-support test on the right. -/
def schwingerProductPositiveCLM_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
    (twoPointProductLiftPositiveZeroDiagCLM_vi1Bridge_local (d := d) χ hχ_pos)

@[simp] theorem schwingerProductPositiveCLM_vi1Bridge_local_apply
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    schwingerProductPositiveCLM_vi1Bridge_local (d := d) OS χ hχ_pos h =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d))) := by
  let hvanish :=
    twoPointProductLift_vanishes_of_orderedPositiveTime_vi1Bridge_local
      (d := d) χ (h : SchwartzSpacetime d) hχ_pos h.property.1
  simp [schwingerProductPositiveCLM_vi1Bridge_local, ContinuousLinearMap.comp_apply,
    twoPointProductLiftPositiveZeroDiagCLM_vi1Bridge_local_eq_ofClassical,
    OsterwalderSchraderAxioms.schwingerCLM]

@[simp] theorem schwingerProductPositiveCLM_vi1Bridge_local_apply_translated
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    schwingerProductPositiveCLM_vi1Bridge_local (d := d) OS χ hχ_pos
        (translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d) g hg_pos hg_compact ξ hξ) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g))) := by
  simpa [translatedPositiveTimeCompactSupport_vi1Bridge_local] using
    schwingerProductPositiveCLM_vi1Bridge_local_apply
      (d := d) OS χ hχ_pos
      (translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d) g hg_pos hg_compact ξ hξ)

/-- The explicit translated product-shell boundary integrand is exactly the
scalar one-point Schwinger orbit through the translated reflected positive-time
test. This is the direct scalar bridge behind the later VI.1 integral
identifications. -/
theorem translatedProductShell_boundary_eq_schwingerProductPositiveOrbit_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (ξ : SpacetimeDim d) :
    let ψ := reflectedSchwartzSpacetime φ
    (if hξ : 0 < ξ 0 then
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ)))
    else 0) =
      (if hξ : 0 < ξ 0 then
        schwingerProductPositiveCLM_vi1Bridge_local (d := d) OS φ
          (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
            (d := d) φ hφ_compact hφ_neg)
          (translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d)
            (reflectedSchwartzSpacetime φ)
            (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
            (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
            ξ hξ)
      else 0) := by
  dsimp
  have hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  by_cases hξ : 0 < ξ 0
  · simpa [hξ] using
      (schwingerProductPositiveCLM_vi1Bridge_local_apply_translated
        (d := d) OS φ hφ_pos
        (reflectedSchwartzSpacetime φ)
        (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
        (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
        ξ hξ).symm
  · simpa [hξ]

/-- Integral form of the scalar boundary/orbit bridge. This is the public VI.1
copy of the scalar-orbit rewriting used later to compare the boundary shell to
regularized positive-time one-point data. -/
theorem integral_translatedProductShell_boundary_eq_schwingerProductPositiveOrbit_integral_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d) :
    let ψ := reflectedSchwartzSpacetime φ
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ)))
      else 0) * ((h : SchwartzSpacetime d) ξ) =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          schwingerProductPositiveCLM_vi1Bridge_local (d := d) OS φ
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)
            (translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d)
              (reflectedSchwartzSpacetime φ)
              (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
              (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
              ξ hξ)
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  dsimp
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  simpa using congrArg
    (fun z : ℂ => z * ((h : SchwartzSpacetime d) ξ))
    (translatedProductShell_boundary_eq_schwingerProductPositiveOrbit_vi1Bridge_local
      (d := d) OS φ hφ_compact hφ_neg ξ)

/-- Public reduced one-point OS Hilbert vector attached to a positive-time
compact-support test, for use in the direct VI.1 bridge. -/
private def positiveTimeOnePointVector_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (h : positiveTimeCompactSupportSubmodule d) : OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1)
          (onePointToFin1_tsupport_orderedPositiveTime_vi1Bridge_local
            (d := d) (h : SchwartzSpacetime d) h.property.1)⟧)) :
      OSHilbertSpace OS))

/-- The fully translated positive-time one-point vector, built only from public
ingredients. -/
private def translatedPositiveTimeOnePointVector_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) : OSHilbertSpace OS :=
  positiveTimeOnePointVector_vi1Bridge_local (d := d) OS
    (translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d) g hg_pos hg_compact ξ hξ)

/-- Full Euclidean translation by `-ξ` factors as time shift followed by a
purely spatial shift. This is the geometric identity behind the OS two-step
orbit. -/
private theorem twoStepTranslateSchwartz_eq_fullTranslate_vi1Bridge_local
    (g : SchwartzSpacetime d)
    (ξ : SpacetimeDim d) :
    let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
    let gt : SchwartzSpacetime d := SCV.translateSchwartz (-(timeShiftVec d (ξ 0))) g
    SCV.translateSchwartz (-Fin.cons 0 ξs) gt =
      SCV.translateSchwartz (-ξ) g := by
  dsimp
  let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
  let gt : SchwartzSpacetime d := SCV.translateSchwartz (-(timeShiftVec d (ξ 0))) g
  have hvec :
      (-Fin.cons 0 ξs : SpacetimeDim d) + (-timeShiftVec d (ξ 0) : SpacetimeDim d) = -ξ := by
    ext μ
    cases μ using Fin.cases with
    | zero =>
        simp [ξs, timeShiftVec]
    | succ i =>
        simp [ξs, timeShiftVec]
  ext x
  simp [SCV.translateSchwartz_apply, add_assoc]
  simpa [add_assoc] using congrArg (fun z : SpacetimeDim d => g (x + z)) hvec

/-- Positive Euclidean time shift on the OS Hilbert space sends the one-point
vector of `g` to the one-point vector of the time-translated test. -/
private theorem osTimeShiftHilbert_positiveTimeOnePointVector_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ)
    (ht : 0 < t) :
    osTimeShiftHilbert (d := d) OS lgc t ht
      (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩) =
      positiveTimeOnePointVector_vi1Bridge_local (d := d) OS
        (translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d) g hg_pos hg_compact
          (timeShiftVec d t) (by simpa [timeShiftVec] using ht)) := by
  let gt : SchwartzSpacetime d := SCV.translateSchwartz (-(timeShiftVec d t)) g
  let hgt : positiveTimeCompactSupportSubmodule d :=
    translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d) g hg_pos hg_compact
      (timeShiftVec d t) (by simpa [timeShiftVec] using ht)
  have hshift :
      timeShiftSchwartzNPoint (d := d) t
          (onePointToFin1CLM d g : SchwartzNPoint d 1) =
        (onePointToFin1CLM d gt : SchwartzNPoint d 1) := by
    ext x
    simp [gt, onePointToFin1CLM_apply, SCV.translateSchwartz_apply, sub_eq_add_neg]
  change osTimeShiftHilbert (d := d) OS lgc t ht
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              (onePointToFin1_tsupport_orderedPositiveTime_vi1Bridge_local
                (d := d) g hg_pos)⟧)) :
          OSHilbertSpace OS)) =
    positiveTimeOnePointVector_vi1Bridge_local (d := d) OS hgt
  rw [osTimeShiftHilbert_coe (d := d) (OS := OS) (lgc := lgc) (t := t) (ht := ht)]
  apply congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS))
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro n
  by_cases hn : n = 1
  · subst hn
    simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, timeShiftPositiveTimeBorchers,
      hgt, translatedPositiveTimeCompactSupport_vi1Bridge_local,
      gt, hshift]
  · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, timeShiftPositiveTimeBorchers,
      hgt, translatedPositiveTimeCompactSupport_vi1Bridge_local, hn]

/-- Public orbit identity for the direct `k = 2` VI.1 route: the translated
positive-time one-point vector is exactly the two-step OS orbit obtained by
positive real-time evolution followed by spatial translation. -/
theorem translatedPositiveTimeOnePointVector_eq_twoStepOrbit_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
    translatedPositiveTimeOnePointVector_vi1Bridge_local
        (d := d) OS g hg_pos hg_compact ξ hξ =
      (osSpatialTranslateHilbert (d := d) OS ξs)
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
          (positiveTimeOnePointVector_vi1Bridge_local
            (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩)) := by
  dsimp [translatedPositiveTimeOnePointVector_vi1Bridge_local]
  let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
  let gpt : positiveTimeCompactSupportSubmodule d := ⟨g, ⟨hg_pos, hg_compact⟩⟩
  let hg_ord :
      tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1Bridge_local (d := d) g hg_pos
  let Fg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_ord
  have hFg_compact :
      ∀ n, HasCompactSupport ((((Fg : BorchersSequence d).funcs n :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      have hg_compact_one :
          HasCompactSupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) := by
        simpa [onePointToFin1CLM] using
          (hg_compact.comp_homeomorph
            ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
      simpa [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single] using hg_compact_one
    · simp [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn, HasCompactSupport.zero]
  have htime_complex :
      (osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
        (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS gpt) =
      osTimeShiftHilbert (d := d) OS lgc (ξ 0) hξ
        (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS gpt) := by
    simpa [gpt, positiveTimeOnePointVector_vi1Bridge_local, Fg] using
      (osTimeShiftHilbertComplex_ofReal_eq_of_isCompactSupport
        (d := d) OS lgc Fg hFg_compact (ξ 0) hξ)
  let gtpt : positiveTimeCompactSupportSubmodule d :=
    translatedPositiveTimeCompactSupport_vi1Bridge_local (d := d) g hg_pos hg_compact
      (timeShiftVec d (ξ 0)) (by simpa [timeShiftVec] using hξ)
  let gt : SchwartzSpacetime d := (gtpt : SchwartzSpacetime d)
  have hspatial :
      (osSpatialTranslateHilbert (d := d) OS ξs)
        (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS gtpt) =
      translatedPositiveTimeOnePointVector_vi1Bridge_local
        (d := d) OS g hg_pos hg_compact ξ hξ := by
    have hraw := osSpatialTranslateHilbert_single_onePoint_eq
      (d := d) (OS := OS) gt gtpt.property.1 ξs
    have hfull :
        SCV.translateSchwartz (-Fin.cons 0 (fun i => ξ (Fin.succ i)))
            (SCV.translateSchwartz (-timeShiftVec d (ξ 0)) g) =
          SCV.translateSchwartz (-ξ) g := by
      simpa [timeShiftVec] using
        (twoStepTranslateSchwartz_eq_fullTranslate_vi1Bridge_local (d := d) g ξ)
    simpa [gtpt, gt, ξs, translatedPositiveTimeOnePointVector_vi1Bridge_local,
      positiveTimeOnePointVector_vi1Bridge_local,
      translatedPositiveTimeCompactSupport_vi1Bridge_local, hfull] using hraw
  calc
    translatedPositiveTimeOnePointVector_vi1Bridge_local
        (d := d) OS g hg_pos hg_compact ξ hξ
      = (osSpatialTranslateHilbert (d := d) OS ξs)
          (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS gtpt) := by
            symm
            exact hspatial
    _ = (osSpatialTranslateHilbert (d := d) OS ξs)
          (osTimeShiftHilbert (d := d) OS lgc (ξ 0) hξ
            (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS gpt)) := by
              rw [osTimeShiftHilbert_positiveTimeOnePointVector_vi1Bridge_local
                (d := d) OS lgc g hg_pos hg_compact (ξ 0) hξ]
    _ = (osSpatialTranslateHilbert (d := d) OS ξs)
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            (positiveTimeOnePointVector_vi1Bridge_local (d := d) OS gpt)) := by
              rw [htime_complex]

/-- The OS two-step orbit attached to a compactly supported positive-time
one-point test is continuous on the positive-time Euclidean domain. -/
theorem continuous_twoStepOrbit_positiveTime_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    let xg := positiveTimeOnePointVector_vi1Bridge_local
      (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξp.1 (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg)) := by
  dsimp
  let xg := positiveTimeOnePointVector_vi1Bridge_local
    (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
  let gtime : {r : ℝ // 0 < r} → OSHilbertSpace OS := fun s =>
    (osTimeShiftHilbertComplex (d := d) OS lgc ((s : ℝ) : ℂ)) xg
  have hcomplex :
      ContinuousOn
        (fun z : ℂ => (osTimeShiftHilbertComplex (d := d) OS lgc z) xg)
        {z : ℂ | 0 < z.re} :=
    continuousOn_osTimeShiftHilbertComplex_apply (d := d) OS lgc xg
  have htime0 :
      ContinuousOn
        (fun t : ℝ => (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) xg)
        (Set.Ioi 0) := by
    apply ContinuousOn.comp hcomplex
    · exact Complex.ofRealCLM.continuous.continuousOn
    · intro t ht
      simpa using ht
  have htimeReal : Continuous gtime := by
    rw [continuousOn_iff_continuous_restrict] at htime0
    change Continuous (fun s : {r : ℝ // 0 < r} =>
      (osTimeShiftHilbertComplex (d := d) OS lgc ((s : ℝ) : ℂ)) xg) at htime0
    simpa [gtime] using htime0
  have htime_map :
      Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        (⟨ξp.1 0, ξp.2⟩ : {r : ℝ // 0 < r})) := by
    exact ((continuous_apply (0 : Fin (d + 1))).comp continuous_subtype_val).subtype_mk
      (fun ξp => ξp.2)
  have htime :
      Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        (osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg) := by
    simpa [gtime] using htimeReal.comp htime_map
  have hspatial_map :
      Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        ((fun i => ξp.1 (Fin.succ i)),
          (osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg)) := by
    let hspatialCoord : Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        ((fun i => ξp.1 (Fin.succ i)) : Fin d → ℝ)) :=
      continuous_pi (fun i => (continuous_apply (Fin.succ i)).comp continuous_subtype_val)
    exact hspatialCoord.prodMk htime
  simpa using
    (continuous_osSpatialTranslateHilbert_jointly (d := d) OS).comp hspatial_map

/-- The genuine translated positive-time one-point vector is continuous on the
positive-time Euclidean domain. -/
theorem continuous_translatedPositiveTimeOnePointVector_positiveTime_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      translatedPositiveTimeOnePointVector_vi1Bridge_local
        (d := d) OS g hg_pos hg_compact ξp.1 ξp.2) := by
  have hEq :
      (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        translatedPositiveTimeOnePointVector_vi1Bridge_local
          (d := d) OS g hg_pos hg_compact ξp.1 ξp.2) =
      (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        (osSpatialTranslateHilbert (d := d) OS (fun i => ξp.1 (Fin.succ i)))
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ))
            (positiveTimeOnePointVector_vi1Bridge_local
              (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩))) := by
    funext ξp
    simpa using
      (translatedPositiveTimeOnePointVector_eq_twoStepOrbit_vi1Bridge_local
        (d := d) OS lgc g hg_pos hg_compact ξp.1 ξp.2)
  rw [hEq]
  exact continuous_twoStepOrbit_positiveTime_vi1Bridge_local
    (d := d) OS lgc g hg_pos hg_compact

/-- The fixed-left-vector matrix element of the two-step OS orbit is continuous
on the positive-time Euclidean domain. -/
theorem continuous_twoStepMatrixElement_positiveTime_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    let xχ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
    let xg := positiveTimeOnePointVector_vi1Bridge_local
      (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      @inner ℂ (OSHilbertSpace OS) _ xχ
        ((osSpatialTranslateHilbert (d := d) OS (fun i => ξp.1 (Fin.succ i)))
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg))) := by
  dsimp
  let xχ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
            hχ_pos⟧)) : OSHilbertSpace OS))
  let xg := positiveTimeOnePointVector_vi1Bridge_local
    (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
  exact continuous_inner.comp
    (continuous_const.prodMk
      (continuous_twoStepOrbit_positiveTime_vi1Bridge_local
        (d := d) OS lgc g hg_pos hg_compact))

/-- The reflected translated product-shell boundary integrand for a real
negative-time probe is continuous on the positive-time Euclidean region. -/
theorem continuousOn_translatedProductShell_boundary_positiveTime_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0}) :
    ContinuousOn
      (fun ξ : SpacetimeDim d =>
        if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0)
      {ξ : SpacetimeDim d | 0 < ξ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
    if hξ : 0 < ξp.1 0 then
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-ξp.1) (reflectedSchwartzSpacetime φ))))
    else 0)
  have hfun :
      (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
        if hξ : 0 < ξp.1 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξp.1) (reflectedSchwartzSpacetime φ))))
        else 0) =
      (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
          (ξp.1 0) (fun i => ξp.1 (Fin.succ i))) := by
    funext ξp
    have hξ : 0 < ξp.1 0 := ξp.2
    rw [dif_pos hξ]
    simpa using
      (osSemigroupGroupMatrixElement_eq_translatedProductShell_of_real_negative_probe_local
        (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξp.1 hξ).symm
  rw [hfun]
  have hbase :
      ContinuousOn
        (fun p : ℝ × (Fin d → ℝ) =>
          osSemigroupGroupMatrixElement (d := d) OS lgc
            (((show OSPreHilbertSpace OS from
              ⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d φ : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
            p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_osSemigroupGroupMatrixElement_Ioi
      (d := d) OS lgc
      (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
            (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
  let coord : {ξ : SpacetimeDim d // 0 < ξ 0} → ℝ × (Fin d → ℝ) :=
    fun ξp => (ξp.1 0, fun i => ξp.1 (Fin.succ i))
  have hcoord_cont : Continuous coord := by
    exact
      ((continuous_apply (0 : Fin (d + 1))).comp continuous_subtype_val).prodMk
        (continuous_pi (fun i => (continuous_apply (Fin.succ i)).comp continuous_subtype_val))
  rw [continuousOn_iff_continuous_restrict] at hbase
  have hcoord_sub :
      Continuous (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
        (⟨coord ξp, by
          exact ⟨ξp.2, by simp⟩⟩ :
          {p : ℝ × (Fin d → ℝ) // p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ})) := by
    exact hcoord_cont.subtype_mk (fun ξp => ⟨ξp.2, by simp⟩)
  simpa [coord] using hbase.comp hcoord_sub

/-- The weighted translated product-shell boundary integrand is integrable
against any compactly supported positive-time test. -/
theorem integrable_translatedProductShell_boundary_weight_vi1Bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d) :
    Integrable
      (fun ξ : SpacetimeDim d =>
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ)) volume := by
  let F : SpacetimeDim d → ℂ := fun ξ =>
    (if hξ : 0 < ξ 0 then
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
    else 0) * ((h : SchwartzSpacetime d) ξ)
  let H : Set (SpacetimeDim d) := tsupport (((h : positiveTimeCompactSupportSubmodule d) :
    SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  have hH_compact : IsCompact H := h.property.2.isCompact
  have hF_support : Function.support F ⊆ H := by
    intro ξ hξ
    by_contra hξH
    have hzero : ((h : SchwartzSpacetime d) ξ) = 0 := image_eq_zero_of_notMem_tsupport hξH
    apply hξ
    simp [F, hzero]
  have hF_cont : ContinuousOn F H := by
    have horbit :
        ContinuousOn
          (fun ξ : SpacetimeDim d =>
            if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift φ
                  (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
            else 0)
          H := by
      refine (continuousOn_translatedProductShell_boundary_positiveTime_vi1Bridge_local
        (d := d) OS lgc φ hφ_real hφ_compact hφ_neg).mono ?_
      intro ξ hξH
      exact h.property.1 hξH
    have hh_cont : ContinuousOn (fun ξ : SpacetimeDim d => ((h : SchwartzSpacetime d) ξ)) H :=
      (SchwartzMap.continuous ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)).continuousOn
    exact horbit.mul hh_cont
  apply (integrableOn_iff_integrable_of_support_subset hF_support).mp
  exact hF_cont.integrableOn_compact hH_compact

end OSReconstruction
