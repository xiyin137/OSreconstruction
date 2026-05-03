import OSReconstruction.SCV.SemigroupGroupBochner
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup

/-!
# Spatial Translation and Momentum Infrastructure for OS Reconstruction

This file develops the spatial-translation side of the OS Hilbert-space
reconstruction. It is the operator-theoretic companion to the Euclidean-time
semigroup in `OSToWightmanSemigroup.lean`.

The proved part of the file constructs the spatial translation operators on the
honest OS quotient and on its Hilbert completion, together with their additive
and unitary properties.

The remaining explicit theorem-level `sorry`s isolate the next genuine
mathematical gaps on the OS/Stone route:

- weak continuity of axis slices on the dense compact-support domain,
- strong continuity at `0` on that dense domain,
- strong continuity on the Hilbert completion.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Complex

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

private theorem timeReflection_involutive_local (x : SpacetimeDim d) :
    timeReflection d (timeReflection d x) = x := by
  ext i
  simp only [timeReflection]
  split_ifs with h
  · subst h
    ring
  · rfl

private theorem timeReflectionN_involutive_local {n : ℕ} (x : NPointDomain d n) :
    timeReflectionN d (timeReflectionN d x) = x := by
  funext i
  exact timeReflection_involutive_local (x i)

private theorem timeReflection_add_spatial_local
    (a0 : SpacetimeDim d) (ha0 : a0 0 = 0) (x : SpacetimeDim d) :
    timeReflection d x + a0 = timeReflection d (x + a0) := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeReflection, ha0]
  · simp [timeReflection, hμ]

@[simp] private theorem osConj_osConj_local {n : ℕ}
    (f : SchwartzNPoint d n) :
    f.osConj.osConj = f := by
  ext x
  simp only [SchwartzNPoint.osConj_apply, starRingEnd_self_apply,
    timeReflectionN_involutive_local]

private theorem onePointToFin1_tsupport_orderedPositiveTime
    (f : SchwartzSpacetime d)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d f : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  have hv0 : v 0 ∈ tsupport (f : SpacetimeDim d → ℂ) := by
    have := tsupport_comp_subset_preimage (f : SpacetimeDim d → ℂ)
      (f := fun w : Fin 1 → SpacetimeDim d => w 0) (continuous_apply 0) hv
    exact this
  exact Set.mem_setOf.mp (hf hv0)

/-- Spatial translation on one-point Schwartz functions:
`(τ_a f)(x) = f(x₀, x₁ + a₁, ..., x_d + a_d)`. -/
def spatialTranslateOnePoint (a : Fin d → ℝ) (f : SchwartzSpacetime d) :
    SchwartzSpacetime d :=
  SCV.translateSchwartz (Fin.cons 0 a) f

/-- Spatial translation preserves positive-time support. -/
theorem spatialTranslateOnePoint_preserves_positive_time
    (a : Fin d → ℝ) (f : SchwartzSpacetime d)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0}) :
    tsupport ((spatialTranslateOnePoint a f : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0} := by
  intro x hx
  let a0 : SpacetimeDim d := Fin.cons 0 a
  have hxpre : x + a0 ∈ tsupport (f : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage (f : SpacetimeDim d → ℂ)
      (f := fun y : SpacetimeDim d => y + a0)
      (continuous_id.add continuous_const) hx
  have hpos := hf hxpre
  simpa [spatialTranslateOnePoint, SCV.translateSchwartz_apply, a0] using hpos

/-- Spatial translation preserves the basic OS two-point tensor term. -/
theorem os_tensor_term_spatial_translate_invariant
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (f g : SchwartzSpacetime d)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hg : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0}) :
    let f0 : SchwartzNPoint d 1 := onePointToFin1CLM d f
    let g0 : SchwartzNPoint d 1 := onePointToFin1CLM d g
    let f0t : SchwartzNPoint d 1 := onePointToFin1CLM d (spatialTranslateOnePoint a f)
    let g0t : SchwartzNPoint d 1 := onePointToFin1CLM d (spatialTranslateOnePoint a g)
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f0t.osConjTensorProduct g0t)) =
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f0.osConjTensorProduct g0)) := by
  let a0 : SpacetimeDim d := Fin.cons 0 a
  have hf_ord :
      tsupport (((onePointToFin1CLM d f : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime (d := d) f hf
  have hg_ord :
      tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime (d := d) g hg
  have hf_trans_ord :
      tsupport (((onePointToFin1CLM d (spatialTranslateOnePoint a f) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime (d := d) (spatialTranslateOnePoint a f)
      (spatialTranslateOnePoint_preserves_positive_time (d := d) a f hf)
  have hg_trans_ord :
      tsupport (((onePointToFin1CLM d (spatialTranslateOnePoint a g) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime (d := d) (spatialTranslateOnePoint a g)
      (spatialTranslateOnePoint_preserves_positive_time (d := d) a g hg)
  let f0 : SchwartzNPoint d 1 := onePointToFin1CLM d f
  let g0 : SchwartzNPoint d 1 := onePointToFin1CLM d g
  let f0t : SchwartzNPoint d 1 := onePointToFin1CLM d (spatialTranslateOnePoint a f)
  let g0t : SchwartzNPoint d 1 := onePointToFin1CLM d (spatialTranslateOnePoint a g)
  have hleft_vanish :
      VanishesToInfiniteOrderOnCoincidence (f0t.osConjTensorProduct g0t) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := f0t) (g := g0t) hf_trans_ord hg_trans_ord
  have hright_vanish :
      VanishesToInfiniteOrderOnCoincidence (f0.osConjTensorProduct g0) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := f0) (g := g0) hf_ord hg_ord
  let leftZ : ZeroDiagonalSchwartz d 2 := ⟨f0t.osConjTensorProduct g0t, hleft_vanish⟩
  let rightZ : ZeroDiagonalSchwartz d 2 := ⟨f0.osConjTensorProduct g0, hright_vanish⟩
  have htranslate :
      ∀ x : NPointDomain d 2,
        leftZ.1 x = rightZ.1 (fun i => x i + a0) := by
    intro x
    change (f0t.osConjTensorProduct g0t) x =
      (f0.osConjTensorProduct g0) (fun i => x i + a0)
    unfold SchwartzNPoint.osConjTensorProduct
    rw [SchwartzMap.tensorProduct_apply, SchwartzMap.tensorProduct_apply]
    simp only [SchwartzNPoint.osConj_apply,
      onePointToFin1CLM_apply, spatialTranslateOnePoint, SCV.translateSchwartz_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (f z))
      (timeReflection_add_spatial_local (d := d) a0 (by simp [a0]) (x 0))
  have hE1 : OS.S 2 leftZ = OS.S 2 rightZ := by
    simpa using (OS.E1_translation_invariant 2 a0 rightZ leftZ htranslate).symm
  simpa [f0, g0, f0t, g0t,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f0t.osConjTensorProduct g0t) hleft_vanish,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f0.osConjTensorProduct g0) hright_vanish] using hE1

/-- Spatial translation on the honest positive-time OS Borchers algebra. -/
private def spatialTranslatePositiveTimeBorchers (a : Fin d → ℝ)
    (F : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d where
  toBorchersSequence :=
    translateBorchers (d := d) (Fin.cons 0 a) (F : BorchersSequence d)
  ordered_tsupport := by
    intro n
    simpa using translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (n := n) (a := Fin.cons 0 a) (ha0 := by simp)
      ((F : BorchersSequence d).funcs n) (F.ordered_tsupport n)

@[simp] private theorem spatialTranslatePositiveTimeBorchers_funcs
    (a : Fin d → ℝ) (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    ((spatialTranslatePositiveTimeBorchers (d := d) a F :
        PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n =
      translateSchwartzNPoint (d := d) (Fin.cons 0 a)
        ((F : BorchersSequence d).funcs n) := rfl

private theorem translate_osConjTensorProduct_eq_of_spatial_local
    (a0 : SpacetimeDim d) (ha0 : a0 0 = 0)
    {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    ((translateSchwartzNPoint (d := d) a0 f).osConjTensorProduct
      (translateSchwartzNPoint (d := d) a0 g)) x =
      (f.osConjTensorProduct g) (fun i => x i - a0) := by
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, translateSchwartzNPoint_apply]
  congr
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, splitFirst, timeReflection, ha0]
    · simp [timeReflectionN, splitFirst, timeReflection, hμ]

private theorem schwinger_translate_tensor_eq_of_spatial_local
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (a0 : SpacetimeDim d) (ha0 : a0 0 = 0)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hleft : VanishesToInfiniteOrderOnCoincidence
      ((translateSchwartzNPoint (d := d) a0 f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a0 g)))
    (hright : VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct g)) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      ((translateSchwartzNPoint (d := d) a0 f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a0 g))) =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  symm
  refine OS.E1_translation_invariant (n + m) (-a0)
    (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g))
    (ZeroDiagonalSchwartz.ofClassical
      ((translateSchwartzNPoint (d := d) a0 f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a0 g))) ?_
  intro x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := f.osConjTensorProduct g) hright,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := ((translateSchwartzNPoint (d := d) a0 f).osConjTensorProduct
        (translateSchwartzNPoint (d := d) a0 g))) hleft]
  simpa [sub_eq_add_neg] using
    (translate_osConjTensorProduct_eq_of_spatial_local (d := d) a0 ha0 f g x)

private theorem translateSchwartzNPoint_add_local
    (a0 b0 : SpacetimeDim d) {n : ℕ}
    (f : SchwartzNPoint d n) :
    translateSchwartzNPoint (d := d) a0
      (translateSchwartzNPoint (d := d) b0 f) =
    translateSchwartzNPoint (d := d) (a0 + b0) f := by
  ext x
  simp [translateSchwartzNPoint_apply, sub_eq_add_neg, Pi.add_apply,
    add_comm, add_left_comm, add_assoc]

private theorem translateSchwartzNPoint_zero_local
    {n : ℕ} (f : SchwartzNPoint d n) :
    translateSchwartzNPoint (d := d) (0 : SpacetimeDim d) f = f := by
  ext x
  simp [translateSchwartzNPoint_apply]

omit [NeZero d] in
private abbrev flatSpatialDirectionLocal (v : Fin d → ℝ) {n : ℕ} :
    Fin (n * (d + 1)) → ℝ :=
  flattenCLEquivReal n (d + 1) (fun _ => Fin.cons 0 (-v))

omit [NeZero d] in
private theorem unflatten_add_flatSpatialDirection_local {n : ℕ}
    (u : Fin (n * (d + 1)) → ℝ) (t : ℝ) (v : Fin d → ℝ) :
    (flattenCLEquivReal n (d + 1)).symm (u + t • flatSpatialDirectionLocal (d := d) v) =
      fun i => ((flattenCLEquivReal n (d + 1)).symm u i) - Fin.cons 0 (t • v) := by
  ext i μ
  refine Fin.cases ?_ ?_ μ
  · simp [flatSpatialDirectionLocal, sub_eq_add_neg]
  · intro j
    simp [flatSpatialDirectionLocal, sub_eq_add_neg]

omit [NeZero d] in
private theorem spatialTranslateSchwartzNPoint_eq_unflatten_translate_local {n : ℕ}
    (v : Fin d → ℝ) (t : ℝ) (f : SchwartzNPoint d n) :
    translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) f =
      unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz (t • flatSpatialDirectionLocal (d := d) v)
          (flattenSchwartzNPoint (d := d) f)) := by
  ext x
  simp [SCV.translateSchwartz_apply, unflatten_add_flatSpatialDirection_local]

omit [NeZero d] in
private theorem hasCompactSupport_flattenSchwartzNPoint_local {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    HasCompactSupport
      ((flattenSchwartzNPoint (d := d) f :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) : (Fin (n * (d + 1)) → ℝ) → ℂ) := by
  simpa [flattenSchwartzNPoint] using
    hf.comp_homeomorph ((flattenCLEquivReal n (d + 1)).symm.toHomeomorph)

omit [NeZero d] in
private theorem tendsto_spatialTranslateSchwartzNPoint_nhds_of_isCompactSupport {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (v : Fin d → ℝ) (t₀ : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) f)
      (nhds t₀)
      (nhds (translateSchwartzNPoint (d := d) (Fin.cons 0 (t₀ • v)) f)) := by
  let ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f
  have hψ : HasCompactSupport ((ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) :
      (Fin (n * (d + 1)) → ℝ) → ℂ) :=
    hasCompactSupport_flattenSchwartzNPoint_local (d := d) f hf
  have hη : Continuous (fun t : ℝ => t • flatSpatialDirectionLocal (d := d) (n := n) v) :=
    continuous_id.smul continuous_const
  have hflat_full :
      Filter.Tendsto
        (fun s : Fin (n * (d + 1)) → ℝ => SCV.translateSchwartz s ψ)
        (nhds (t₀ • flatSpatialDirectionLocal (d := d) (n := n) v))
        (nhds (SCV.translateSchwartz (t₀ • flatSpatialDirectionLocal (d := d) (n := n) v) ψ)) :=
    SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ
      (t₀ • flatSpatialDirectionLocal (d := d) (n := n) v)
  have hflat :
      Filter.Tendsto
        (fun t : ℝ => SCV.translateSchwartz (t • flatSpatialDirectionLocal (d := d) (n := n) v) ψ)
        (nhds t₀)
        (nhds (SCV.translateSchwartz (t₀ • flatSpatialDirectionLocal (d := d) (n := n) v) ψ)) :=
    hflat_full.comp (hη.tendsto t₀)
  have hunflat :
      Filter.Tendsto
        (fun t : ℝ =>
          unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t • flatSpatialDirectionLocal (d := d) (n := n) v) ψ))
        (nhds t₀)
        (nhds
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t₀ • flatSpatialDirectionLocal (d := d) (n := n) v) ψ))) :=
    (((unflattenSchwartzNPoint (d := d) :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n).continuous).tendsto
      _).comp hflat
  simpa [ψ, spatialTranslateSchwartzNPoint_eq_unflatten_translate_local] using hunflat

omit [NeZero d] in
private theorem continuous_spatialTranslateSchwartzNPoint_of_isCompactSupport {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (v : Fin d → ℝ) :
    Continuous (fun t : ℝ => translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) f) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  exact tendsto_spatialTranslateSchwartzNPoint_nhds_of_isCompactSupport
    (d := d) f hf v t₀

/-- Spatial translation preserves the honest OS pairing on positive-time
Borchers vectors. -/
private theorem positiveTime_osInner_spatial_translate_eq
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (F G : PositiveTimeBorchersSequence d) :
    PositiveTimeBorchersSequence.osInner OS
      (spatialTranslatePositiveTimeBorchers (d := d) a F)
      (spatialTranslatePositiveTimeBorchers (d := d) a G) =
    PositiveTimeBorchersSequence.osInner OS F G := by
  let a0 : SpacetimeDim d := Fin.cons 0 a
  have ha0 : a0 0 = 0 := by
    simp [a0]
  have hleft :
      OSTensorAdmissible d
        ((spatialTranslatePositiveTimeBorchers (d := d) a F :
            PositiveTimeBorchersSequence d) : BorchersSequence d)
        ((spatialTranslatePositiveTimeBorchers (d := d) a G :
            PositiveTimeBorchersSequence d) : BorchersSequence d) :=
    PositiveTimeBorchersSequence.ostensorAdmissible (d := d)
      (spatialTranslatePositiveTimeBorchers (d := d) a F)
      (spatialTranslatePositiveTimeBorchers (d := d) a G)
  have hright :
      OSTensorAdmissible d (F : BorchersSequence d) (G : BorchersSequence d) :=
    PositiveTimeBorchersSequence.ostensorAdmissible (d := d) F G
  unfold PositiveTimeBorchersSequence.osInner
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  simpa [a0, spatialTranslatePositiveTimeBorchers_funcs] using
    schwinger_translate_tensor_eq_of_spatial_local (d := d) OS a0 ha0
      ((F : BorchersSequence d).funcs n) ((G : BorchersSequence d).funcs m)
      (hleft n m) (hright n m)

private theorem spatialTranslatePositiveTimeBorchers_respects_equiv
    (OS : OsterwalderSchraderAxioms d) (a : Fin d → ℝ)
    (F G : PositiveTimeBorchersSequence d)
    (hFG : osBorchersSetoid OS F G) :
    osBorchersSetoid OS
      (spatialTranslatePositiveTimeBorchers (d := d) a F)
      (spatialTranslatePositiveTimeBorchers (d := d) a G) := by
  let A : PositiveTimeBorchersSequence d := F - G
  have hA :
      PositiveTimeBorchersSequence.osInner OS A A = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS A A hFG
  have htranslate :
      PositiveTimeBorchersSequence.osInner OS
          (spatialTranslatePositiveTimeBorchers (d := d) a A)
          (spatialTranslatePositiveTimeBorchers (d := d) a A) =
        PositiveTimeBorchersSequence.osInner OS A A :=
    positiveTime_osInner_spatial_translate_eq (d := d) OS a A A
  have htranslate_zero :
      PositiveTimeBorchersSequence.osInner OS
          (spatialTranslatePositiveTimeBorchers (d := d) a A)
          (spatialTranslatePositiveTimeBorchers (d := d) a A) = 0 := by
    rw [htranslate, hA]
  show (PositiveTimeBorchersSequence.osInner OS
      ((spatialTranslatePositiveTimeBorchers (d := d) a F) -
        (spatialTranslatePositiveTimeBorchers (d := d) a G))
      ((spatialTranslatePositiveTimeBorchers (d := d) a F) -
        (spatialTranslatePositiveTimeBorchers (d := d) a G))).re = 0
  have hfuncs :
      ∀ n,
        ((((spatialTranslatePositiveTimeBorchers (d := d) a F) -
            (spatialTranslatePositiveTimeBorchers (d := d) a G) :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          (((spatialTranslatePositiveTimeBorchers (d := d) a A :
            PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simp [A, BorchersSequence.sub_funcs, spatialTranslatePositiveTimeBorchers_funcs]
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS
          ((spatialTranslatePositiveTimeBorchers (d := d) a F) -
            (spatialTranslatePositiveTimeBorchers (d := d) a G))
          ((spatialTranslatePositiveTimeBorchers (d := d) a F) -
            (spatialTranslatePositiveTimeBorchers (d := d) a G)) =
        PositiveTimeBorchersSequence.osInner OS
          (spatialTranslatePositiveTimeBorchers (d := d) a A)
          (spatialTranslatePositiveTimeBorchers (d := d) a A) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, htranslate_zero]
  simp

/-- Positive Euclidean time translation on the honest positive-time OS Borchers
algebra, localized to the spatial-momentum lane. -/
private def timeShiftPositiveTimeBorchersLocal (t : ℝ) (ht : 0 < t)
    (F : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d where
  toBorchersSequence := timeShiftBorchers (d := d) t (F : BorchersSequence d)
  ordered_tsupport := by
    intro n
    simpa using timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) (n := n) t ht ((F : BorchersSequence d).funcs n) (F.ordered_tsupport n)

@[simp] private theorem timeShiftPositiveTimeBorchersLocal_toBorchersSequence
    (t : ℝ) (ht : 0 < t) (F : PositiveTimeBorchersSequence d) :
    ((timeShiftPositiveTimeBorchersLocal (d := d) t ht F :
        PositiveTimeBorchersSequence d) : BorchersSequence d) =
      timeShiftBorchers (d := d) t (F : BorchersSequence d) := rfl

@[simp] private theorem timeShiftPositiveTimeBorchersLocal_translate_toBorchers_eq
    (t : ℝ) (ht : 0 < t) (a : Fin d → ℝ)
    (F : PositiveTimeBorchersSequence d) :
    ((timeShiftPositiveTimeBorchersLocal (d := d) t ht
        (spatialTranslatePositiveTimeBorchers (d := d) a F) :
          PositiveTimeBorchersSequence d) : BorchersSequence d) =
      ((spatialTranslatePositiveTimeBorchers (d := d) a
        (timeShiftPositiveTimeBorchersLocal (d := d) t ht F) :
          PositiveTimeBorchersSequence d) : BorchersSequence d) := by
  simpa [timeShiftPositiveTimeBorchersLocal_toBorchersSequence,
    spatialTranslatePositiveTimeBorchers] using
    timeShiftBorchers_translateBorchers (d := d) t (Fin.cons 0 a)
      (F : BorchersSequence d)

/-- Spatial translation descends to the honest OS quotient. -/
private def osSpatialTranslate (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    OSPreHilbertSpace OS → OSPreHilbertSpace OS :=
  Quotient.map (spatialTranslatePositiveTimeBorchers (d := d) a)
    (fun F G hFG =>
      spatialTranslatePositiveTimeBorchers_respects_equiv (d := d) OS a F G hFG)

/-- The quotient-level spatial translation is linear. -/
def osSpatialTranslateLinear (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    OSPreHilbertSpace OS →ₗ[ℂ] OSPreHilbertSpace OS where
  toFun := osSpatialTranslate (d := d) OS a
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with
    | h F =>
      induction y using Quotient.inductionOn with
      | h G =>
        exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
          simp [BorchersSequence.add_funcs, spatialTranslatePositiveTimeBorchers_funcs])
  map_smul' := by
    intro c x
    induction x using Quotient.inductionOn with
    | h F =>
      exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
        simp [BorchersSequence.smul_funcs, spatialTranslatePositiveTimeBorchers_funcs])

/-- Spatial translation preserves the OS inner product on the quotient. -/
theorem osSpatialTranslateLinear_inner_eq
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (x y : OSPreHilbertSpace OS) :
    @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        ((osSpatialTranslateLinear (d := d) OS a) x)
        ((osSpatialTranslateLinear (d := d) OS a) y) =
      @inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS) x y := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      change PositiveTimeBorchersSequence.osInner OS
          (spatialTranslatePositiveTimeBorchers (d := d) a F)
          (spatialTranslatePositiveTimeBorchers (d := d) a G) =
        PositiveTimeBorchersSequence.osInner OS F G
      exact positiveTime_osInner_spatial_translate_eq (d := d) OS a F G

/-- The quotient-level spatial translations form an additive representation. -/
theorem osSpatialTranslateLinear_comp
    (OS : OsterwalderSchraderAxioms d)
    (a b : Fin d → ℝ) :
    (osSpatialTranslateLinear (d := d) OS a).comp
        (osSpatialTranslateLinear (d := d) OS b) =
      osSpatialTranslateLinear (d := d) OS (a + b) := by
  ext x
  induction x using Quotient.inductionOn with
  | h F =>
      have hcons :
          (Fin.cons 0 a : SpacetimeDim d) + Fin.cons 0 b = Fin.cons 0 (a + b) := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j
          simp
      exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
        simp [spatialTranslatePositiveTimeBorchers_funcs,
          translateSchwartzNPoint_add_local, hcons])

/-- Zero spatial translation acts as the identity on the honest OS quotient. -/
theorem osSpatialTranslateLinear_zero
    (OS : OsterwalderSchraderAxioms d) :
    osSpatialTranslateLinear (d := d) OS 0 = 1 := by
  ext x
  induction x using Quotient.inductionOn with
  | h F =>
      have hzero : (Fin.cons 0 (0 : Fin d → ℝ) : SpacetimeDim d) = 0 := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j
          simp
      exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
        simp [spatialTranslatePositiveTimeBorchers_funcs,
          translateSchwartzNPoint_zero_local, hzero])

/-- Spatial translation preserves the norm on the honest OS quotient. -/
theorem osSpatialTranslateLinear_norm_eq
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (x : OSPreHilbertSpace OS) :
    ‖(osSpatialTranslateLinear (d := d) OS a) x‖ = ‖x‖ := by
  have hsq :
      ‖(osSpatialTranslateLinear (d := d) OS a) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ((osSpatialTranslateLinear (d := d) OS a) x),
      osSpatialTranslateLinear_inner_eq, inner_self_eq_norm_sq]
  nlinarith [norm_nonneg ((osSpatialTranslateLinear (d := d) OS a) x), norm_nonneg x]

/-- The quotient-level spatial translation is a bounded linear operator. -/
private noncomputable def osSpatialTranslateContinuous
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    OSPreHilbertSpace OS →L[ℂ] OSPreHilbertSpace OS :=
  (osSpatialTranslateLinear (d := d) OS a).mkContinuous 1 (fun x => by
    simpa [one_mul] using
      le_of_eq (osSpatialTranslateLinear_norm_eq (d := d) OS a x))

@[simp] private theorem osSpatialTranslateContinuous_apply
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) (x : OSPreHilbertSpace OS) :
    osSpatialTranslateContinuous (d := d) OS a x =
      osSpatialTranslateLinear (d := d) OS a x := rfl

/-- Spatial translation extended to the Hilbert completion. -/
noncomputable def osSpatialTranslateHilbert
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  (UniformSpace.Completion.toComplL.comp
    (osSpatialTranslateContinuous (d := d) OS a)).extend
    UniformSpace.Completion.toComplL

theorem osSpatialTranslateHilbert_coe
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) (x : OSPreHilbertSpace OS) :
    osSpatialTranslateHilbert (d := d) OS a (x : OSHilbertSpace OS) =
      ((osSpatialTranslateLinear (d := d) OS a x : OSPreHilbertSpace OS) :
        OSHilbertSpace OS) := by
  exact ContinuousLinearMap.extend_eq _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _) x

/-- Spatial translation of a one-point positive-time vector is represented by
the corresponding spatially translated one-point test. -/
theorem osSpatialTranslateHilbert_single_onePoint_eq
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (a : Fin d → ℝ) :
    let hg_ord :=
      onePointToFin1_tsupport_orderedPositiveTime (d := d) g hg_pos
    let a0 : SpacetimeDim d := Fin.cons 0 a
    let g_translated := SCV.translateSchwartz (-a0) g
    let hg_translated_ord :
        tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
      by
        have ha0 : a0 0 = 0 := by simp [a0]
        have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) =
          (((translateSchwartzNPoint (d := d) a0
            (onePointToFin1CLM d g : SchwartzNPoint d 1)) :
              NPointDomain d 1 → ℂ)) := by
            ext x
            simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
              translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
        rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) =
          tsupport (((translateSchwartzNPoint (d := d) a0
            (onePointToFin1CLM d g : SchwartzNPoint d 1)) :
              NPointDomain d 1 → ℂ)) from congr_arg tsupport hsup]
        exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
          (d := d) a0 ha0
          (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_ord
    (osSpatialTranslateHilbert (d := d) OS a)
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              hg_ord⟧) : OSHilbertSpace OS)) =
      (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
              hg_translated_ord⟧) : OSHilbertSpace OS)) := by
  dsimp
  rw [osSpatialTranslateHilbert_coe (d := d) OS a]
  apply congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS))
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro n
  by_cases hn : n = 1
  · subst hn
    have htrans :
        translateSchwartzNPoint (d := d) (Fin.cons 0 a)
          (onePointToFin1CLM d g : SchwartzNPoint d 1) =
        (onePointToFin1CLM d (SCV.translateSchwartz (-Fin.cons 0 a) g) :
          SchwartzNPoint d 1) := by
      ext x
      simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, spatialTranslatePositiveTimeBorchers_funcs, htrans]
  · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, spatialTranslatePositiveTimeBorchers_funcs, hn]

/-- Spatial translation of a concentrated positive-time vector is represented by
the corresponding spatially translated single Schwartz test. -/
theorem osSpatialTranslateHilbert_single_eq
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (a : Fin d → ℝ) :
    let a0 : SpacetimeDim d := Fin.cons 0 a
    let f_translated := translateSchwartzNPoint (d := d) a0 f
    let hf_translated_ord :
        tsupport (((f_translated : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n :=
      translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a0 (by simp [a0]) f hf_ord
    (osSpatialTranslateHilbert (d := d) OS a)
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS)) =
      (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single n f_translated hf_translated_ord⟧) :
            OSHilbertSpace OS)) := by
  dsimp
  rw [osSpatialTranslateHilbert_coe (d := d) OS a]
  apply congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS))
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro m
  by_cases hm : m = n
  · subst hm
    simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, spatialTranslatePositiveTimeBorchers_funcs]
  · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, spatialTranslatePositiveTimeBorchers_funcs, hm]

/-- The Hilbert-space spatial translations form an additive representation. -/
theorem osSpatialTranslateHilbert_comp
    (OS : OsterwalderSchraderAxioms d)
    (a b : Fin d → ℝ) :
    (osSpatialTranslateHilbert (d := d) OS a).comp
        (osSpatialTranslateHilbert (d := d) OS b) =
      osSpatialTranslateHilbert (d := d) OS (a + b) := by
  symm
  exact ContinuousLinearMap.extend_unique _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _)
    ((osSpatialTranslateHilbert (d := d) OS a).comp
      (osSpatialTranslateHilbert (d := d) OS b)) (by
      ext x
      change
        osSpatialTranslateHilbert (d := d) OS a
            ((osSpatialTranslateHilbert (d := d) OS b)
              (x : OSHilbertSpace OS)) =
          (((osSpatialTranslateContinuous (d := d) OS (a + b) x) :
            OSPreHilbertSpace OS) : OSHilbertSpace OS)
      rw [osSpatialTranslateHilbert_coe (d := d) OS b x]
      change
        osSpatialTranslateHilbert (d := d) OS a
            (((osSpatialTranslateLinear (d := d) OS b x) : OSPreHilbertSpace OS) :
              OSHilbertSpace OS) =
          (((osSpatialTranslateLinear (d := d) OS (a + b) x) :
            OSPreHilbertSpace OS) : OSHilbertSpace OS)
      rw [osSpatialTranslateHilbert_coe (d := d) OS a
        ((osSpatialTranslateLinear (d := d) OS b x) : OSPreHilbertSpace OS)]
      congr 1
      exact congrArg (fun f => f x)
        (osSpatialTranslateLinear_comp (d := d) OS a b))

/-- Zero spatial translation acts as the identity on the Hilbert completion. -/
theorem osSpatialTranslateHilbert_zero
    (OS : OsterwalderSchraderAxioms d) :
    osSpatialTranslateHilbert (d := d) OS 0 = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (osSpatialTranslateHilbert (d := d) OS 0).continuous
      continuous_id
  · intro a
    rw [osSpatialTranslateHilbert_coe (d := d) OS 0 a,
      osSpatialTranslateLinear_zero (d := d) OS]
    rfl

/-- Spatial translation by `-a` is a left inverse to translation by `a` on the
Hilbert completion. -/
theorem osSpatialTranslateHilbert_left_inv
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    (osSpatialTranslateHilbert (d := d) OS (-a)).comp
        (osSpatialTranslateHilbert (d := d) OS a) = 1 := by
  calc
    (osSpatialTranslateHilbert (d := d) OS (-a)).comp
        (osSpatialTranslateHilbert (d := d) OS a)
      = osSpatialTranslateHilbert (d := d) OS ((-a) + a) :=
          osSpatialTranslateHilbert_comp (d := d) OS (-a) a
    _ = osSpatialTranslateHilbert (d := d) OS 0 := by simp
    _ = 1 := osSpatialTranslateHilbert_zero (d := d) OS

/-- Spatial translation by `-a` is a right inverse to translation by `a` on the
Hilbert completion. -/
theorem osSpatialTranslateHilbert_right_inv
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    (osSpatialTranslateHilbert (d := d) OS a).comp
        (osSpatialTranslateHilbert (d := d) OS (-a)) = 1 := by
  calc
    (osSpatialTranslateHilbert (d := d) OS a).comp
        (osSpatialTranslateHilbert (d := d) OS (-a))
      = osSpatialTranslateHilbert (d := d) OS (a + (-a)) :=
          osSpatialTranslateHilbert_comp (d := d) OS a (-a)
    _ = osSpatialTranslateHilbert (d := d) OS 0 := by simp
    _ = 1 := osSpatialTranslateHilbert_zero (d := d) OS

/-- Spatial translation preserves the Hilbert inner product. -/
theorem osSpatialTranslateHilbert_inner_eq
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (x y : OSHilbertSpace OS) :
    @inner ℂ (OSHilbertSpace OS) _ ((osSpatialTranslateHilbert (d := d) OS a) x)
        ((osSpatialTranslateHilbert (d := d) OS a) y) =
      @inner ℂ (OSHilbertSpace OS) _ x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      (((osSpatialTranslateHilbert (d := d) OS a).continuous.comp continuous_fst).inner
        ((osSpatialTranslateHilbert (d := d) OS a).continuous.comp continuous_snd))
      (continuous_fst.inner continuous_snd)
  · intro x y
    rw [osSpatialTranslateHilbert_coe (d := d) OS a x,
      osSpatialTranslateHilbert_coe (d := d) OS a y,
      UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
    exact osSpatialTranslateLinear_inner_eq (d := d) OS a x y

/-- The adjoint of the spatial translation by `a` is translation by `-a`. -/
theorem osSpatialTranslateHilbert_adjoint
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    ContinuousLinearMap.adjoint (osSpatialTranslateHilbert (d := d) OS a) =
      osSpatialTranslateHilbert (d := d) OS (-a) := by
  have h :
      osSpatialTranslateHilbert (d := d) OS (-a) =
        ContinuousLinearMap.adjoint (osSpatialTranslateHilbert (d := d) OS a) := by
    apply (ContinuousLinearMap.eq_adjoint_iff
      (osSpatialTranslateHilbert (d := d) OS (-a))
      (osSpatialTranslateHilbert (d := d) OS a)).2
    intro x y
    have hy :
        (osSpatialTranslateHilbert (d := d) OS (-a))
            ((osSpatialTranslateHilbert (d := d) OS a) y) = y := by
      have h' := congrArg (fun f => f y) (osSpatialTranslateHilbert_left_inv (d := d) OS a)
      simpa using h'
    calc
      @inner ℂ (OSHilbertSpace OS) _
          ((osSpatialTranslateHilbert (d := d) OS (-a)) x) y
        = @inner ℂ (OSHilbertSpace OS) _
            ((osSpatialTranslateHilbert (d := d) OS (-a)) x)
            ((osSpatialTranslateHilbert (d := d) OS (-a))
              ((osSpatialTranslateHilbert (d := d) OS a) y)) := by
                exact congrArg
                  (fun z =>
                    @inner ℂ (OSHilbertSpace OS) _
                      ((osSpatialTranslateHilbert (d := d) OS (-a)) x) z)
                  hy.symm
      _ = @inner ℂ (OSHilbertSpace OS) _
            x ((osSpatialTranslateHilbert (d := d) OS a) y) := by
              have hinner :
                  @inner ℂ (OSHilbertSpace OS) _
                      ((osSpatialTranslateHilbert (d := d) OS (-a)) x)
                      ((osSpatialTranslateHilbert (d := d) OS (-a))
                        ((osSpatialTranslateHilbert (d := d) OS a) y)) =
                    @inner ℂ (OSHilbertSpace OS) _
                      x ((osSpatialTranslateHilbert (d := d) OS a) y) :=
                osSpatialTranslateHilbert_inner_eq (d := d) OS (-a) x
                  ((osSpatialTranslateHilbert (d := d) OS a) y)
              exact hinner
  simpa using h.symm

/-- Spatial translation is unitary on the Hilbert completion: left inverse form. -/
theorem osSpatialTranslateHilbert_unitary_left
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    ContinuousLinearMap.adjoint (osSpatialTranslateHilbert (d := d) OS a) ∘L
        osSpatialTranslateHilbert (d := d) OS a = 1 := by
  rw [osSpatialTranslateHilbert_adjoint (d := d) OS a]
  exact osSpatialTranslateHilbert_left_inv (d := d) OS a

/-- Spatial translation is unitary on the Hilbert completion: right inverse form. -/
theorem osSpatialTranslateHilbert_unitary_right
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) :
    osSpatialTranslateHilbert (d := d) OS a ∘L
        ContinuousLinearMap.adjoint (osSpatialTranslateHilbert (d := d) OS a) = 1 := by
  rw [osSpatialTranslateHilbert_adjoint (d := d) OS a]
  exact osSpatialTranslateHilbert_right_inv (d := d) OS a

/-- The honest semigroup pairing is invariant under simultaneous spatial
translation of both positive-time vectors. -/
theorem semigroup_inner_spatial_translate_invariant
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (F G : PositiveTimeBorchersSequence d)
    (t : ℝ) (ht : 0 < t) :
    PositiveTimeBorchersSequence.osInner OS
      (spatialTranslatePositiveTimeBorchers (d := d) a F)
      (timeShiftPositiveTimeBorchersLocal (d := d) t ht
        (spatialTranslatePositiveTimeBorchers (d := d) a G)) =
    PositiveTimeBorchersSequence.osInner OS F
      (timeShiftPositiveTimeBorchersLocal (d := d) t ht G) := by
  have hcomm :
      ((timeShiftPositiveTimeBorchersLocal (d := d) t ht
          (spatialTranslatePositiveTimeBorchers (d := d) a G) :
            PositiveTimeBorchersSequence d) : BorchersSequence d) =
        ((spatialTranslatePositiveTimeBorchers (d := d) a
          (timeShiftPositiveTimeBorchersLocal (d := d) t ht G) :
            PositiveTimeBorchersSequence d) : BorchersSequence d) :=
    timeShiftPositiveTimeBorchersLocal_translate_toBorchers_eq
      (d := d) t ht a G
  unfold PositiveTimeBorchersSequence.osInner
  rw [hcomm]
  exact positiveTime_osInner_spatial_translate_eq (d := d) OS a F
    (timeShiftPositiveTimeBorchersLocal (d := d) t ht G)

/-- Weak continuity of the axis slice on the dense compact-support domain. -/
theorem continuous_inner_osSpatialTranslate_axis_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (i : Fin d)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))) :
    Continuous (fun t : ℝ =>
      @inner ℂ (OSPreHilbertSpace OS) _ (⟦F⟧ : OSPreHilbertSpace OS)
        ((osSpatialTranslateLinear (d := d) OS
            (t • (Pi.single i (1 : ℝ) : Fin d → ℝ)))
          (⟦G⟧ : OSPreHilbertSpace OS))) := by
  let v : Fin d → ℝ := Pi.single i (1 : ℝ)
  have hcont :
      Continuous (fun t : ℝ =>
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (translateBorchers (d := d) (Fin.cons 0 (t • v)) (G : BorchersSequence d))) := by
    unfold OSInnerProduct
    simp only [translateBorchers]
    apply continuous_finset_sum
    intro n hn
    apply continuous_finset_sum
    intro m hm
    let f_n : SchwartzNPoint d n := (F : BorchersSequence d).funcs n
    let g_m : SchwartzNPoint d m := (G : BorchersSequence d).funcs m
    let hterm : ℝ → ZeroDiagonalSchwartz d (n + m) := fun t =>
      let g_trans := translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) g_m
      ⟨f_n.osConjTensorProduct g_trans,
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
          (d := d) (n := n) (m := m) (f := f_n) (g := g_trans)
          (F.ordered_tsupport n)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) (a := Fin.cons 0 (t • v)) (ha0 := by simp)
            g_m (G.ordered_tsupport m))⟩
    have hshift :
        Continuous (fun t : ℝ =>
          translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) g_m) :=
      continuous_spatialTranslateSchwartzNPoint_of_isCompactSupport
        (d := d) g_m (hG_compact m) v
    have hbase :
        Continuous (fun t : ℝ =>
          f_n.osConjTensorProduct
            (translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) g_m)) := by
      simpa [SchwartzNPoint.osConjTensorProduct] using
        (SchwartzMap.tensorProduct_continuous_right f_n.osConj).comp hshift
    have hterm_cont : Continuous hterm := by
      exact hbase.subtype_mk (fun t =>
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
          (d := d) (n := n) (m := m) (f := f_n)
          (g := translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) g_m)
          (F.ordered_tsupport n)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) (a := Fin.cons 0 (t • v)) (ha0 := by simp)
            g_m (G.ordered_tsupport m)))
    let hscalar : ℝ → ℂ := fun t => OS.S (n + m) (hterm t)
    have hscalar_cont : Continuous hscalar := (OS.E0_tempered (n + m)).comp hterm_cont
    convert hscalar_cont using 1
    ext t
    simp [hscalar, hterm]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f_n.osConjTensorProduct
        (translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) g_m))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := n) (m := m) (f := f_n)
        (g := translateSchwartzNPoint (d := d) (Fin.cons 0 (t • v)) g_m)
        (F.ordered_tsupport n)
        (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
          (d := d) (a := Fin.cons 0 (t • v)) (ha0 := by simp)
          g_m (G.ordered_tsupport m)))]
  simpa [OSPreHilbertSpace.inner_eq, osSpatialTranslateLinear, osSpatialTranslate,
    PositiveTimeBorchersSequence.osInner, spatialTranslatePositiveTimeBorchers,
    translateBorchers, v] using hcont

/-- Strong continuity at `0` of the axis slice on the dense compact-support domain. -/
theorem tendsto_osSpatialTranslateLinear_axis_nhds_zero_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d) (i : Fin d)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))) :
    Filter.Tendsto
      (fun t : ℝ =>
        (osSpatialTranslateLinear (d := d) OS
          (t • (Pi.single i (1 : ℝ) : Fin d → ℝ)))
          (⟦F⟧ : OSPreHilbertSpace OS))
      (nhds 0)
      (nhds (⟦F⟧ : OSPreHilbertSpace OS)) := by
  let x0 : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
  let T : ℝ → OSPreHilbertSpace OS →ₗ[ℂ] OSPreHilbertSpace OS := fun t =>
    osSpatialTranslateLinear (d := d) OS
      (t • (Pi.single i (1 : ℝ) : Fin d → ℝ))
  have hinner_raw :
      Filter.Tendsto
        (fun t : ℝ => @inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0))
        (nhds 0)
        (nhds (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T 0 x0))) := by
    simpa [x0, T] using
      (((continuous_inner_osSpatialTranslate_axis_of_isCompactSupport
        (d := d) OS i F F hF_compact).continuousAt (x := 0)).tendsto)
  have hinner :
      Filter.Tendsto
        (fun t : ℝ => @inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0))
        (nhds 0)
        (nhds (@inner ℂ (OSPreHilbertSpace OS) _ x0 x0)) := by
    simpa [T, osSpatialTranslateLinear_zero] using hinner_raw
  have hkernel :
      Filter.Tendsto
        (fun t : ℝ => RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0)))
        (nhds 0)
        (nhds (RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 x0))) := by
    simpa [Function.comp] using
      (Complex.continuous_re.continuousAt.tendsto.comp hinner)
  have hxnorm :
      RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 x0) = ‖x0‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x0)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hδ : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  filter_upwards [Metric.tendsto_nhds.1 hkernel (ε ^ 2 / 2) hδ] with t hclose
  have hgap :
      ‖x0‖ ^ 2 - RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0)) < ε ^ 2 / 2 := by
    have hclose' :
        |RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0)) -
            (↑(‖x0‖ ^ 2) : ℂ).re| < ε ^ 2 / 2 := by
      simpa [Real.dist_eq] using hclose
    rcases abs_lt.mp hclose' with ⟨hleft, _hright⟩
    have hcast : ((↑(‖x0‖ ^ 2) : ℂ).re) = ‖x0‖ ^ 2 := by
      rfl
    nlinarith
  have hnorm_eq : ‖T t x0‖ = ‖x0‖ := by
    simpa [T, x0] using
      (osSpatialTranslateLinear_norm_eq (d := d) OS
        (t • (Pi.single i (1 : ℝ) : Fin d → ℝ)) x0)
  have hnorm_sq : ‖T t x0‖ ^ 2 = ‖x0‖ ^ 2 := by
    nlinarith [hnorm_eq, norm_nonneg (T t x0), norm_nonneg x0]
  have hexpand :
      ‖T t x0 - x0‖ ^ 2 =
        ‖T t x0‖ ^ 2 - 2 * RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0)) +
          ‖x0‖ ^ 2 := by
    rw [@norm_sub_sq ℂ (OSPreHilbertSpace OS) _ _ _]
    have hsym :
        RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ (T t x0) x0) =
          RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0)) := by
      simpa using inner_re_symm (𝕜 := ℂ) (T t x0) x0
    linarith
  have hnsq : ‖T t x0 - x0‖ ^ 2 < ε ^ 2 := by
    calc
      ‖T t x0 - x0‖ ^ 2
          = ‖T t x0‖ ^ 2 - 2 * RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0)) +
              ‖x0‖ ^ 2 := hexpand
      _ = 2 * (‖x0‖ ^ 2 - RCLike.re (@inner ℂ (OSPreHilbertSpace OS) _ x0 (T t x0))) := by
          rw [hnorm_sq]
          ring
      _ < 2 * (ε ^ 2 / 2) := by nlinarith
      _ = ε ^ 2 := by ring
  rw [dist_eq_norm]
  have hroot : ‖T t x0 - x0‖ < ε :=
    lt_of_pow_lt_pow_left₀ 2 hε.le (by simpa using hnsq)
  simpa [T, x0] using hroot

/-! ## Compact-support truncations for the dense positive-time core -/

private noncomputable def unitBallBumpSchwartzNPointRadius
    (n d : ℕ) (R : ℝ) (hR : 0 < R) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1))
    (OSReconstruction.unitBallBumpSchwartzPiRadius (n * (d + 1)) R hR)

private noncomputable def bumpTruncationRadiusNPoint {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) : SchwartzNPoint d n :=
  SchwartzMap.smulLeftCLM ℂ
    (unitBallBumpSchwartzNPointRadius n d
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)) f

private theorem unflatten_flattenSchwartzNPoint_local {n : ℕ}
    (f : SchwartzNPoint d n) :
    unflattenSchwartzNPoint (d := d) (flattenSchwartzNPoint (d := d) f) = f := by
  ext x
  simp [flattenSchwartzNPoint_apply]

private theorem bumpTruncationRadiusNPoint_eq_unflatten {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) :
    bumpTruncationRadiusNPoint (d := d) f N =
      unflattenSchwartzNPoint (d := d)
        (OSReconstruction.bumpTruncationRadius (flattenSchwartzNPoint (d := d) f) N) := by
  ext x
  rw [unflattenSchwartzNPoint_apply]
  rw [bumpTruncationRadiusNPoint]
  rw [OSReconstruction.bumpTruncationRadius]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [unitBallBumpSchwartzNPointRadius, flattenSchwartzNPoint_apply]

def compactApproxPositiveTimeBorchers
    (F : PositiveTimeBorchersSequence d) (N : ℕ) :
    PositiveTimeBorchersSequence d where
  toBorchersSequence :=
    { funcs := fun n => bumpTruncationRadiusNPoint (((F : BorchersSequence d).funcs n)) N
      bound := ((F : BorchersSequence d).bound)
      bound_spec := by
        intro n hn
        simp [bumpTruncationRadiusNPoint, (F : BorchersSequence d).bound_spec n hn] }
  ordered_tsupport := by
    intro n x hx
    change x ∈ tsupport
      ((((SchwartzMap.smulLeftCLM ℂ
          (unitBallBumpSchwartzNPointRadius n d
            (OSReconstruction.bumpTruncationRadiusValue N)
            (OSReconstruction.bumpTruncationRadiusValue_pos N)))
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) :
        SchwartzNPoint d n) : NPointDomain d n → ℂ) at hx
    have hsubset := SchwartzMap.tsupport_smulLeftCLM_subset
      (F := ℂ)
      (g := unitBallBumpSchwartzNPointRadius n d
        (OSReconstruction.bumpTruncationRadiusValue N)
        (OSReconstruction.bumpTruncationRadiusValue_pos N))
      (f := ((F : BorchersSequence d).funcs n : SchwartzNPoint d n))
    exact F.ordered_tsupport n (hsubset hx).1

@[simp] private theorem compactApproxPositiveTimeBorchers_funcs
    (F : PositiveTimeBorchersSequence d) (N n : ℕ) :
    (((compactApproxPositiveTimeBorchers (d := d) F N : PositiveTimeBorchersSequence d) :
        BorchersSequence d).funcs n : SchwartzNPoint d n) =
      bumpTruncationRadiusNPoint (d := d)
        (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)) N := rfl

theorem compactApproxPositiveTimeBorchers_component_compact
    (F : PositiveTimeBorchersSequence d) (N n : ℕ) :
    HasCompactSupport
      ((((compactApproxPositiveTimeBorchers F N : PositiveTimeBorchersSequence d) :
        BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  have hflat :
      HasCompactSupport
        (((OSReconstruction.bumpTruncationRadius
          (flattenSchwartzNPoint (d := d)
            (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) N :
            SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) :
          (Fin (n * (d + 1)) → ℝ) → ℂ)) := by
    simpa [OSReconstruction.bumpTruncationRadius] using
      (OSReconstruction.hasCompactSupport_cutoff_mul_radius
        (OSReconstruction.bumpTruncationRadiusValue N)
        (OSReconstruction.bumpTruncationRadiusValue_pos N)
        (flattenSchwartzNPoint (d := d)
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))))
  rw [compactApproxPositiveTimeBorchers_funcs (d := d)]
  rw [bumpTruncationRadiusNPoint_eq_unflatten (d := d)]
  simpa using hflat.comp_homeomorph (flattenCLEquivReal n (d + 1)).toHomeomorph

theorem tendsto_compactApproxPositiveTimeBorchers_component
    (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((compactApproxPositiveTimeBorchers F N : PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs n : SchwartzNPoint d n))
      Filter.atTop
      (nhds (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) := by
  have hflat :
      Filter.Tendsto
        (fun N : ℕ =>
          OSReconstruction.bumpTruncationRadius
            (flattenSchwartzNPoint (d := d)
              (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) N)
        Filter.atTop
        (nhds (flattenSchwartzNPoint (d := d)
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))) := by
    simpa using
      (SchwartzMap.tendsto_bump_truncation_nhds
        (flattenSchwartzNPoint (d := d)
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))))
  have hrew :
      (fun N : ℕ =>
        (((compactApproxPositiveTimeBorchers (d := d) F N :
            PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs n : SchwartzNPoint d n)) =
      fun N : ℕ =>
        bumpTruncationRadiusNPoint (d := d)
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)) N := by
    funext N
    simp [compactApproxPositiveTimeBorchers_funcs]
  rw [hrew]
  have hrew' :
      (fun N : ℕ =>
        bumpTruncationRadiusNPoint (d := d)
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)) N) =
      fun N : ℕ =>
        unflattenSchwartzNPoint (d := d)
          (OSReconstruction.bumpTruncationRadius
            (flattenSchwartzNPoint (d := d)
              (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) N) := by
    funext N
    rw [bumpTruncationRadiusNPoint_eq_unflatten (d := d)]
  rw [hrew']
  have hunflat :=
    ((unflattenSchwartzNPoint (d := d)).continuous.tendsto
      (flattenSchwartzNPoint (d := d)
        (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))).comp hflat
  simpa [Function.comp, unflatten_flattenSchwartzNPoint_local] using hunflat

private theorem tendsto_compactApproxPositiveTimeBorchers_diff_component
    (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((((compactApproxPositiveTimeBorchers (d := d) F N - F :
            PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs n : SchwartzNPoint d n)))
      Filter.atTop
      (nhds (0 : SchwartzNPoint d n)) := by
  have hconst :
      Filter.Tendsto
        (fun _ : ℕ =>
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))
        Filter.atTop
        (nhds (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) :=
    tendsto_const_nhds
  simpa [sub_eq_add_neg] using
    (tendsto_compactApproxPositiveTimeBorchers_component (d := d) F n).sub hconst

private theorem tendsto_compactApproxPositiveTimeBorchers_diff_pair
    (F : PositiveTimeBorchersSequence d) (n m : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((((compactApproxPositiveTimeBorchers (d := d) F N - F :
            PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs n : SchwartzNPoint d n)).osConjTensorProduct
          ((((compactApproxPositiveTimeBorchers (d := d) F N - F :
            PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs m : SchwartzNPoint d m)))
      Filter.atTop
      (nhds (0 : SchwartzNPoint d (n + m))) := by
  have hprod :
      Filter.Tendsto
        (fun N : ℕ =>
          ( ((((compactApproxPositiveTimeBorchers (d := d) F N - F :
                PositiveTimeBorchersSequence d) :
              BorchersSequence d).funcs n : SchwartzNPoint d n)),
            ((((compactApproxPositiveTimeBorchers (d := d) F N - F :
                PositiveTimeBorchersSequence d) :
              BorchersSequence d).funcs m : SchwartzNPoint d m)) ))
        Filter.atTop
        (nhds ((0 : SchwartzNPoint d n), (0 : SchwartzNPoint d m))) := by
    exact (tendsto_compactApproxPositiveTimeBorchers_diff_component (d := d) F n).prodMk_nhds
      (tendsto_compactApproxPositiveTimeBorchers_diff_component (d := d) F m)
  simpa using
    ((SchwartzNPoint.osConjTensorProduct_continuous (d := d) (n := n) (m := m)).continuousAt.tendsto.comp
      hprod)

private noncomputable def compactApproxPositiveTimeBorchers_diff_pairZeroDiag
    (F : PositiveTimeBorchersSequence d) (n m N : ℕ) :
    ZeroDiagonalSchwartz d (n + m) := by
  let Δ : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers (d := d) F N - F
  refine ⟨((((Δ : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
      SchwartzNPoint d n)).osConjTensorProduct
        ((((Δ : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs m :
          SchwartzNPoint d m)), ?_⟩
  exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    (d := d)
    (f := (((Δ : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n : SchwartzNPoint d n))
    (g := (((Δ : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs m : SchwartzNPoint d m))
    (Δ.ordered_tsupport n) (Δ.ordered_tsupport m)

private theorem tendsto_compactApproxPositiveTimeBorchers_diff_pair_schwinger
    (OS : OsterwalderSchraderAxioms d) (F : PositiveTimeBorchersSequence d) (n m : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        OS.S (n + m)
          (compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N))
      Filter.atTop
      (nhds 0) := by
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N)
        Filter.atTop
        (nhds (0 : ZeroDiagonalSchwartz d (n + m))) := by
    rw [tendsto_subtype_rng]
    simpa [compactApproxPositiveTimeBorchers_diff_pairZeroDiag] using
      tendsto_compactApproxPositiveTimeBorchers_diff_pair (d := d) F n m
  have hmain :
      Filter.Tendsto
        (((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)) :
            ZeroDiagonalSchwartz d (n + m) → ℂ) ∘
          fun N : ℕ => compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N)
        Filter.atTop
        (nhds
          (((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)) :
            ZeroDiagonalSchwartz d (n + m) → ℂ) 0)) :=
    ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).continuous.tendsto 0).comp hsub
  have hzero :
      (((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)) :
          ZeroDiagonalSchwartz d (n + m) → ℂ) 0) = 0 := by
    simpa [OsterwalderSchraderAxioms.schwingerCLM] using
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).map_zero
  have hzero' : OS.S (n + m) (0 : ZeroDiagonalSchwartz d (n + m)) = 0 := by
    simpa [OsterwalderSchraderAxioms.schwingerCLM] using hzero
  have hmain' :
      Filter.Tendsto
        (fun N : ℕ =>
          OS.S (n + m)
            (compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N))
        Filter.atTop
        (nhds (OS.S (n + m) 0)) := by
    simpa [compactApproxPositiveTimeBorchers_diff_pairZeroDiag, ContinuousLinearMap.comp_apply,
      OsterwalderSchraderAxioms.schwingerCLM, Function.comp] using hmain
  simpa [hzero'] using hmain'

private theorem tendsto_compactApproxPositiveTimeBorchers_diff_osInner
    (OS : OsterwalderSchraderAxioms d) (F : PositiveTimeBorchersSequence d) :
    Filter.Tendsto
      (fun N : ℕ =>
        PositiveTimeBorchersSequence.osInner OS
          (compactApproxPositiveTimeBorchers (d := d) F N - F)
          (compactApproxPositiveTimeBorchers (d := d) F N - F))
      Filter.atTop
      (nhds 0) := by
  have hsum_inner :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
            ∑ m ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
              OS.S (n + m)
                (compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N))
        Filter.atTop
        (nhds (0 : ℂ)) := by
    have hinner : ∀ n : ℕ, ∀ s : Finset ℕ,
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ m ∈ s,
              OS.S (n + m)
                (compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N))
          Filter.atTop
          (nhds (0 : ℂ)) := by
      intro n s
      classical
      refine Finset.induction_on (s := s) ?_ ?_
      · simp
      · intro m s hm ih
        simpa [Finset.sum_insert, hm] using
          (tendsto_compactApproxPositiveTimeBorchers_diff_pair_schwinger
            (d := d) OS F n m).add ih
    have houter : ∀ s : Finset ℕ,
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ n ∈ s,
              ∑ m ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
                OS.S (n + m)
                  (compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N))
          Filter.atTop
          (nhds (0 : ℂ)) := by
      intro s
      classical
      refine Finset.induction_on (s := s) ?_ ?_
      · simp
      · intro n s hn ih
        simpa [Finset.sum_insert, hn] using
          (hinner n (Finset.range (((F : BorchersSequence d).bound) + 1))).add ih
    classical
    exact houter (Finset.range (((F : BorchersSequence d).bound) + 1))
  have hEq :
      ∀ N : ℕ,
        ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
          ∑ m ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
            OS.S (n + m)
              (compactApproxPositiveTimeBorchers_diff_pairZeroDiag (d := d) F n m N) =
        PositiveTimeBorchersSequence.osInner OS
          (compactApproxPositiveTimeBorchers (d := d) F N - F)
          (compactApproxPositiveTimeBorchers (d := d) F N - F) := by
    intro N
    unfold PositiveTimeBorchersSequence.osInner OSInnerProduct
    simp [compactApproxPositiveTimeBorchers, BorchersSequence.sub_bound, max_self]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    let fN : SchwartzNPoint d n :=
      bumpTruncationRadiusNPoint (d := d) (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)) N -
        ((F : BorchersSequence d).funcs n : SchwartzNPoint d n)
    let gN : SchwartzNPoint d m :=
      bumpTruncationRadiusNPoint (d := d) (((F : BorchersSequence d).funcs m : SchwartzNPoint d m)) N -
        ((F : BorchersSequence d).funcs m : SchwartzNPoint d m)
    have hvanish :
        VanishesToInfiniteOrderOnCoincidence (fN.osConjTensorProduct gN) := by
      exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (f := fN) (g := gN)
        ((compactApproxPositiveTimeBorchers (d := d) F N - F).ordered_tsupport n)
        ((compactApproxPositiveTimeBorchers (d := d) F N - F).ordered_tsupport m)
    have hclass :
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (fN.osConjTensorProduct gN)) =
          OS.S (n + m) ⟨fN.osConjTensorProduct gN, hvanish⟩ := by
      exact congrArg (fun z : ZeroDiagonalSchwartz d (n + m) => OS.S (n + m) z)
        (ZeroDiagonalSchwartz.ofClassical_of_vanishes
          (f := fN.osConjTensorProduct gN) hvanish)
    simpa [fN, gN, compactApproxPositiveTimeBorchers, compactApproxPositiveTimeBorchers_funcs]
      using hclass.symm
  refine Filter.Tendsto.congr' ?_ hsum_inner
  exact Filter.Eventually.of_forall hEq

/-- Lower-layer positive-time OS Hilbert vector.  This duplicates the direct
completion representative under a name available before
`OSToWightmanPositivity.lean`, so theorem-3 closure support can be used by
`OSToWightmanBoundaryValues.lean` without an import cycle. -/
noncomputable def positiveTimeBorchersVectorCore
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))

/-- Positive-time Borchers vectors are dense in the OS Hilbert completion. -/
theorem positiveTimeBorchersVectorCore_dense
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (positiveTimeBorchersVectorCore (d := d) OS)) := by
  have hrange :
      Set.range (positiveTimeBorchersVectorCore (d := d) OS) =
        Set.range ((↑) : OSPreHilbertSpace OS → OSHilbertSpace OS) := by
    ext x
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨(⟦F⟧ : OSPreHilbertSpace OS), rfl⟩
    · rintro ⟨xpre, rfl⟩
      induction xpre using Quotient.inductionOn with
      | h F =>
          exact ⟨F, rfl⟩
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

/-- Compact positive-time Borchers cutoffs converge to the original
positive-time OS Hilbert vector. -/
theorem positiveTimeBorchersVectorCore_compactApprox_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    Filter.Tendsto
      (fun N : ℕ =>
        positiveTimeBorchersVectorCore (d := d) OS
          (compactApproxPositiveTimeBorchers (d := d) F N))
      Filter.atTop
      (nhds (positiveTimeBorchersVectorCore (d := d) OS F)) := by
  let yN : ℕ → OSPreHilbertSpace OS := fun N =>
    (⟦compactApproxPositiveTimeBorchers (d := d) F N - F⟧ : OSPreHilbertSpace OS)
  have happrox_inner :=
    tendsto_compactApproxPositiveTimeBorchers_diff_osInner (d := d) OS F
  have happrox_norm :
      Filter.Tendsto
        (fun N : ℕ => ‖yN N‖)
        Filter.atTop
        (nhds (0 : ℝ)) := by
    have hkernel :
        Filter.Tendsto
          (fun N : ℕ => ‖yN N‖ ^ 2)
          Filter.atTop
          (nhds (0 : ℝ)) := by
      have hre :
          Filter.Tendsto
            (fun N : ℕ =>
              RCLike.re
                (PositiveTimeBorchersSequence.osInner OS
                  (compactApproxPositiveTimeBorchers (d := d) F N - F)
                  (compactApproxPositiveTimeBorchers (d := d) F N - F)))
            Filter.atTop
            (nhds (0 : ℝ)) := by
        simpa [Function.comp] using
          (Complex.continuous_re.continuousAt.tendsto.comp happrox_inner)
      have hEq_kernel :
          (fun N : ℕ => ‖yN N‖ ^ 2) =
          (fun N : ℕ =>
            RCLike.re
              (PositiveTimeBorchersSequence.osInner OS
                (compactApproxPositiveTimeBorchers (d := d) F N - F)
                (compactApproxPositiveTimeBorchers (d := d) F N - F))) := by
        funext N
        have hnorm :=
          congrArg RCLike.re (inner_self_eq_norm_sq (𝕜 := ℂ) (yN N))
        have hinner :
            @inner ℂ (OSPreHilbertSpace OS)
                (OSPreHilbertSpace.instInner OS) (yN N) (yN N) =
              PositiveTimeBorchersSequence.osInner OS
                (compactApproxPositiveTimeBorchers (d := d) F N - F)
                (compactApproxPositiveTimeBorchers (d := d) F N - F) := by
          simpa [yN] using
            (OSPreHilbertSpace.inner_eq (OS := OS)
              (compactApproxPositiveTimeBorchers (d := d) F N - F)
              (compactApproxPositiveTimeBorchers (d := d) F N - F))
        calc
          ‖yN N‖ ^ 2 =
              RCLike.re
                (@inner ℂ (OSPreHilbertSpace OS)
                  (OSPreHilbertSpace.instInner OS) (yN N) (yN N)) := by
            simpa using hnorm.symm
          _ = RCLike.re
                (PositiveTimeBorchersSequence.osInner OS
                  (compactApproxPositiveTimeBorchers (d := d) F N - F)
                  (compactApproxPositiveTimeBorchers (d := d) F N - F)) := by
            exact congrArg RCLike.re hinner
      exact hEq_kernel.symm ▸ hre
    refine Metric.tendsto_nhds.2 ?_
    intro η hη
    have hη2 : (0 : ℝ) < η ^ 2 := sq_pos_of_pos hη
    filter_upwards [Metric.tendsto_nhds.1 hkernel (η ^ 2) hη2] with N hclose
    have hnsq : ‖yN N‖ ^ 2 < η ^ 2 := by
      simpa [Real.dist_eq] using hclose
    exact lt_of_pow_lt_pow_left₀ 2 hη.le (by simpa using hnsq)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 happrox_norm ε hε] with N hN
  rw [dist_eq_norm]
  let xFN_pre : OSPreHilbertSpace OS :=
    (⟦compactApproxPositiveTimeBorchers (d := d) F N⟧ : OSPreHilbertSpace OS)
  let xF_pre : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
  have hcoediff :
      (((xFN_pre - xF_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) =
        positiveTimeBorchersVectorCore (d := d) OS
            (compactApproxPositiveTimeBorchers (d := d) F N) -
          positiveTimeBorchersVectorCore (d := d) OS F := by
    simpa [positiveTimeBorchersVectorCore, xFN_pre, xF_pre] using
      (UniformSpace.Completion.coe_sub xFN_pre xF_pre)
  have hpre : xFN_pre - xF_pre = yN N := by
    dsimp [xFN_pre, xF_pre, yN]
    rfl
  calc
    ‖positiveTimeBorchersVectorCore (d := d) OS
          (compactApproxPositiveTimeBorchers (d := d) F N) -
        positiveTimeBorchersVectorCore (d := d) OS F‖ =
        ‖(((xFN_pre - xF_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS))‖ := by
          rw [← hcoediff]
    _ = ‖((yN N : OSPreHilbertSpace OS) : OSHilbertSpace OS)‖ := by
          rw [hpre]
    _ < ε := by
          simpa using hN

private theorem osSpatialTranslateHilbert_norm_eq
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ)
    (x : OSHilbertSpace OS) :
    ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ := by
  have hsq :
      ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ((osSpatialTranslateHilbert (d := d) OS a) x),
      osSpatialTranslateHilbert_inner_eq, inner_self_eq_norm_sq]
  nlinarith [norm_nonneg ((osSpatialTranslateHilbert (d := d) OS a) x), norm_nonneg x]

private theorem tendsto_osSpatialTranslateHilbert_axis_nhds_zero
    (OS : OsterwalderSchraderAxioms d) (i : Fin d)
    (x : OSHilbertSpace OS) :
    Filter.Tendsto
      (fun t : ℝ =>
        osSpatialTranslateHilbert (d := d) OS
          (t • (Pi.single i (1 : ℝ) : Fin d → ℝ)) x)
      (nhds 0)
      (nhds x) := by
  let v : Fin d → ℝ := Pi.single i (1 : ℝ)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hε5 : 0 < ε / 5 := by positivity
  have hdense :
      Dense (Set.range (↑· : OSPreHilbertSpace OS → OSHilbertSpace OS)) := by
    exact UniformSpace.Completion.denseRange_coe
  have hx_mem :
      x ∈ closure (Set.range (↑· : OSPreHilbertSpace OS → OSHilbertSpace OS)) := by
    simpa [hdense.closure_eq]
  rw [Metric.mem_closure_iff] at hx_mem
  rcases hx_mem (ε / 5) hε5 with ⟨y, hy_range, hy_close⟩
  rcases hy_range with ⟨y0, rfl⟩
  induction y0 using Quotient.inductionOn with
  | h F =>
      have happrox_inner :=
        tendsto_compactApproxPositiveTimeBorchers_diff_osInner (d := d) OS F
      let yN : ℕ → OSPreHilbertSpace OS := fun N =>
        (⟦compactApproxPositiveTimeBorchers (d := d) F N - F⟧ : OSPreHilbertSpace OS)
      have happrox_norm :
          Filter.Tendsto
            (fun N : ℕ => ‖yN N‖)
            Filter.atTop
            (nhds (0 : ℝ)) := by
        have hkernel :
            Filter.Tendsto
              (fun N : ℕ => ‖yN N‖ ^ 2)
              Filter.atTop
              (nhds (0 : ℝ)) := by
          have hre :
              Filter.Tendsto
                (fun N : ℕ =>
                  RCLike.re
                    (PositiveTimeBorchersSequence.osInner OS
                      (compactApproxPositiveTimeBorchers (d := d) F N - F)
                      (compactApproxPositiveTimeBorchers (d := d) F N - F)))
                Filter.atTop
                (nhds (0 : ℝ)) := by
            simpa [Function.comp] using
              (Complex.continuous_re.continuousAt.tendsto.comp happrox_inner)
          have hEq_kernel :
              (fun N : ℕ => ‖yN N‖ ^ 2) =
              (fun N : ℕ =>
                RCLike.re
                  (PositiveTimeBorchersSequence.osInner OS
                    (compactApproxPositiveTimeBorchers (d := d) F N - F)
                    (compactApproxPositiveTimeBorchers (d := d) F N - F))) := by
            funext N
            have hnorm :=
              congrArg RCLike.re (inner_self_eq_norm_sq (𝕜 := ℂ) (yN N))
            have hinner :
                @inner ℂ (OSPreHilbertSpace OS)
                    (OSPreHilbertSpace.instInner OS) (yN N) (yN N) =
                  PositiveTimeBorchersSequence.osInner OS
                    (compactApproxPositiveTimeBorchers (d := d) F N - F)
                    (compactApproxPositiveTimeBorchers (d := d) F N - F) := by
              simpa [yN] using
                (OSPreHilbertSpace.inner_eq (OS := OS)
                  (compactApproxPositiveTimeBorchers (d := d) F N - F)
                  (compactApproxPositiveTimeBorchers (d := d) F N - F))
            calc
              ‖yN N‖ ^ 2 =
                  RCLike.re
                    (@inner ℂ (OSPreHilbertSpace OS)
                      (OSPreHilbertSpace.instInner OS) (yN N) (yN N)) := by
                simpa using hnorm.symm
              _ = RCLike.re
                    (PositiveTimeBorchersSequence.osInner OS
                      (compactApproxPositiveTimeBorchers (d := d) F N - F)
                      (compactApproxPositiveTimeBorchers (d := d) F N - F)) := by
                exact congrArg RCLike.re hinner
          exact hEq_kernel.symm ▸ hre
        refine Metric.tendsto_nhds.2 ?_
        intro η hη
        have hη2 : (0 : ℝ) < η ^ 2 := sq_pos_of_pos hη
        filter_upwards [Metric.tendsto_nhds.1 hkernel (η ^ 2) hη2] with N hclose
        have hnsq : ‖yN N‖ ^ 2 < η ^ 2 := by
          simpa [Real.dist_eq] using hclose
        have hroot : ‖yN N‖ < η :=
          lt_of_pow_lt_pow_left₀ 2 hη.le (by simpa using hnsq)
        simpa [yN] using hroot
      have happrox_event :
          ∀ᶠ N : ℕ in Filter.atTop,
            ‖yN N‖ < ε / 5 := by
        simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 happrox_norm (ε / 5) hε5)
      rcases Filter.mem_atTop_sets.mp happrox_event with ⟨N0, hN0⟩
      let F0 := compactApproxPositiveTimeBorchers (d := d) F N0
      let zF0 : OSPreHilbertSpace OS := (⟦F0 - F⟧ : OSPreHilbertSpace OS)
      let xF_pre : OSPreHilbertSpace OS := (⟦F⟧ : OSPreHilbertSpace OS)
      let xF0_pre : OSPreHilbertSpace OS := (⟦F0⟧ : OSPreHilbertSpace OS)
      let xF : OSHilbertSpace OS := ((xF_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)
      let xF0 : OSHilbertSpace OS := ((xF0_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)
      have hF0 :
          ‖((zF0 : OSPreHilbertSpace OS) : OSHilbertSpace OS)‖ < ε / 5 := by
        simpa [zF0, yN, F0] using hN0 N0 le_rfl
      have hcore :=
        tendsto_osSpatialTranslateLinear_axis_nhds_zero_of_isCompactSupport
          (d := d) OS i F0 (compactApproxPositiveTimeBorchers_component_compact (d := d) F N0)
      have hcore_event :
          ∀ᶠ t : ℝ in nhds 0,
            ‖(osSpatialTranslateLinear (d := d) OS (t • v) xF0_pre) - xF0_pre‖ < ε / 5 := by
        simpa [xF0_pre, dist_eq_norm] using (Metric.tendsto_nhds.1 hcore (ε / 5) hε5)
      filter_upwards [hcore_event] with t ht
      rw [dist_eq_norm] at hy_close ⊢
      have hfirst :
          ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) x -
              (osSpatialTranslateHilbert (d := d) OS (t • v))
                xF‖ < ε / 5 := by
        have hUdiffx :
            ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) x -
                (osSpatialTranslateHilbert (d := d) OS (t • v))
                  xF‖ =
              ‖x - xF‖ := by
          calc
            ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) x -
                (osSpatialTranslateHilbert (d := d) OS (t • v)) xF‖
                = ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) (x - xF)‖ := by
                    rw [ContinuousLinearMap.map_sub]
            _ = ‖x - xF‖ := by
                  exact osSpatialTranslateHilbert_norm_eq (d := d) OS (t • v) (x - xF)
        simpa [xF, hUdiffx] using hy_close
      have hfourthNormEq :
          ‖xF0 - xF‖ = ‖((zF0 : OSPreHilbertSpace OS) : OSHilbertSpace OS)‖ := by
        have hcoediff :
            (((xF0_pre - xF_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) = xF0 - xF := by
          simpa [xF, xF0] using (UniformSpace.Completion.coe_sub xF0_pre xF_pre)
        have hzF0 : xF0_pre - xF_pre = zF0 := by
          dsimp [xF0_pre, xF_pre, zF0, F0]
          rfl
        calc
          ‖xF0 - xF‖ = ‖(((xF0_pre - xF_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS))‖ := by
            rw [← hcoediff]
          _ = ‖((zF0 : OSPreHilbertSpace OS) : OSHilbertSpace OS)‖ := by
            rw [hzF0]
      have hsecond :
          ‖(osSpatialTranslateHilbert (d := d) OS (t • v))
                xF -
              (osSpatialTranslateHilbert (d := d) OS (t • v))
                xF0‖ < ε / 5 := by
        have hUdiff :
            ‖(osSpatialTranslateHilbert (d := d) OS (t • v))
                  xF -
                (osSpatialTranslateHilbert (d := d) OS (t • v))
                  xF0‖ =
              ‖xF - xF0‖ := by
          calc
            ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) xF -
                (osSpatialTranslateHilbert (d := d) OS (t • v)) xF0‖
                = ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) (xF - xF0)‖ := by
                    rw [ContinuousLinearMap.map_sub]
            _ = ‖xF - xF0‖ := by
                  exact osSpatialTranslateHilbert_norm_eq (d := d) OS (t • v) (xF - xF0)
        have hxF0 : ‖xF - xF0‖ < ε / 5 := by
          rw [norm_sub_rev, hfourthNormEq]
          exact hF0
        simpa [hUdiff] using hxF0
      have hthird :
          ‖(osSpatialTranslateHilbert (d := d) OS (t • v))
                xF0 -
              xF0‖ < ε / 5 := by
        have ht' :
            ‖(((osSpatialTranslateLinear (d := d) OS (t • v) xF0_pre) - xF0_pre :
                OSPreHilbertSpace OS) : OSHilbertSpace OS)‖ < ε / 5 := by
          simpa using ht
        have hthird_norm :
            ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) xF0 - xF0‖ =
              ‖(((osSpatialTranslateLinear (d := d) OS (t • v) xF0_pre) - xF0_pre :
                  OSPreHilbertSpace OS) : OSHilbertSpace OS)‖ := by
          have hcoediff :
              ((((osSpatialTranslateLinear (d := d) OS (t • v) xF0_pre) - xF0_pre :
                    OSPreHilbertSpace OS) : OSHilbertSpace OS)) =
                (osSpatialTranslateHilbert (d := d) OS (t • v)) xF0 - xF0 := by
            simpa [xF0, osSpatialTranslateHilbert_coe (d := d) OS (t • v) xF0_pre] using
              (UniformSpace.Completion.coe_sub
                ((osSpatialTranslateLinear (d := d) OS (t • v) xF0_pre))
                xF0_pre)
          rw [← hcoediff]
        rw [hthird_norm]
        exact ht'
      have hfourth :
          ‖xF0 - xF‖ < ε / 5 := by
        exact lt_of_eq_of_lt hfourthNormEq hF0
      have hfifth :
          ‖xF - x‖ < ε / 5 := by
        simpa [xF, norm_sub_rev] using hy_close
      let a1 : OSHilbertSpace OS :=
        (osSpatialTranslateHilbert (d := d) OS (t • v)) x -
          (osSpatialTranslateHilbert (d := d) OS (t • v)) xF
      let a2 : OSHilbertSpace OS :=
        (osSpatialTranslateHilbert (d := d) OS (t • v)) xF -
          (osSpatialTranslateHilbert (d := d) OS (t • v)) xF0
      let a3 : OSHilbertSpace OS :=
        (osSpatialTranslateHilbert (d := d) OS (t • v)) xF0 - xF0
      let a4 : OSHilbertSpace OS := xF0 - xF
      let a5 : OSHilbertSpace OS := xF - x
      have ha1 : ‖a1‖ < ε / 5 := by
        simpa [a1] using hfirst
      have ha2 : ‖a2‖ < ε / 5 := by
        simpa [a2] using hsecond
      have ha3 : ‖a3‖ < ε / 5 := by
        simpa [a3] using hthird
      have ha4 : ‖a4‖ < ε / 5 := by
        simpa [a4] using hfourth
      have ha5 : ‖a5‖ < ε / 5 := by
        simpa [a5] using hfifth
      have hdecomp :
          (osSpatialTranslateHilbert (d := d) OS (t • v)) x - x =
            a1 + (a2 + (a3 + (a4 + a5))) := by
        dsimp [a1, a2, a3, a4, a5]
        abel_nf
      calc
        ‖(osSpatialTranslateHilbert (d := d) OS (t • v)) x - x‖
            = ‖a1 + (a2 + (a3 + (a4 + a5)))‖ := by
              rw [hdecomp]
        _ ≤ ‖a1‖ + ‖a2 + (a3 + (a4 + a5))‖ := by
              exact norm_add_le _ _
        _ ≤ ‖a1‖ + (‖a2‖ + ‖a3 + (a4 + a5)‖) := by
              gcongr
              exact norm_add_le _ _
        _ ≤ ‖a1‖ + (‖a2‖ + (‖a3‖ + ‖a4 + a5‖)) := by
              gcongr
              exact norm_add_le _ _
        _ ≤ ‖a1‖ + (‖a2‖ + (‖a3‖ + (‖a4‖ + ‖a5‖))) := by
              gcongr
              exact norm_add_le _ _
        _ < ε / 5 + (ε / 5 + (ε / 5 + (ε / 5 + ε / 5))) := by
              exact add_lt_add ha1 (add_lt_add ha2 (add_lt_add ha3 (add_lt_add ha4 ha5)))
        _ = ε := by ring

/-- Strong continuity of the axis slice on the Hilbert completion. -/
theorem continuous_osSpatialTranslateHilbert_axis
    (OS : OsterwalderSchraderAxioms d) (i : Fin d)
    (x : OSHilbertSpace OS) :
    Continuous (fun t : ℝ =>
      osSpatialTranslateHilbert (d := d) OS
        (t • (Pi.single i (1 : ℝ) : Fin d → ℝ)) x) := by
  let v : Fin d → ℝ := Pi.single i (1 : ℝ)
  refine continuous_iff_continuousAt.2 ?_
  intro t
  have hzero :=
    tendsto_osSpatialTranslateHilbert_axis_nhds_zero (d := d) OS i
      ((osSpatialTranslateHilbert (d := d) OS (t • v)) x)
  have hshift : Filter.Tendsto (fun s : ℝ => s - t) (nhds t) (nhds 0) := by
    have hcont : Continuous (fun s : ℝ => s - t) := by
      fun_prop
    simpa using (hcont.continuousAt : ContinuousAt (fun s : ℝ => s - t) t).tendsto
  have hEq :
      ∀ s : ℝ,
        osSpatialTranslateHilbert (d := d) OS (s • v) x =
          osSpatialTranslateHilbert (d := d) OS ((s - t) • v)
            ((osSpatialTranslateHilbert (d := d) OS (t • v)) x) := by
    intro s
    have hadd : (s - t) • v + t • v = s • v := by
      ext j
      simp [v, sub_eq_add_neg]
      ring
    calc
      osSpatialTranslateHilbert (d := d) OS (s • v) x
          = osSpatialTranslateHilbert (d := d) OS (((s - t) • v) + (t • v)) x := by
              rw [hadd]
      _ = ((osSpatialTranslateHilbert (d := d) OS ((s - t) • v)).comp
            (osSpatialTranslateHilbert (d := d) OS (t • v))) x := by
              rw [← osSpatialTranslateHilbert_comp (d := d) OS ((s - t) • v) (t • v)]
      _ = osSpatialTranslateHilbert (d := d) OS ((s - t) • v)
            ((osSpatialTranslateHilbert (d := d) OS (t • v)) x) := rfl
  have hmain :
      Filter.Tendsto
        (fun s : ℝ =>
          osSpatialTranslateHilbert (d := d) OS ((s - t) • v)
            ((osSpatialTranslateHilbert (d := d) OS (t • v)) x))
        (nhds t)
        (nhds ((osSpatialTranslateHilbert (d := d) OS (t • v)) x)) := by
    simpa [v] using hzero.comp hshift
  exact hmain.congr' (Filter.Eventually.of_forall fun s => (hEq s).symm)

private theorem norm_sub_osSpatialTranslateHilbert_le_sum_axes
    (OS : OsterwalderSchraderAxioms d)
    (x : OSHilbertSpace OS)
    (a : Fin d → ℝ) :
    ‖(osSpatialTranslateHilbert (d := d) OS a) x - x‖ ≤
      ∑ i : Fin d,
        ‖(osSpatialTranslateHilbert (d := d) OS
            ((a i) • (Pi.single i (1 : ℝ) : Fin d → ℝ))) x - x‖ := by
  classical
  let e : Fin d → Fin d → ℝ := fun i => (Pi.single i (1 : ℝ) : Fin d → ℝ)
  have hs :
      ∀ s : Finset (Fin d),
        ‖(osSpatialTranslateHilbert (d := d) OS
              (Finset.sum s (fun i => (a i) • e i)) ) x - x‖ ≤
          Finset.sum s (fun i =>
            ‖(osSpatialTranslateHilbert (d := d) OS
                ((a i) • e i)) x - x‖) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa [osSpatialTranslateHilbert_zero]
    · intro i s hi hs_ind
      let b : Fin d → ℝ := Finset.sum s (fun j => (a j) • e j)
      have hcomp :
          (osSpatialTranslateHilbert (d := d) OS (b + (a i) • e i)) x =
            (osSpatialTranslateHilbert (d := d) OS b)
              ((osSpatialTranslateHilbert (d := d) OS
                  ((a i) • e i)) x) := by
        simpa [ContinuousLinearMap.comp_apply] using
          (congrArg (fun f : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS => f x)
            (osSpatialTranslateHilbert_comp (d := d) OS b
              ((a i) • e i))).symm
      have hdecomp :
          (osSpatialTranslateHilbert (d := d) OS (b + (a i) • e i)) x - x =
            (osSpatialTranslateHilbert (d := d) OS b)
                ((osSpatialTranslateHilbert (d := d) OS
                    ((a i) • e i)) x - x) +
              ((osSpatialTranslateHilbert (d := d) OS b) x - x) := by
        calc
          (osSpatialTranslateHilbert (d := d) OS (b + (a i) • e i)) x - x
              = (osSpatialTranslateHilbert (d := d) OS b)
                  ((osSpatialTranslateHilbert (d := d) OS
                      ((a i) • e i)) x) - x := by
                  rw [hcomp]
          _ =
              ((osSpatialTranslateHilbert (d := d) OS b)
                  ((osSpatialTranslateHilbert (d := d) OS
                      ((a i) • e i)) x) -
                (osSpatialTranslateHilbert (d := d) OS b) x) +
                ((osSpatialTranslateHilbert (d := d) OS b) x - x) := by
                  abel_nf
          _ =
              (osSpatialTranslateHilbert (d := d) OS b)
                  ((osSpatialTranslateHilbert (d := d) OS
                      ((a i) • e i)) x - x) +
                ((osSpatialTranslateHilbert (d := d) OS b) x - x) := by
                  rw [ContinuousLinearMap.map_sub]
      have hmain :
          ‖(osSpatialTranslateHilbert (d := d) OS
                (Finset.sum (insert i s) (fun j => (a j) • e j))) x - x‖ ≤
            ‖(osSpatialTranslateHilbert (d := d) OS ((a i) • e i)) x - x‖ +
              ‖(osSpatialTranslateHilbert (d := d) OS b) x - x‖ := by
        calc
          ‖(osSpatialTranslateHilbert (d := d) OS
                (Finset.sum (insert i s)
                  (fun j => (a j) • e j))) x - x‖
              = ‖(osSpatialTranslateHilbert (d := d) OS (b + (a i) • e i)) x - x‖ := by
                  congr 1
                  simp [b, e, hi, Finset.sum_insert, add_comm, add_left_comm, add_assoc]
          _ = ‖(osSpatialTranslateHilbert (d := d) OS b)
                  ((osSpatialTranslateHilbert (d := d) OS
                      ((a i) • e i)) x - x) +
                ((osSpatialTranslateHilbert (d := d) OS b) x - x)‖ := by
                  rw [hdecomp]
          _ ≤ ‖(osSpatialTranslateHilbert (d := d) OS b)
                  ((osSpatialTranslateHilbert (d := d) OS
                      ((a i) • e i)) x - x)‖ +
                ‖(osSpatialTranslateHilbert (d := d) OS b) x - x‖ := by
                  exact norm_add_le _ _
          _ = ‖(osSpatialTranslateHilbert (d := d) OS
                  ((a i) • e i)) x - x‖ +
                ‖(osSpatialTranslateHilbert (d := d) OS b) x - x‖ := by
                  congr 1
                  exact osSpatialTranslateHilbert_norm_eq (d := d) OS b
                    ((osSpatialTranslateHilbert (d := d) OS
                        ((a i) • e i)) x - x)
      have hsum :
          ‖(osSpatialTranslateHilbert (d := d) OS ((a i) • e i)) x - x‖ +
              ‖(osSpatialTranslateHilbert (d := d) OS b) x - x‖ ≤
            Finset.sum (insert i s) (fun j =>
              ‖(osSpatialTranslateHilbert (d := d) OS
                  ((a j) • e j)) x - x‖) := by
        calc
          ‖(osSpatialTranslateHilbert (d := d) OS ((a i) • e i)) x - x‖ +
              ‖(osSpatialTranslateHilbert (d := d) OS b) x - x‖
              ≤ ‖(osSpatialTranslateHilbert (d := d) OS
                    ((a i) • e i)) x - x‖ +
                  Finset.sum s (fun j =>
                    ‖(osSpatialTranslateHilbert (d := d) OS
                        ((a j) • e j)) x - x‖) := by
                    gcongr
          _ = Finset.sum (insert i s) (fun j =>
                ‖(osSpatialTranslateHilbert (d := d) OS
                    ((a j) • e j)) x - x‖) := by
                  simp [e, hi, Finset.sum_insert, add_comm]
      exact le_trans hmain hsum
  calc
    ‖(osSpatialTranslateHilbert (d := d) OS a) x - x‖
        = ‖(osSpatialTranslateHilbert (d := d) OS
              (∑ i : Fin d, (a i) • (Pi.single i (1 : ℝ) : Fin d → ℝ))) x - x‖ := by
              rw [← pi_eq_sum_univ' a]
    _ ≤ ∑ i : Fin d,
          ‖(osSpatialTranslateHilbert (d := d) OS
              ((a i) • e i)) x - x‖ := hs Finset.univ

private theorem continuousAt_zero_osSpatialTranslateHilbert
    (OS : OsterwalderSchraderAxioms d)
    (x : OSHilbertSpace OS) :
    ContinuousAt (fun a : Fin d → ℝ => osSpatialTranslateHilbert (d := d) OS a x) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hd_pos_nat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let η : ℝ := ε / d
  have hη : 0 < η := by
    dsimp [η]
    positivity
  choose δ hδ_pos hδ using
    fun i : Fin d =>
      (Metric.continuousAt_iff.mp
        ((continuous_osSpatialTranslateHilbert_axis (d := d) OS i x).continuousAt)) η hη
  let ρ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact (Finset.lt_inf'_iff _).2 (fun i _ => hδ_pos i)
  refine ⟨ρ, hρ_pos, ?_⟩
  intro a ha
  have hcoord :
      ∀ i : Fin d,
        ‖(osSpatialTranslateHilbert (d := d) OS
            ((a i) • (Pi.single i (1 : ℝ) : Fin d → ℝ))) x - x‖ < η := by
    intro i
    have hρ_le : ρ ≤ δ i := by
      dsimp [ρ]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    have hdist_i : dist (a i) 0 < δ i := by
      calc
        dist (a i) 0 = ‖a i‖ := by simp [dist_eq_norm]
        _ ≤ ‖a‖ := norm_le_pi_norm a i
        _ < ρ := by simpa [dist_eq_norm] using ha
        _ ≤ δ i := hρ_le
    have hi := hδ i hdist_i
    simpa [dist_eq_norm, osSpatialTranslateHilbert_zero] using hi
  calc
    dist ((osSpatialTranslateHilbert (d := d) OS a) x)
        ((osSpatialTranslateHilbert (d := d) OS 0) x)
        = ‖(osSpatialTranslateHilbert (d := d) OS a) x - x‖ := by
            simp [dist_eq_norm, osSpatialTranslateHilbert_zero]
    _ ≤ ∑ i : Fin d,
          ‖(osSpatialTranslateHilbert (d := d) OS
              ((a i) • (Pi.single i (1 : ℝ) : Fin d → ℝ))) x - x‖ :=
          norm_sub_osSpatialTranslateHilbert_le_sum_axes (d := d) OS x a
    _ < ∑ _i : Fin d, η := by
          exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hcoord i)
    _ = ε := by
          have hd_ne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (NeZero.ne d)
          calc
            (∑ _i : Fin d, η) = (d : ℝ) * η := by simp
            _ = (d : ℝ) * (ε / d) := by rfl
            _ = ε := by field_simp [hd_ne]

/-- Strong continuity of the full spatial translation action on the Hilbert
completion. -/
theorem continuous_osSpatialTranslateHilbert
    (OS : OsterwalderSchraderAxioms d)
    (x : OSHilbertSpace OS) :
    Continuous (fun a : Fin d → ℝ =>
      osSpatialTranslateHilbert (d := d) OS a x) := by
  refine continuous_iff_continuousAt.2 ?_
  intro a
  have hzero :=
    continuousAt_zero_osSpatialTranslateHilbert (d := d) OS
      ((osSpatialTranslateHilbert (d := d) OS a) x)
  have hshift : ContinuousAt (fun b : Fin d → ℝ => b - a) a := by
    have hcont : Continuous (fun b : Fin d → ℝ => b - a) := by
      fun_prop
    simpa using (hcont.continuousAt : ContinuousAt (fun b : Fin d → ℝ => b - a) a)
  have hEq :
      ∀ b : Fin d → ℝ,
        osSpatialTranslateHilbert (d := d) OS b x =
          osSpatialTranslateHilbert (d := d) OS (b - a)
            ((osSpatialTranslateHilbert (d := d) OS a) x) := by
    intro b
    have hadd : (b - a) + a = b := by
      ext j
      simp [sub_eq_add_neg]
    calc
      osSpatialTranslateHilbert (d := d) OS b x
          = osSpatialTranslateHilbert (d := d) OS (((b - a) + a)) x := by
              rw [hadd]
      _ = ((osSpatialTranslateHilbert (d := d) OS (b - a)).comp
            (osSpatialTranslateHilbert (d := d) OS a)) x := by
              rw [← osSpatialTranslateHilbert_comp (d := d) OS (b - a) a]
      _ = osSpatialTranslateHilbert (d := d) OS (b - a)
            ((osSpatialTranslateHilbert (d := d) OS a) x) := rfl
  have hcomp :
      ContinuousAt (fun b : Fin d → ℝ =>
        osSpatialTranslateHilbert (d := d) OS (b - a)
          ((osSpatialTranslateHilbert (d := d) OS a) x)) a := by
    simpa [Function.comp] using
      (ContinuousAt.comp_of_eq hzero hshift (by simp))
  have hEqfun :
      (fun b : Fin d → ℝ => osSpatialTranslateHilbert (d := d) OS b x) =
        (fun b : Fin d → ℝ =>
          osSpatialTranslateHilbert (d := d) OS (b - a)
            ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
    funext b
    exact hEq b
  simpa [hEqfun] using hcomp

/-- Joint continuity of the spatial translation action on the OS Hilbert space. -/
theorem continuous_osSpatialTranslateHilbert_jointly
    (OS : OsterwalderSchraderAxioms d) :
    Continuous (fun p : (Fin d → ℝ) × OSHilbertSpace OS =>
      osSpatialTranslateHilbert (d := d) OS p.1 p.2) := by
  refine continuous_iff_continuousAt.2 ?_
  intro p0
  rcases p0 with ⟨a0, x0⟩
  have hcontx0 : ContinuousAt
      (fun a : Fin d → ℝ => osSpatialTranslateHilbert (d := d) OS a x0) a0 :=
    (continuous_osSpatialTranslateHilbert (d := d) OS x0).continuousAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  rcases (Metric.continuousAt_iff.mp hcontx0) (ε / 2) hhalf with
    ⟨δ1, hδ1, hδ1prop⟩
  refine ⟨min δ1 (ε / 2), by positivity, ?_⟩
  intro p hp
  rcases p with ⟨b, y⟩
  rw [Prod.dist_eq] at hp
  have hp' := max_lt_iff.mp hp
  have hb : dist b a0 < δ1 := by
    exact lt_of_lt_of_le hp'.1 (min_le_left _ _)
  have hy : dist y x0 < ε / 2 := by
    exact lt_of_lt_of_le hp'.2 (min_le_right _ _)
  have hU : osSpatialTranslateHilbert (d := d) OS b ∈
      unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
    constructor
    · exact osSpatialTranslateHilbert_unitary_left (d := d) OS b
    · exact osSpatialTranslateHilbert_unitary_right (d := d) OS b
  have hdecomp :
      osSpatialTranslateHilbert (d := d) OS b y -
          osSpatialTranslateHilbert (d := d) OS a0 x0 =
        (osSpatialTranslateHilbert (d := d) OS b) (y - x0) +
          ((osSpatialTranslateHilbert (d := d) OS b) x0 -
            (osSpatialTranslateHilbert (d := d) OS a0) x0) := by
    rw [map_sub]
    abel_nf
  calc
    dist (osSpatialTranslateHilbert (d := d) OS b y)
        (osSpatialTranslateHilbert (d := d) OS a0 x0) =
          ‖osSpatialTranslateHilbert (d := d) OS b y -
            osSpatialTranslateHilbert (d := d) OS a0 x0‖ := by
            simp [dist_eq_norm]
    _ = ‖(osSpatialTranslateHilbert (d := d) OS b) (y - x0) +
          ((osSpatialTranslateHilbert (d := d) OS b) x0 -
            (osSpatialTranslateHilbert (d := d) OS a0) x0)‖ := by
            rw [hdecomp]
    _ ≤ ‖(osSpatialTranslateHilbert (d := d) OS b) (y - x0)‖ +
          ‖(osSpatialTranslateHilbert (d := d) OS b) x0 -
            (osSpatialTranslateHilbert (d := d) OS a0) x0‖ := by
            exact norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
            refine add_lt_add ?_ ?_
            · have hnorm :=
                ContinuousLinearMap.norm_map_of_mem_unitary
                  (u := osSpatialTranslateHilbert (d := d) OS b) hU (y - x0)
              rw [hnorm]
              simpa [dist_eq_norm] using hy
            · simpa [dist_eq_norm] using hδ1prop hb
    _ = ε := by ring

/-- Spatial translation commutes with the positive Euclidean time shift on the
honest OS quotient. -/
private theorem osSpatialTranslateLinear_commutes_osTimeShiftLinear
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) (t : ℝ) (ht : 0 < t) :
    (osSpatialTranslateLinear (d := d) OS a).comp
      (osTimeShiftLinear OS t ht) =
    (osTimeShiftLinear OS t ht).comp
      (osSpatialTranslateLinear (d := d) OS a) := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn with
  | h F =>
      exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun n => by
        simpa [timeShiftBorchers, translateBorchers] using
          (translateSchwartzNPoint_timeShiftSchwartzNPoint
            (d := d) (a := Fin.cons 0 a) (t := t)
            (((F : BorchersSequence d).funcs n) : SchwartzNPoint d n)))

/-- Spatial translation commutes with the Euclidean time semigroup. -/
theorem osSpatialTranslateHilbert_commutes_osTimeShiftHilbert
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (a : Fin d → ℝ) (t : ℝ) (ht : 0 < t) :
    (osSpatialTranslateHilbert (d := d) OS a).comp
      (osTimeShiftHilbert (d := d) OS lgc t ht) =
    (osTimeShiftHilbert (d := d) OS lgc t ht).comp
      (osSpatialTranslateHilbert (d := d) OS a) := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (((osSpatialTranslateHilbert (d := d) OS a).comp
          (osTimeShiftHilbert (d := d) OS lgc t ht)).continuous)
      (((osTimeShiftHilbert (d := d) OS lgc t ht).comp
          (osSpatialTranslateHilbert (d := d) OS a)).continuous)
  · intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [osTimeShiftHilbert_coe OS lgc t ht x]
    rw [osSpatialTranslateHilbert_coe (d := d) OS a
      ((osTimeShiftLinear OS t ht x) : OSPreHilbertSpace OS)]
    rw [osSpatialTranslateHilbert_coe (d := d) OS a x]
    rw [osTimeShiftHilbert_coe OS lgc t ht
      ((osSpatialTranslateLinear (d := d) OS a x) : OSPreHilbertSpace OS)]
    exact congrArg (fun y : OSPreHilbertSpace OS => (y : OSHilbertSpace OS))
      (congrArg (fun f => f x)
        (osSpatialTranslateLinear_commutes_osTimeShiftLinear
          (d := d) OS a t ht))

/-- Spatial translation commutes with the positive-real restriction of the
complex Euclidean time semigroup. -/
theorem osSpatialTranslateHilbert_commutes_osTimeShiftHilbertComplex_ofReal
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (a : Fin d → ℝ) (t : ℝ) (ht : 0 < t) :
    (osSpatialTranslateHilbert (d := d) OS a).comp
      (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) =
    (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)).comp
      (osSpatialTranslateHilbert (d := d) OS a) := by
  have hcommA :
      Commute
        (osSpatialTranslateHilbert (d := d) OS a)
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) := by
    change
      (osSpatialTranslateHilbert (d := d) OS a).comp
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos) =
      (osTimeShiftHilbert (d := d) OS lgc 1 one_pos).comp
        (osSpatialTranslateHilbert (d := d) OS a)
    simpa using
      osSpatialTranslateHilbert_commutes_osTimeShiftHilbert
        (d := d) OS lgc a 1 one_pos
  have hcommComplex :
      Commute
        (osSpatialTranslateHilbert (d := d) OS a)
        (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) := by
    simpa [osTimeShiftHilbertComplex] using
      (ContinuousLinearMap.Commute.spectralSemigroupComplex
        (H := OSHilbertSpace OS)
        (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (B := osSpatialTranslateHilbert (d := d) OS a)
        hcommA
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_nonneg (d := d) OS lgc 1 one_pos)
        (spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
        (t : ℂ) (by simpa using ht))
  change
    (osSpatialTranslateHilbert (d := d) OS a).comp
      (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) =
    (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)).comp
      (osSpatialTranslateHilbert (d := d) OS a)
  exact hcommComplex.eq

/-- Real positive-time matrix elements of the complex OS semigroup factor through
two shorter time steps, even after spatial translation of the input vectors. -/
theorem inner_osSpatialTranslateHilbert_osTimeShiftHilbertComplex_add
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (a b : Fin d → ℝ) (x : OSHilbertSpace OS) :
    @inner ℂ (OSHilbertSpace OS) _
      ((osSpatialTranslateHilbert (d := d) OS a) x)
      ((osTimeShiftHilbertComplex (d := d) OS lgc ((s + t : ℝ) : ℂ))
        ((osSpatialTranslateHilbert (d := d) OS b) x)) =
    @inner ℂ (OSHilbertSpace OS) _
      ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
        ((osSpatialTranslateHilbert (d := d) OS a) x))
      ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
        ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
  rw [osTimeShiftHilbertComplex_comp (d := d) OS lgc s t hs ht]
  rw [ContinuousLinearMap.comp_apply]
  have hsa := osTimeShiftHilbertComplex_isSelfAdjoint (d := d) OS lgc s hs
  have hsa' :
      ContinuousLinearMap.adjoint
        (osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) =
      osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ) := by
    simpa [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using hsa
  calc
    @inner ℂ (OSHilbertSpace OS) _
        ((osSpatialTranslateHilbert (d := d) OS a) x)
        ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS b) x)))
      =
        @inner ℂ (OSHilbertSpace OS) _
          ((osSpatialTranslateHilbert (d := d) OS a) x)
          ((ContinuousLinearMap.adjoint
              (osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)))
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS b) x))) := by
            rw [hsa']
    _ =
        @inner ℂ (OSHilbertSpace OS) _
          ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS a) x))
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
            exact ContinuousLinearMap.adjoint_inner_right
              (osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) x)
              ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS b) x))

/-- The off-diagonal spectral Laplace matrix element for spatially translated
vectors factors across positive real times. -/
theorem selfAdjointSpectralLaplaceOffdiag_spatialTranslate_add
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) (a b : Fin d → ℝ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        ((osSpatialTranslateHilbert (d := d) OS a) x)
        ((osSpatialTranslateHilbert (d := d) OS b) x)
        (((s + t : ℝ) : ℂ)) =
      @inner ℂ (OSHilbertSpace OS) _
        ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS a) x))
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
  rw [← osTimeShiftHilbertComplex_inner_eq
    (d := d) OS lgc
    ((osSpatialTranslateHilbert (d := d) OS a) x)
    ((osSpatialTranslateHilbert (d := d) OS b) x)
    (((s + t : ℝ) : ℂ))
    (by exact add_pos hs ht)]
  exact inner_osSpatialTranslateHilbert_osTimeShiftHilbertComplex_add
    (d := d) OS lgc s t hs ht a b x

/-- The scalar semigroup-group matrix kernel attached to the OS Hilbert vector
`x`: Euclidean time in the semigroup direction and spatial translation in the
group direction. -/
def osSemigroupGroupMatrixElement
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    ℝ → (Fin d → ℝ) → ℂ :=
  fun t a =>
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
      (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      x
      ((osSpatialTranslateHilbert (d := d) OS a) x)
      (t : ℂ)

/-- On positive real times, the semigroup-group kernel depends on the spatial
variables only through the difference `b - a`, exactly as expected from the
unitary spatial translation representation. -/
theorem osSemigroupGroupMatrixElement_eq_translated_pair
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (a b : Fin d → ℝ) (t : ℝ) (ht : 0 < t) :
    osSemigroupGroupMatrixElement (d := d) OS lgc x t (b - a) =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        ((osSpatialTranslateHilbert (d := d) OS a) x)
        ((osSpatialTranslateHilbert (d := d) OS b) x)
        (t : ℂ) := by
  rw [osSemigroupGroupMatrixElement]
  rw [← osTimeShiftHilbertComplex_inner_eq
    (d := d) OS lgc x
    ((osSpatialTranslateHilbert (d := d) OS (b - a)) x)
    (t : ℂ) ht]
  rw [← osTimeShiftHilbertComplex_inner_eq
    (d := d) OS lgc
    ((osSpatialTranslateHilbert (d := d) OS a) x)
    ((osSpatialTranslateHilbert (d := d) OS b) x)
    (t : ℂ) ht]
  have hcomm :
      (osSpatialTranslateHilbert (d := d) OS (-a))
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS b) x)) =
        (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS (b - a)) x) := by
    calc
      (osSpatialTranslateHilbert (d := d) OS (-a))
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS b) x))
        =
          (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (-a))
              ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
              exact congrArg (fun f => f ((osSpatialTranslateHilbert (d := d) OS b) x))
                (osSpatialTranslateHilbert_commutes_osTimeShiftHilbertComplex_ofReal
                  (d := d) OS lgc (-a) t ht)
      _ =
          (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            (((osSpatialTranslateHilbert (d := d) OS (-a)).comp
              (osSpatialTranslateHilbert (d := d) OS b)) x) := by
              rfl
      _ =
          (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS ((-a) + b)) x) := by
              rw [osSpatialTranslateHilbert_comp (d := d) OS (-a) b]
      _ =
          (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (b - a)) x) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    @inner ℂ (OSHilbertSpace OS) _
        x
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS (b - a)) x))
      =
        @inner ℂ (OSHilbertSpace OS) _
          x
          ((osSpatialTranslateHilbert (d := d) OS (-a))
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS b) x))) := by
            rw [hcomm.symm]
    _ =
        @inner ℂ (OSHilbertSpace OS) _
          ((osSpatialTranslateHilbert (d := d) OS a) x)
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
            rw [← osSpatialTranslateHilbert_adjoint (d := d) OS a]
            exact ContinuousLinearMap.adjoint_inner_right
              (osSpatialTranslateHilbert (d := d) OS a)
              x
              ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS b) x))

/-- Mixed semigroup-group matrix element with the time evolution moved to the left
translated vector. -/
theorem osSemigroupGroupMatrixElement_eq_inner_timeShift_left
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (a b : Fin d → ℝ) (t : ℝ) (ht : 0 < t) :
    osSemigroupGroupMatrixElement (d := d) OS lgc x t (b - a) =
      @inner ℂ (OSHilbertSpace OS) _
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS a) x))
        ((osSpatialTranslateHilbert (d := d) OS b) x) := by
  rw [osSemigroupGroupMatrixElement_eq_translated_pair
    (d := d) OS lgc x a b t ht]
  rw [← osTimeShiftHilbertComplex_inner_eq (d := d) OS lgc
    ((osSpatialTranslateHilbert (d := d) OS a) x)
    ((osSpatialTranslateHilbert (d := d) OS b) x)
    (t : ℂ) ht]
  have hsa := osTimeShiftHilbertComplex_isSelfAdjoint (d := d) OS lgc t ht
  have hsa' :
      ContinuousLinearMap.adjoint
        (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) =
      osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ) := by
    simpa [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using hsa
  simpa [hsa'] using
    (ContinuousLinearMap.adjoint_inner_right
      (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
      ((osSpatialTranslateHilbert (d := d) OS a) x)
      ((osSpatialTranslateHilbert (d := d) OS b) x))

/-- Mixed semigroup-group matrix element with the time evolution moved to the right
translated vector. -/
theorem osSemigroupGroupMatrixElement_eq_inner_timeShift_right
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (a b : Fin d → ℝ) (t : ℝ) (ht : 0 < t) :
    osSemigroupGroupMatrixElement (d := d) OS lgc x t (b - a) =
      @inner ℂ (OSHilbertSpace OS) _
        ((osSpatialTranslateHilbert (d := d) OS a) x)
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
  rw [osSemigroupGroupMatrixElement_eq_translated_pair
    (d := d) OS lgc x a b t ht]
  rw [← osTimeShiftHilbertComplex_inner_eq (d := d) OS lgc
    ((osSpatialTranslateHilbert (d := d) OS a) x)
    ((osSpatialTranslateHilbert (d := d) OS b) x)
    (t : ℂ) ht]

/-- Positive-time semigroup-group matrix element split across two time evolutions. -/
theorem osSemigroupGroupMatrixElement_eq_inner_timeShift_add
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (a b : Fin d → ℝ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    osSemigroupGroupMatrixElement (d := d) OS lgc x (s + t) (b - a) =
      @inner ℂ (OSHilbertSpace OS) _
        ((osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS a) x))
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS b) x)) := by
  rw [osSemigroupGroupMatrixElement_eq_translated_pair
    (d := d) OS lgc x a b (s + t) (add_pos hs ht)]
  exact selfAdjointSpectralLaplaceOffdiag_spatialTranslate_add
    (d := d) OS lgc x a b s t hs ht

/-- The spatially translated real-time matrix kernel of the OS semigroup is
positive semidefinite. This is the first operator-theoretic positivity input on
the OS/Stone route toward a semigroup-group Bochner theorem. -/
theorem spatialTranslate_timeShift_matrix_posSemidef
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (τ : ι → Set.Ioi (0 : ℝ)) (a : ι → Fin d → ℝ) :
    let q := ∑ i : ι, ∑ j : ι,
      starRingEnd ℂ (c i) * c j *
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          ((osSpatialTranslateHilbert (d := d) OS (a i)) x)
          ((osSpatialTranslateHilbert (d := d) OS (a j)) x)
          (((((τ i : ℝ) + (τ j : ℝ)) : ℝ) : ℂ))
    q.im = 0 ∧ 0 ≤ q.re := by
  classical
  let v : ι → OSHilbertSpace OS := fun i =>
    c i • (osTimeShiftHilbertComplex (d := d) OS lgc ((τ i : ℝ) : ℂ))
      ((osSpatialTranslateHilbert (d := d) OS (a i)) x)
  have hq :
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            ((osSpatialTranslateHilbert (d := d) OS (a i)) x)
            ((osSpatialTranslateHilbert (d := d) OS (a j)) x)
            (((((τ i : ℝ) + (τ j : ℝ)) : ℝ) : ℂ)))
        = ↑‖∑ i : ι, v i‖ ^ 2 := by
    calc
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            ((osSpatialTranslateHilbert (d := d) OS (a i)) x)
            ((osSpatialTranslateHilbert (d := d) OS (a j)) x)
            (((((τ i : ℝ) + (τ j : ℝ)) : ℝ) : ℂ)))
          =
        ∑ i : ι, ∑ j : ι,
          starRingEnd ℂ (c i) * c j *
            @inner ℂ (OSHilbertSpace OS) _
              ((osTimeShiftHilbertComplex (d := d) OS lgc ((τ i : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (a i)) x))
              ((osTimeShiftHilbertComplex (d := d) OS lgc ((τ j : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (a j)) x)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [selfAdjointSpectralLaplaceOffdiag_spatialTranslate_add
              (d := d) (OS := OS) (lgc := lgc) (x := x) (a := a i) (b := a j)
              (s := (τ i : ℝ)) (t := (τ j : ℝ)) (τ i).2 (τ j).2]
      _ = @inner ℂ (OSHilbertSpace OS) _ (∑ i : ι, v i) (∑ i : ι, v i) := by
            calc
              ∑ i : ι, ∑ j : ι,
                  starRingEnd ℂ (c i) * c j *
                    @inner ℂ (OSHilbertSpace OS) _
                      ((osTimeShiftHilbertComplex (d := d) OS lgc ((τ i : ℝ) : ℂ))
                        ((osSpatialTranslateHilbert (d := d) OS (a i)) x))
                      ((osTimeShiftHilbertComplex (d := d) OS lgc ((τ j : ℝ) : ℂ))
                        ((osSpatialTranslateHilbert (d := d) OS (a j)) x))
                = ∑ i : ι, ∑ j : ι,
                    @inner ℂ (OSHilbertSpace OS) _ (v i) (v j) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      simp [v, inner_smul_left, inner_smul_right]
                      ring
              _ = @inner ℂ (OSHilbertSpace OS) _ (∑ i : ι, v i) (∑ i : ι, v i) := by
                    symm
                    rw [inner_sum]
                    simp_rw [sum_inner]
                    simpa using
                      (Finset.sum_comm
                        (f := fun x i : ι =>
                          @inner ℂ (OSHilbertSpace OS) _ (v i) (v x)))
      _ = ↑‖∑ i : ι, v i‖ ^ 2 := by
            rw [inner_self_eq_norm_sq_to_K]
            rfl
  constructor
  · rw [hq]
    simpa [pow_two]
  · rw [hq]
    simpa [pow_two] using sq_nonneg ‖∑ i : ι, v i‖

/-- Strict positive-time positive-definiteness of the scalar semigroup-group
matrix kernel attached to a single OS Hilbert vector. This is the direct
positive-time precursor to the full `IsSemigroupGroupPD` hypothesis needed by
`semigroupGroup_bochner`. -/
theorem osSemigroupGroupMatrixElement_posSemidef_Ioi
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (τ : ι → Set.Ioi (0 : ℝ)) (a : ι → Fin d → ℝ) :
    let q := ∑ i : ι, ∑ j : ι,
      starRingEnd ℂ (c i) * c j *
        osSemigroupGroupMatrixElement (d := d) OS lgc x
          ((τ i : ℝ) + (τ j : ℝ)) (a j - a i)
    q.im = 0 ∧ 0 ≤ q.re := by
  classical
  have hq :
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          osSemigroupGroupMatrixElement (d := d) OS lgc x
            ((τ i : ℝ) + (τ j : ℝ)) (a j - a i))
        =
      ∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            ((osSpatialTranslateHilbert (d := d) OS (a i)) x)
            ((osSpatialTranslateHilbert (d := d) OS (a j)) x)
            (((((τ i : ℝ) + (τ j : ℝ)) : ℝ) : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [osSemigroupGroupMatrixElement_eq_translated_pair
      (d := d) OS lgc x (a i) (a j) ((τ i : ℝ) + (τ j : ℝ))
      (add_pos (τ i).2 (τ j).2)]
  rw [hq]
  exact spatialTranslate_timeShift_matrix_posSemidef
    (d := d) OS lgc x c τ a

/-- Bochner measure for the OS semigroup-group matrix kernel, once continuity,
boundedness, and full semigroup-group positive-definiteness have been
established. This is the exact point where the abstract semigroup-group Bochner
theorem enters the OS/Stone route. -/
theorem exists_measure_osSemigroupGroupMatrixElement
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (hcont : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      osSemigroupGroupMatrixElement (d := d) OS lgc x p.1 p.2))
    (hbdd : ∃ C : ℝ, ∀ t a,
      ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ ≤ C)
    (hpd : SCV.IsSemigroupGroupPD d
      (osSemigroupGroupMatrixElement (d := d) OS lgc x)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        osSemigroupGroupMatrixElement (d := d) OS lgc x t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
            ∂μ := by
  exact SCV.semigroupGroup_bochner d
    (osSemigroupGroupMatrixElement (d := d) OS lgc x)
    hcont hbdd hpd

/-- Continuity of the positive-time semigroup-group matrix kernel. -/
theorem continuousOn_osSemigroupGroupMatrixElement_Ioi
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS) :
    ContinuousOn (fun p : ℝ × (Fin d → ℝ) =>
      osSemigroupGroupMatrixElement (d := d) OS lgc x p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  intro p hp
  have hp1 : 0 < p.1 := hp.1
  let g : ℝ × (Fin d → ℝ) → ℂ × OSHilbertSpace OS := fun q =>
    ((q.1 : ℂ), (osSpatialTranslateHilbert (d := d) OS q.2 x))
  have hg : ContinuousAt g p := by
    refine ContinuousAt.prodMk ?_ ?_
    · exact (Complex.continuous_ofReal.comp continuous_fst).continuousAt
    · exact ((continuous_osSpatialTranslateHilbert (d := d) OS x).comp continuous_snd).continuousAt
  have hAt : ContinuousAt (fun q : ℝ × (Fin d → ℝ) =>
      osTimeShiftHilbertComplex (d := d) OS lgc (q.1 : ℂ)
        ((osSpatialTranslateHilbert (d := d) OS q.2 x))) p := by
    have hp' : g p ∈ ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
      constructor
      · simpa [g] using hp1
      · simp [g]
    have hp'_nhds : ({z : ℂ | 0 < z.re} ×ˢ Set.univ) ∈ nhds (g p) := by
      exact IsOpen.mem_nhds
        ((isOpen_lt continuous_const continuous_re).prod isOpen_univ)
        hp'
    have h0 :
        ContinuousAt (fun z : ℂ × OSHilbertSpace OS =>
          osTimeShiftHilbertComplex (d := d) OS lgc z.1 z.2) (g p) := by
      exact (continuousOn_osTimeShiftHilbertComplex_jointly
        (d := d) OS lgc).continuousAt hp'_nhds
    exact h0.comp hg
  have hInner :
      ContinuousAt (fun q : ℝ × (Fin d → ℝ) =>
        @inner ℂ (OSHilbertSpace OS) _ x
          (osTimeShiftHilbertComplex (d := d) OS lgc (q.1 : ℂ)
            ((osSpatialTranslateHilbert (d := d) OS q.2 x)))) p := by
    exact continuous_inner.continuousAt.comp (continuous_const.continuousAt.prodMk hAt)
  refine (hInner.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [prod_mem_nhds (Ioi_mem_nhds hp1) Filter.univ_mem] with q hq
  have hq' : 0 < q.1 := hq.1
  rw [osSemigroupGroupMatrixElement, ← osTimeShiftHilbertComplex_inner_eq
    (d := d) OS lgc x
    ((osSpatialTranslateHilbert (d := d) OS q.2 x))
    (q.1 : ℂ) hq']

/-- The semigroup-group matrix kernel extends continuously to `t = 0` on
compactly supported positive-time vectors by freezing the semigroup factor to
the identity at the boundary. -/
theorem continuous_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))) :
    Continuous (fun p : ℝ × (Fin d → ℝ) =>
      if hp : 0 < p.1 then
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) p.1 p.2
      else
        @inner ℂ (OSHilbertSpace OS) _
          (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
          ((osSpatialTranslateHilbert (d := d) OS p.2)
            (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))) := by
  let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
  let Fext : ℝ × (Fin d → ℝ) → ℂ := fun p =>
    if hp : 0 < p.1 then
      osSemigroupGroupMatrixElement (d := d) OS lgc x p.1 p.2
    else
      @inner ℂ (OSHilbertSpace OS) _ x ((osSpatialTranslateHilbert (d := d) OS p.2) x)
  refine continuous_iff_continuousAt.2 ?_
  intro p0
  rcases p0 with ⟨t0, a0⟩
  by_cases ht0 : 0 < t0
  · have hposWithin :
        ContinuousWithinAt (fun p : ℝ × (Fin d → ℝ) =>
          osSemigroupGroupMatrixElement (d := d) OS lgc x p.1 p.2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.univ) (t0, a0) :=
        (continuousOn_osSemigroupGroupMatrixElement_Ioi (d := d) OS lgc x)
          (t0, a0) ⟨ht0, by simp⟩
    have hposAt : ContinuousAt (fun p : ℝ × (Fin d → ℝ) =>
        osSemigroupGroupMatrixElement (d := d) OS lgc x p.1 p.2) (t0, a0) := by
      exact hposWithin.continuousAt
        (by simpa using prod_mem_nhds (Ioi_mem_nhds ht0) Filter.univ_mem)
    refine hposAt.congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds (Ioi_mem_nhds ht0) Filter.univ_mem] with q hq
    have hq1 : 0 < q.1 := hq.1
    show (if hp : 0 < q.1 then
        osSemigroupGroupMatrixElement (d := d) OS lgc x q.1 q.2
      else
        @inner ℂ (OSHilbertSpace OS) _ x
          ((osSpatialTranslateHilbert (d := d) OS q.2) x)) =
      osSemigroupGroupMatrixElement (d := d) OS lgc x q.1 q.2
    simp [Fext, hq1]
  · by_cases hneg0 : t0 < 0
    · have hnegCont : Continuous (fun p : ℝ × (Fin d → ℝ) =>
          @inner ℂ (OSHilbertSpace OS) _ x
            ((osSpatialTranslateHilbert (d := d) OS p.2) x)) := by
        exact continuous_const.inner
          ((continuous_osSpatialTranslateHilbert (d := d) OS x).comp continuous_snd)
      have hnegAt : ContinuousAt (fun p : ℝ × (Fin d → ℝ) =>
          @inner ℂ (OSHilbertSpace OS) _ x
            ((osSpatialTranslateHilbert (d := d) OS p.2) x)) (t0, a0) :=
        hnegCont.continuousAt
      refine hnegAt.congr_of_eventuallyEq ?_
      filter_upwards [prod_mem_nhds (Iio_mem_nhds hneg0) Filter.univ_mem] with q hq
      have hq1 : ¬ 0 < q.1 := by exact not_lt_of_gt hq.1
      simpa [x, Fext, hq1]
    · have ht0_eq : t0 = 0 := by
        exact le_antisymm (le_of_not_gt ht0) (le_of_not_gt hneg0)
      subst ht0_eq
      rw [Metric.continuousAt_iff]
      intro ε hε
      let x0 : OSHilbertSpace OS := x
      let M : ℝ := ‖x0‖ + 1
      have hM : 0 < M := by
        dsimp [M]
        positivity
      let η : ℝ := ε / (2 * M)
      have hη : 0 < η := by
        dsimp [η]
        positivity
      have hsp : ContinuousAt (fun a : Fin d → ℝ =>
          @inner ℂ (OSHilbertSpace OS) _ x0
            ((osSpatialTranslateHilbert (d := d) OS a) x0)) a0 := by
        have hcont : Continuous (fun a : Fin d → ℝ =>
            @inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a) x0)) := by
          exact continuous_const.inner
            (continuous_osSpatialTranslateHilbert (d := d) OS x0)
        simpa using (hcont.continuousAt : ContinuousAt _ a0)
      rcases (Metric.continuousAt_iff.mp hsp) (η * M) (by positivity) with
        ⟨δa, hδa, hδaprop⟩
      have htime :
          Filter.Tendsto
            (fun t : ℝ =>
              if ht : 0 < t then
                (osTimeShiftHilbert (d := d) OS lgc t ht) x0
              else x0)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds x0) := by
        simpa [x0] using
          tendsto_osTimeShiftHilbert_nhdsWithin_zero_of_isCompactSupport
            (d := d) OS lgc F hF_compact
      rcases (Metric.tendsto_nhdsWithin_nhds.mp htime) η hη with
        ⟨δt, hδt, hδtprop⟩
      refine ⟨min δa δt, by positivity, ?_⟩
      intro p hp
      rcases p with ⟨t, a⟩
      rw [Prod.dist_eq] at hp
      have hp' := max_lt_iff.mp hp
      have ha : dist a a0 < δa := by
        exact lt_of_lt_of_le hp'.2 (min_le_left _ _)
      have htd : dist t 0 < δt := by
        exact lt_of_lt_of_le hp'.1 (min_le_right _ _)
      have hF0 : Fext (0, a0) =
          @inner ℂ (OSHilbertSpace OS) _ x0
            ((osSpatialTranslateHilbert (d := d) OS a0) x0) := by
        simpa [x, Fext, x0]
      by_cases htp : 0 < t
      · have htimeNorm : ‖(osTimeShiftHilbert (d := d) OS lgc t htp) x0 - x0‖ < η := by
          have hδtprop' :
              dist (if ht : 0 < t then (osTimeShiftHilbert (d := d) OS lgc t ht) x0 else x0) x0 < η :=
            hδtprop (show t ∈ Set.Ioi 0 from htp) htd
          simpa [htp, dist_eq_norm] using hδtprop'
        have hU : osSpatialTranslateHilbert (d := d) OS a ∈
            unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
          constructor
          · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
          · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
        have hFpos : Fext (t, a) =
            @inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a)
                ((osTimeShiftHilbert (d := d) OS lgc t htp) x0)) := by
          simp [Fext, htp, x0]
          rw [osSemigroupGroupMatrixElement]
          rw [← osTimeShiftHilbertComplex_inner_eq
            (d := d) OS lgc x0
            ((osSpatialTranslateHilbert (d := d) OS a) x0)
            (t : ℂ) htp]
          have hcomm0 :
              (osSpatialTranslateHilbert (d := d) OS a)
                  ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) x0) =
                (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x0) := by
            exact congrArg (fun f => f x0)
              (osSpatialTranslateHilbert_commutes_osTimeShiftHilbertComplex_ofReal
                (d := d) OS lgc a t htp)
          calc
            @inner ℂ (OSHilbertSpace OS) _ x0
                ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x0))
                =
              @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a)
                  ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) x0)) := by
                    rw [← hcomm0]
            _ =
              @inner ℂ (OSHilbertSpace OS) _ x
                ((osSpatialTranslateHilbert (d := d) OS a)
                  ((osTimeShiftHilbert (d := d) OS lgc t htp) x)) := by
                    rw [osTimeShiftHilbertComplex_ofReal_eq_of_isCompactSupport
                      (d := d) OS lgc F hF_compact t htp]
        have hsplit :
            @inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a)
                ((osTimeShiftHilbert (d := d) OS lgc t htp) x0)) -
              @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a0) x0) =
            @inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a)
                (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0)) +
            (@inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a) x0) -
             @inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a0) x0)) := by
          calc
            @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a)
                  ((osTimeShiftHilbert (d := d) OS lgc t htp) x0)) -
              @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a0) x0)
                =
              (@inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a)
                  ((osTimeShiftHilbert (d := d) OS lgc t htp) x0)) -
               @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a) x0)) +
              (@inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a) x0) -
               @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a0) x0)) := by ring
            _ =
              @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a)
                  (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0)) +
              (@inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a) x0) -
               @inner ℂ (OSHilbertSpace OS) _ x0
                ((osSpatialTranslateHilbert (d := d) OS a0) x0)) := by
                  rw [← inner_sub_right, ← map_sub]
        calc
          dist (Fext (t, a)) (Fext (0, a0)) = ‖Fext (t, a) - Fext (0, a0)‖ := by
                simp [dist_eq_norm]
          _ =
              ‖@inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a)
                    ((osTimeShiftHilbert (d := d) OS lgc t htp) x0)) -
                @inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a0) x0)‖ := by
                  rw [hFpos, hF0]
          _ =
              ‖@inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a)
                    (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0)) +
                (@inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a) x0) -
                 @inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a0) x0))‖ := by
                  rw [hsplit]
          _ ≤
              ‖@inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a)
                    (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0))‖ +
              ‖(@inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a) x0) -
                 @inner ℂ (OSHilbertSpace OS) _ x0
                  ((osSpatialTranslateHilbert (d := d) OS a0) x0))‖ := by
                  exact norm_add_le _ _
          _ < η * M + η * M := by
                  refine add_lt_add ?_ ?_
                  · have hnormU :=
                      ContinuousLinearMap.norm_map_of_mem_unitary
                        (u := osSpatialTranslateHilbert (d := d) OS a) hU
                        (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0)
                    calc
                      ‖@inner ℂ (OSHilbertSpace OS) _ x0
                          ((osSpatialTranslateHilbert (d := d) OS a)
                            (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0))‖
                          ≤ ‖x0‖ *
                              ‖(osSpatialTranslateHilbert (d := d) OS a)
                                  (((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0)‖ := by
                                  exact norm_inner_le_norm _ _
                      _ = ‖x0‖ *
                            ‖((osTimeShiftHilbert (d := d) OS lgc t htp) x0) - x0‖ := by
                            rw [hnormU]
                      _ ≤ ‖x0‖ * η := by
                            exact mul_le_mul_of_nonneg_left (le_of_lt htimeNorm) (norm_nonneg _)
                      _ < M * η := by
                            have hx_lt : ‖x0‖ < M := by
                              dsimp [M]
                              linarith
                            exact mul_lt_mul_of_pos_right hx_lt hη
                      _ = η * M := by ring
                  · simpa [dist_eq_norm] using hδaprop ha
          _ = ε := by
                  dsimp [η, M]
                  field_simp
                  ring
      · have hnegEq : Fext (t, a) =
            @inner ℂ (OSHilbertSpace OS) _ x0
              ((osSpatialTranslateHilbert (d := d) OS a) x0) := by
          simpa [x, x0, Fext, htp]
        calc
          dist (Fext (t, a)) (Fext (0, a0)) =
              dist (@inner ℂ (OSHilbertSpace OS) _ x0
                      ((osSpatialTranslateHilbert (d := d) OS a) x0))
                    (@inner ℂ (OSHilbertSpace OS) _ x0
                      ((osSpatialTranslateHilbert (d := d) OS a0) x0)) := by
                        rw [hnegEq, hF0]
          _ < η * M := hδaprop ha
          _ < ε := by
                have hEqHalf : η * M = ε / 2 := by
                  dsimp [η]
                  have hMne : M ≠ 0 := by linarith [hM]
                  field_simp [hMne]
                rw [hEqHalf]
                linarith

/- Full semigroup-group positive-definiteness of the compact-support extension
of the OS matrix kernel. -/
section semigroupGroupPDExtension

set_option maxHeartbeats 1600000 in
theorem isSemigroupGroupPD_osSemigroupGroupMatrixElement_extension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    SCV.IsSemigroupGroupPD d
      (fun t a =>
        if ht : 0 < t then
          osSemigroupGroupMatrixElement (d := d) OS lgc
            (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) t a
        else
          @inner ℂ (OSHilbertSpace OS) _
            (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
            ((osSpatialTranslateHilbert (d := d) OS a)
              (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)))) := by
  classical
  let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
  intro n c ts as hts
  let q : ℂ := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j *
        (if ht : 0 < ts i + ts j then
          osSemigroupGroupMatrixElement (d := d) OS lgc x (ts i + ts j) (as j - as i)
        else
          @inner ℂ (OSHilbertSpace OS) _ x
            ((osSpatialTranslateHilbert (d := d) OS (as j - as i)) x))
  change q.im = 0 ∧ 0 ≤ q.re
  let v : Fin n → OSHilbertSpace OS := fun i =>
    if hti : 0 < ts i then
      c i • (osTimeShiftHilbertComplex (d := d) OS lgc ((ts i : ℝ) : ℂ))
        ((osSpatialTranslateHilbert (d := d) OS (as i)) x)
    else
      c i • ((osSpatialTranslateHilbert (d := d) OS (as i)) x)
  have hpair : ∀ i j : Fin n,
      (if ht : 0 < ts i + ts j then
        osSemigroupGroupMatrixElement (d := d) OS lgc x (ts i + ts j) (as j - as i)
      else
        @inner ℂ (OSHilbertSpace OS) _ x
          ((osSpatialTranslateHilbert (d := d) OS (as j - as i)) x)) =
      @inner ℂ (OSHilbertSpace OS) _
        (if hti : 0 < ts i then
          (osTimeShiftHilbertComplex (d := d) OS lgc ((ts i : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (as i)) x)
        else
          ((osSpatialTranslateHilbert (d := d) OS (as i)) x))
        (if htj : 0 < ts j then
          (osTimeShiftHilbertComplex (d := d) OS lgc ((ts j : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (as j)) x)
        else
          ((osSpatialTranslateHilbert (d := d) OS (as j)) x)) := by
    intro i j
    by_cases hi : 0 < ts i
    · by_cases hj : 0 < ts j
      · have hij : 0 < ts i + ts j := add_pos hi hj
        simpa [hi, hj, hij] using
          osSemigroupGroupMatrixElement_eq_inner_timeShift_add
            (d := d) OS lgc x (as i) (as j) (ts i) (ts j) hi hj
      · have htsj0 : ts j = 0 := by
          exact le_antisymm (le_of_not_gt hj) (hts j)
        have hij : 0 < ts i + ts j := by
          simpa [htsj0] using hi
        simp [hi, hj, hij, htsj0]
        simpa [htsj0, add_zero] using
          osSemigroupGroupMatrixElement_eq_inner_timeShift_left
            (d := d) OS lgc x (as i) (as j) (ts i) hi
    · have htsi0 : ts i = 0 := by
        exact le_antisymm (le_of_not_gt hi) (hts i)
      by_cases hj : 0 < ts j
      · have hij : 0 < ts i + ts j := by
          simpa [htsi0] using hj
        simp [hi, hj, hij, htsi0]
        simpa [htsi0, zero_add] using
          osSemigroupGroupMatrixElement_eq_inner_timeShift_right
            (d := d) OS lgc x (as i) (as j) (ts j) hj
      · have htsj0 : ts j = 0 := by
          exact le_antisymm (le_of_not_gt hj) (hts j)
        simp [hi, hj, htsi0, htsj0]
        have htrans :
          @inner ℂ (OSHilbertSpace OS) _ x
              ((osSpatialTranslateHilbert (d := d) OS (as j - as i)) x) =
            @inner ℂ (OSHilbertSpace OS) _
              ((osSpatialTranslateHilbert (d := d) OS (as i)) x)
              ((osSpatialTranslateHilbert (d := d) OS (as j)) x) := by
                calc
                  @inner ℂ (OSHilbertSpace OS) _ x
                      ((osSpatialTranslateHilbert (d := d) OS (as j - as i)) x) =
                    @inner ℂ (OSHilbertSpace OS) _ x
                      (((osSpatialTranslateHilbert (d := d) OS (-as i)).comp
                        (osSpatialTranslateHilbert (d := d) OS (as j))) x) := by
                          congr 1
                          rw [osSpatialTranslateHilbert_comp (d := d) OS (-as i) (as j)]
                          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
                  _ =
                    @inner ℂ (OSHilbertSpace OS) _ x
                      ((osSpatialTranslateHilbert (d := d) OS (-as i))
                        ((osSpatialTranslateHilbert (d := d) OS (as j)) x)) := by
                          rfl
                  _ =
                    @inner ℂ (OSHilbertSpace OS) _
                      ((osSpatialTranslateHilbert (d := d) OS (as i)) x)
                      ((osSpatialTranslateHilbert (d := d) OS (as j)) x) := by
                        rw [← osSpatialTranslateHilbert_adjoint (d := d) OS (as i)]
                        exact ContinuousLinearMap.adjoint_inner_right
                          (osSpatialTranslateHilbert (d := d) OS (as i))
                          x
                          ((osSpatialTranslateHilbert (d := d) OS (as j)) x)
        exact htrans
  have hq : q = ↑‖∑ i : Fin n, v i‖ ^ 2 := by
    dsimp [q]
    calc
      ∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (c i) * c j *
            (if ht : 0 < ts i + ts j then
              osSemigroupGroupMatrixElement (d := d) OS lgc x (ts i + ts j) (as j - as i)
            else
              @inner ℂ (OSHilbertSpace OS) _ x
                ((osSpatialTranslateHilbert (d := d) OS (as j - as i)) x))
          =
        ∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (c i) * c j * @inner ℂ (OSHilbertSpace OS) _
            (if hti : 0 < ts i then
              (osTimeShiftHilbertComplex (d := d) OS lgc ((ts i : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (as i)) x)
            else
              ((osSpatialTranslateHilbert (d := d) OS (as i)) x))
            (if htj : 0 < ts j then
              (osTimeShiftHilbertComplex (d := d) OS lgc ((ts j : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (as j)) x)
            else
              ((osSpatialTranslateHilbert (d := d) OS (as j)) x)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                refine Finset.sum_congr rfl ?_
                intro j hj
                exact congrArg
                  (fun z => starRingEnd ℂ (c i) * c j * z)
                  (hpair i j)
      _ = ∑ i : Fin n, ∑ j : Fin n, @inner ℂ (OSHilbertSpace OS) _ (v i) (v j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hti : 0 < ts i
            · by_cases htj : 0 < ts j
              · simp [v, hti, htj, inner_smul_left, inner_smul_right,
                  mul_assoc, mul_left_comm, mul_comm]
              · simp [v, hti, htj, inner_smul_left, inner_smul_right,
                  mul_assoc, mul_left_comm, mul_comm]
            · by_cases htj : 0 < ts j
              · simp [v, hti, htj, inner_smul_left, inner_smul_right,
                  mul_assoc, mul_left_comm, mul_comm]
              · simp [v, hti, htj, inner_smul_left, inner_smul_right,
                  mul_assoc, mul_left_comm, mul_comm]
      _ = @inner ℂ (OSHilbertSpace OS) _ (∑ i : Fin n, v i) (∑ i : Fin n, v i) := by
            symm
            rw [inner_sum]
            simp_rw [sum_inner]
            exact
              (Finset.sum_comm
                (f := fun x i : Fin n => @inner ℂ (OSHilbertSpace OS) _ (v i) (v x)))
      _ = ↑‖∑ i : Fin n, v i‖ ^ 2 := by
            rw [inner_self_eq_norm_sq_to_K]
            rfl
  constructor
  · rw [hq]
    simp [pow_two]
  · rw [hq]
    exact_mod_cast sq_nonneg ‖∑ i : Fin n, v i‖

end semigroupGroupPDExtension

/-- Bochner measure for the compact-support extension of the OS semigroup-group
matrix kernel attached to a positive-time Borchers vector.

This packages the exact input produced by the OS/Stone route before one fixes a
particular probe: continuity at `t = 0`, semigroup-group positive-definiteness,
and a uniform matrix-element bound are all discharged once for a compact-support
positive-time vector. Later arguments can then specialize this theorem to the
four diagonal polarization vectors needed by VI.1. -/
theorem exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))) :
    let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        (if ht : 0 < t then
          osSemigroupGroupMatrixElement (d := d) OS lgc x t a
        else
          @inner ℂ (OSHilbertSpace OS) _ x
            ((osSpatialTranslateHilbert (d := d) OS a) x)) =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
            ∂μ := by
  let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
  let Fext : ℝ → (Fin d → ℝ) → ℂ := fun t a =>
    if ht : 0 < t then
      osSemigroupGroupMatrixElement (d := d) OS lgc x t a
    else
      @inner ℂ (OSHilbertSpace OS) _ x
        ((osSpatialTranslateHilbert (d := d) OS a) x)
  have hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => Fext p.1 p.2) := by
    simpa [Fext, x] using
      continuous_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
        (d := d) OS lgc F hF_compact
  have hbdd : ∃ C : ℝ, ∀ t a, ‖Fext t a‖ ≤ C := by
    refine ⟨2 * ‖x‖ ^ 2, ?_⟩
    intro t a
    have hU :
        osSpatialTranslateHilbert (d := d) OS a ∈
          unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
      constructor
      · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
      · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
    have hU_norm :
        ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ := by
      simpa using
        (ContinuousLinearMap.norm_map_of_mem_unitary
          (u := osSpatialTranslateHilbert (d := d) OS a) hU x)
    by_cases ht : 0 < t
    · calc
        ‖Fext t a‖
            = ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ := by
                simp [Fext, ht]
        _ = ‖@inner ℂ (OSHilbertSpace OS) _ x
              ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS a) x))‖ := by
              have hinner :
                  osSemigroupGroupMatrixElement (d := d) OS lgc x t a =
                    @inner ℂ (OSHilbertSpace OS) _ x
                      ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                        ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
                simpa [osSpatialTranslateHilbert_zero (d := d) OS] using
                  (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                    (d := d) OS lgc x (0 : Fin d → ℝ) a t ht)
              rw [hinner]
        _ ≤ ‖x‖ *
              ‖(osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
              exact norm_inner_le_norm _ _
        _ ≤ ‖x‖ *
              (‖osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)‖ *
                ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm
                (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS a) x)
        _ ≤ ‖x‖ * (2 * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
              gcongr
              exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc (t : ℂ) (by simpa using ht)
        _ = ‖x‖ * (2 * ‖x‖) := by rw [hU_norm]
        _ = 2 * ‖x‖ ^ 2 := by ring
    · calc
        ‖Fext t a‖
            = ‖@inner ℂ (OSHilbertSpace OS) _ x
                ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
                  simp [Fext, ht]
        _ ≤ ‖x‖ * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ := by
              exact norm_inner_le_norm _ _
        _ = ‖x‖ * ‖x‖ := by rw [hU_norm]
        _ ≤ 2 * ‖x‖ ^ 2 := by
              nlinarith [sq_nonneg ‖x‖]
  have hpd : SCV.IsSemigroupGroupPD d Fext := by
    simpa [Fext, x] using
      isSemigroupGroupPD_osSemigroupGroupMatrixElement_extension
        (d := d) OS lgc F
  simpa [Fext, x] using
    (SCV.semigroupGroup_bochner d Fext hcont hbdd hpd)

/-- Polarized semigroup-group Bochner package for two compact-support
positive-time vectors.

This packages the four diagonal measures attached to `F + G`, `F - G`,
`F + iG`, and `F - iG`. It is the reusable off-diagonal bridge needed when a
later argument wants one fixed pair of compact-support OS vectors rather than a
single diagonal probe. -/
theorem exists_polarized_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)))
    (hG_compact : ∀ n,
      HasCompactSupport ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))) :
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
    ∃ (ν₁ : Measure (ℝ × (Fin d → ℝ))) (_hν₁fin : IsFiniteMeasure ν₁)
      (ν₂ : Measure (ℝ × (Fin d → ℝ))) (_hν₂fin : IsFiniteMeasure ν₂)
      (ν₃ : Measure (ℝ × (Fin d → ℝ))) (_hν₃fin : IsFiniteMeasure ν₃)
      (ν₄ : Measure (ℝ × (Fin d → ℝ))) (_hν₄fin : IsFiniteMeasure ν₄)
      (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        (if ht : 0 < t then
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) xG))
        else
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert (d := d) OS a) xG)) =
          (1 / 4 : ℂ) *
            ((∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
  let xF_pre : OSPreHilbertSpace OS := (show OSPreHilbertSpace OS from (⟦F⟧))
  let xG_pre : OSPreHilbertSpace OS := (show OSPreHilbertSpace OS from (⟦G⟧))
  let xF : OSHilbertSpace OS := ((xF_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)
  let xG : OSHilbertSpace OS := ((xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)
  let Fpp : PositiveTimeBorchersSequence d := F + G
  let Fmm : PositiveTimeBorchersSequence d := F - G
  let Fpi : PositiveTimeBorchersSequence d := F + Complex.I • G
  let Fmi : PositiveTimeBorchersSequence d := F - Complex.I • G
  have hFpp_compact :
      ∀ n,
        HasCompactSupport ((((Fpp : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    simpa [Fpp, PositiveTimeBorchersSequence.add_toBorchersSequence, BorchersSequence.add_funcs]
      using (hF_compact n).add (hG_compact n)
  have hFmm_compact :
      ∀ n,
        HasCompactSupport ((((Fmm : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    simpa [Fmm, PositiveTimeBorchersSequence.sub_toBorchersSequence, BorchersSequence.sub_funcs,
      sub_eq_add_neg] using (hF_compact n).add (hG_compact n).neg
  have hFpi_compact :
      ∀ n,
        HasCompactSupport ((((Fpi : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    simpa [Fpi, PositiveTimeBorchersSequence.add_toBorchersSequence,
      PositiveTimeBorchersSequence.smul_toBorchersSequence, BorchersSequence.add_funcs,
      BorchersSequence.smul_funcs] using
      (hF_compact n).add
        (HasCompactSupport.smul_left
          (f := fun _ : NPointDomain d n => (Complex.I : ℂ)) (hG_compact n))
  have hFmi_compact :
      ∀ n,
        HasCompactSupport ((((Fmi : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    simpa [Fmi, PositiveTimeBorchersSequence.sub_toBorchersSequence,
      PositiveTimeBorchersSequence.smul_toBorchersSequence, BorchersSequence.sub_funcs,
      BorchersSequence.smul_funcs, sub_eq_add_neg] using
      (hF_compact n).add
        ((HasCompactSupport.smul_left
          (f := fun _ : NPointDomain d n => (Complex.I : ℂ)) (hG_compact n)).neg)
  obtain ⟨ν₁, hν₁fin, hsupp₁, hrepr₁⟩ :=
    exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
      (d := d) OS lgc Fpp hFpp_compact
  obtain ⟨ν₂, hν₂fin, hsupp₂, hrepr₂⟩ :=
    exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
      (d := d) OS lgc Fmm hFmm_compact
  obtain ⟨ν₃, hν₃fin, hsupp₃, hrepr₃⟩ :=
    exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
      (d := d) OS lgc Fpi hFpi_compact
  obtain ⟨ν₄, hν₄fin, hsupp₄, hrepr₄⟩ :=
    exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
      (d := d) OS lgc Fmi hFmi_compact
  refine ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, ?_⟩
  let xpp : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦Fpp⟧)) : OSHilbertSpace OS))
  let xmm : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦Fmm⟧)) : OSHilbertSpace OS))
  let xpi : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦Fpi⟧)) : OSHilbertSpace OS))
  let xmi : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦Fmi⟧)) : OSHilbertSpace OS))
  have hxpp : xpp = xF + xG := by
    have hcoe :
        (((xF_pre + xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) = xF + xG := by
      simpa [xF, xG, xF_pre, xG_pre] using
        (UniformSpace.Completion.coe_add xF_pre xG_pre)
    simpa [xpp, xF_pre, xG_pre, Fpp,
      PositiveTimeBorchersSequence.add_toBorchersSequence] using hcoe
  have hxmm : xmm = xF - xG := by
    have hcoe :
        (((xF_pre - xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) = xF - xG := by
      simpa [xF, xG, xF_pre, xG_pre] using
        (UniformSpace.Completion.coe_sub xF_pre xG_pre)
    simpa [xmm, xF_pre, xG_pre, Fmm,
      PositiveTimeBorchersSequence.sub_toBorchersSequence] using hcoe
  have hxpi : xpi = xF + Complex.I • xG := by
    have hsmul :
        ((((Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS))) =
          Complex.I • xG := by
      simpa [xG, xG_pre] using (UniformSpace.Completion.coe_smul Complex.I xG_pre)
    have hcoe :
        (((xF_pre + Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) =
          xF + Complex.I • xG := by
      calc
        (((xF_pre + Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS))
            = xF + (((Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) := by
                simpa [xF, xF_pre] using
                  (UniformSpace.Completion.coe_add xF_pre (Complex.I • xG_pre))
        _ = xF + Complex.I • xG := by rw [hsmul]
    simpa [xpi, xF_pre, xG_pre, Fpi,
      PositiveTimeBorchersSequence.add_toBorchersSequence,
      PositiveTimeBorchersSequence.smul_toBorchersSequence] using hcoe
  have hxmi : xmi = xF - Complex.I • xG := by
    have hsmul :
        ((((Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS))) =
          Complex.I • xG := by
      simpa [xG, xG_pre] using (UniformSpace.Completion.coe_smul Complex.I xG_pre)
    have hcoe :
        (((xF_pre - Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) =
          xF - Complex.I • xG := by
      calc
        (((xF_pre - Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS))
            = xF - (((Complex.I • xG_pre : OSPreHilbertSpace OS) : OSHilbertSpace OS)) := by
                simpa [xF, xF_pre] using
                  (UniformSpace.Completion.coe_sub xF_pre (Complex.I • xG_pre))
        _ = xF - Complex.I • xG := by rw [hsmul]
    simpa [xmi, xF_pre, xG_pre, Fmi,
      PositiveTimeBorchersSequence.sub_toBorchersSequence,
      PositiveTimeBorchersSequence.smul_toBorchersSequence] using hcoe
  let Aext : ℝ → (Fin d → ℝ) → OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
    fun t a =>
      if ht : 0 < t then
        (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)).comp
          (osSpatialTranslateHilbert (d := d) OS a)
      else
        osSpatialTranslateHilbert (d := d) OS a
  have hdiag_of_repr :
      ∀ {x : OSHilbertSpace OS} {μ : Measure (ℝ × (Fin d → ℝ))},
        (∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
          (if ht : 0 < t then
            osSemigroupGroupMatrixElement (d := d) OS lgc x t a
          else
            @inner ℂ (OSHilbertSpace OS) _ x
              ((osSpatialTranslateHilbert (d := d) OS a) x)) =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) →
        ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
          @inner ℂ (OSHilbertSpace OS) _ x ((Aext t a) x) =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
    intro x μ hrepr t a ht_nonneg
    specialize hrepr t a ht_nonneg
    by_cases ht : 0 < t
    · calc
        @inner ℂ (OSHilbertSpace OS) _ x ((Aext t a) x)
            = @inner ℂ (OSHilbertSpace OS) _ x
                ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
                    simp [Aext, ht]
        _ = osSemigroupGroupMatrixElement (d := d) OS lgc x t a := by
              symm
              simpa [osSpatialTranslateHilbert_zero (d := d) OS] using
                (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                  (d := d) OS lgc x (0 : Fin d → ℝ) a t ht)
        _ = ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
              simpa [ht] using hrepr
    · simpa [Aext, ht] using hrepr
  intro t a ht_nonneg
  have hdiag₁ := hdiag_of_repr (x := xpp) (μ := ν₁) hrepr₁ t a ht_nonneg
  have hdiag₂ := hdiag_of_repr (x := xmm) (μ := ν₂) hrepr₂ t a ht_nonneg
  have hdiag₃ := hdiag_of_repr (x := xpi) (μ := ν₃) hrepr₃ t a ht_nonneg
  have hdiag₄ := hdiag_of_repr (x := xmi) (μ := ν₄) hrepr₄ t a ht_nonneg
  have hpol :
      @inner ℂ (OSHilbertSpace OS) _ xF ((Aext t a) xG) =
        (1 / 4 : ℂ) *
          (@inner ℂ (OSHilbertSpace OS) _ (xF + xG) ((Aext t a) (xF + xG)) -
            @inner ℂ (OSHilbertSpace OS) _ (xF - xG) ((Aext t a) (xF - xG)) -
            Complex.I *
              @inner ℂ (OSHilbertSpace OS) _ (xF + Complex.I • xG)
                ((Aext t a) (xF + Complex.I • xG)) +
            Complex.I *
              @inner ℂ (OSHilbertSpace OS) _ (xF - Complex.I • xG)
                ((Aext t a) (xF - Complex.I • xG))) := by
    exact (inner_polarization_clm (Aext t a) xF xG).symm
  calc
    (if ht : 0 < t then
      @inner ℂ (OSHilbertSpace OS) _ xF
        ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
          ((osSpatialTranslateHilbert (d := d) OS a) xG))
    else
      @inner ℂ (OSHilbertSpace OS) _ xF
        ((osSpatialTranslateHilbert (d := d) OS a) xG))
        = @inner ℂ (OSHilbertSpace OS) _ xF ((Aext t a) xG) := by
            by_cases ht : 0 < t <;> simp [Aext, ht]
    _ =
      (1 / 4 : ℂ) *
        (@inner ℂ (OSHilbertSpace OS) _ (xF + xG) ((Aext t a) (xF + xG)) -
          @inner ℂ (OSHilbertSpace OS) _ (xF - xG) ((Aext t a) (xF - xG)) -
          Complex.I *
            @inner ℂ (OSHilbertSpace OS) _ (xF + Complex.I • xG)
              ((Aext t a) (xF + Complex.I • xG)) +
          Complex.I *
            @inner ℂ (OSHilbertSpace OS) _ (xF - Complex.I • xG)
              ((Aext t a) (xF - Complex.I • xG))) := hpol
    _ =
      (1 / 4 : ℂ) *
        (@inner ℂ (OSHilbertSpace OS) _ xpp ((Aext t a) xpp) -
          @inner ℂ (OSHilbertSpace OS) _ xmm ((Aext t a) xmm) -
          Complex.I * @inner ℂ (OSHilbertSpace OS) _ xpi ((Aext t a) xpi) +
          Complex.I * @inner ℂ (OSHilbertSpace OS) _ xmi ((Aext t a) xmi)) := by
            rw [← hxpp, ← hxmm, ← hxpi, ← hxmi]
    _ =
      (1 / 4 : ℂ) *
        ((∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
          (∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
          Complex.I *
            (∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
          Complex.I *
            (∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
            rw [hdiag₁, hdiag₂, hdiag₃, hdiag₄]

theorem exists_approx_identity_schwartz
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : SchwartzSpacetime d),
      (∀ x : SpacetimeDim d, 0 ≤ (φ x).re) ∧
      (∀ x : SpacetimeDim d, (φ x).im = 0) ∧
      (∫ x : SpacetimeDim d, φ x = 1) ∧
      HasCompactSupport (φ : SpacetimeDim d → ℂ) ∧
      tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
      tsupport (φ : SpacetimeDim d → ℂ) ⊆ Metric.ball 0 ε := by
  let c : SpacetimeDim d := Fin.cons (ε / 2) 0
  let b : ContDiffBump c := ⟨ε / 8, ε / 4, by linarith, by linarith⟩
  let f : SpacetimeDim d → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let g₀ := HasCompactSupport.toSchwartzMap hf_compact hf_smooth
  have hg₀_int_ne : ∫ x : SpacetimeDim d, g₀ x ≠ 0 := by
    change ∫ x, (↑(b x) : ℂ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt b.integral_pos)
  let φ := (∫ x : SpacetimeDim d, g₀ x)⁻¹ • g₀
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Complex.mul_re]
    have hg₀_im : (g₀ x).im = 0 := Complex.ofReal_im (b x)
    have hg₀_re : 0 ≤ (g₀ x).re := Complex.ofReal_re (b x) ▸ b.nonneg
    have hint_im : (∫ u : SpacetimeDim d, g₀ u).im = 0 := by
      rw [show (fun u => g₀ u) = (fun u => (↑(b u) : ℂ)) from rfl]
      rw [integral_complex_ofReal]
      simp
    have hinv_im : ((∫ u : SpacetimeDim d, g₀ u)⁻¹).im = 0 := by
      rw [Complex.inv_im, hint_im]
      ring_nf
    rw [hg₀_im, hinv_im]
    ring_nf
    apply mul_nonneg _ hg₀_re
    rw [Complex.inv_re]
    apply div_nonneg
    · change 0 ≤ (∫ u, (↑(b u) : ℂ)).re
      rw [integral_complex_ofReal]
      simp only [Complex.ofReal_re]
      exact le_of_lt b.integral_pos
    · exact Complex.normSq_nonneg _
  · intro x
    simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Complex.mul_im]
    have hg₀_im : (g₀ x).im = 0 := Complex.ofReal_im (b x)
    have hint_im : (∫ u : SpacetimeDim d, g₀ u).im = 0 := by
      rw [show (fun u => g₀ u) = (fun u => (↑(b u) : ℂ)) from rfl]
      rw [integral_complex_ofReal]
      simp
    have hinv_im : ((∫ u : SpacetimeDim d, g₀ u)⁻¹).im = 0 := by
      rw [Complex.inv_im, hint_im]
      ring_nf
    rw [hg₀_im, hinv_im]
    ring_nf
  · simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
    exact inv_mul_cancel₀ hg₀_int_ne
  · exact hf_compact.smul_left
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hsubset : tsupport (φ : SpacetimeDim d → ℂ) ⊆ tsupport (g₀ : SpacetimeDim d → ℂ) := by
      exact tsupport_smul_subset_right
        (fun _ : SpacetimeDim d => (∫ u : SpacetimeDim d, g₀ u)⁻¹)
        (g₀ : SpacetimeDim d → ℂ)
    have hx_supp : x ∈ Metric.closedBall c (ε / 4 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (ε / 4) := by
        intro y hy
        rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f (hsubset hx)
    rw [Metric.mem_closedBall] at hx_supp
    have h0 : |x 0 - ε / 2| ≤ ε / 4 := by
      calc
        |x 0 - ε / 2| = |x 0 - c 0| := by simp [c]
        _ = ‖(x - c) 0‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖x - c‖ := norm_le_pi_norm _ 0
        _ = dist x c := by rw [dist_eq_norm]
        _ ≤ ε / 4 := hx_supp
    have h0' := abs_le.mp h0
    linarith
  · intro x hx
    have hsubset : tsupport (φ : SpacetimeDim d → ℂ) ⊆ tsupport (g₀ : SpacetimeDim d → ℂ) := by
      exact tsupport_smul_subset_right
        (fun _ : SpacetimeDim d => (∫ u : SpacetimeDim d, g₀ u)⁻¹)
        (g₀ : SpacetimeDim d → ℂ)
    have hx_supp : x ∈ Metric.closedBall c (ε / 4 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (ε / 4) := by
        intro y hy
        rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f (hsubset hx)
    rw [Metric.mem_ball]
    have hc : dist c (0 : SpacetimeDim d) ≤ ε / 2 := by
      rw [dist_eq_norm]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => by
        refine Fin.cases ?_ ?_ i
        · simp [c, Real.norm_eq_abs, abs_of_pos hε]
        · intro j
          simpa [c, Fin.cons_succ] using (show (0 : ℝ) ≤ ε / 2 by linarith))
    have hx' : dist x c ≤ ε / 4 := by
      simpa [Metric.mem_closedBall] using hx_supp
    linarith [dist_triangle x c 0]

/-- The Fourier-Laplace transform of a nonnegative normalized positive-time
Schwartz function is bounded by `1` in absolute value for nonnegative energy. -/
theorem fourierLaplace_nonneg_normalized_le_one
    (φ : SchwartzSpacetime d)
    (hφ_nonneg : ∀ x : SpacetimeDim d, 0 ≤ (φ x).re)
    (hφ_real : ∀ x : SpacetimeDim d, (φ x).im = 0)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
    (hφ_pos_time : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | 0 ≤ x 0})
    (E : ℝ) (hE : 0 ≤ E) (p : Fin d → ℝ) :
    ‖∫ x : SpacetimeDim d, φ x * Complex.exp (-(↑(x 0 * E) : ℂ) +
        Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i)))‖ ≤ 1 := by
  calc ‖∫ x, φ x * Complex.exp (-↑(x 0 * E) + Complex.I * ↑(∑ i, p i * x (Fin.succ i)))‖
      ≤ ∫ x, ‖φ x * Complex.exp (-↑(x 0 * E) + Complex.I * ↑(∑ i, p i * x (Fin.succ i)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ x‖ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
        · exact (SchwartzMap.integrable φ).norm
        · apply Filter.Eventually.of_forall
          intro x
          show ‖φ x * Complex.exp (-↑(x 0 * E) + Complex.I * ↑(∑ i, p i * x (Fin.succ i)))‖
            ≤ ‖φ x‖
          by_cases hx : (φ : SpacetimeDim d → ℂ) x = 0
          · simp [hx]
          · rw [norm_mul]
            have hx_mem : x ∈ tsupport (φ : SpacetimeDim d → ℂ) :=
              subset_tsupport _ (by rwa [Function.mem_support])
            have hx0 : 0 ≤ x 0 := hφ_pos_time hx_mem
            calc ‖φ x‖ * ‖Complex.exp (-↑(x 0 * E) + Complex.I * ↑(∑ i, p i * x (Fin.succ i)))‖
                ≤ ‖φ x‖ * 1 := by
                  gcongr
                  rw [Complex.norm_exp, Real.exp_le_one_iff]
                  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
                    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
                  ring_nf
                  nlinarith [mul_nonneg hx0 hE]
              _ = ‖φ x‖ := mul_one _
    _ = ‖∫ x, φ x‖ := by
        rw [hφ_int]
        simp
        have hnorm_re : ∀ x : SpacetimeDim d, ‖φ x‖ = (φ x).re := by
          intro x
          rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg x, (hφ_real x).symm⟩]
        simp_rw [hnorm_re]
        rw [show (fun x => (φ x).re) = (fun x => RCLike.re (φ x)) from rfl]
        rw [integral_re (SchwartzMap.integrable φ)]
        have := congrArg Complex.re hφ_int
        simpa using this
    _ = 1 := by
        rw [hφ_int]
        simp

/-- If a normalized real nonnegative Schwartz sequence has support shrinking to
the origin, then its Fourier-Laplace transform converges pointwise to `1`. -/
theorem fourierLaplace_approx_identity_tendsto_one
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (E : ℝ) (p : Fin d → ℝ) :
    Filter.Tendsto (fun n => ∫ x : SpacetimeDim d,
        φ_seq n x * Complex.exp (-(↑(x 0 * E) : ℂ) +
          Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i))))
      Filter.atTop (nhds 1) := by
  let ψ : SpacetimeDim d → ℂ := fun x =>
    Complex.exp (-(↑(x 0 * E) : ℂ) +
      Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i)))
  have hψ_cont : Continuous ψ := by
    continuity
  have hψ0 : ψ 0 = 1 := by
    simp [ψ]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by
    linarith
  have hψ_cont0 : ContinuousAt ψ 0 := hψ_cont.continuousAt
  rw [Metric.continuousAt_iff] at hψ_cont0
  obtain ⟨δ, hδpos, hδ⟩ := hψ_cont0 (ε / 2) hε2
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n + 1 : ℝ) < δ := by
    rcases exists_nat_one_div_lt hδpos with ⟨N, hN⟩
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hNle : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) hNle
    exact lt_of_le_of_lt hmono hN
  filter_upwards [hsmall] with n hn
  have hnorm_int : ∫ x : SpacetimeDim d, ‖φ_seq n x‖ = 1 := by
    have hnorm_re : ∀ x : SpacetimeDim d, ‖φ_seq n x‖ = (φ_seq n x).re := by
      intro x
      rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg n x, (hφ_real n x).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun x => (φ_seq n x).re) = (fun x => RCLike.re (φ_seq n x)) from rfl]
    rw [integral_re (SchwartzMap.integrable (φ_seq n))]
    have := congrArg Complex.re (hφ_int n)
    simpa using this
  have hbound : ∀ x : SpacetimeDim d,
      ‖φ_seq n x * (ψ x - 1)‖ ≤ (ε / 2) * ‖φ_seq n x‖ := by
    intro x
    by_cases hx : x ∈ tsupport (φ_seq n : SpacetimeDim d → ℂ)
    · have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := hφ_support n hx
      have hxdist : dist x 0 < δ := by
        have : dist x 0 < 1 / (n + 1 : ℝ) := by
          simpa [Metric.mem_ball] using hxball
        exact lt_of_lt_of_le this hn.le
      have hψx : ‖ψ x - ψ 0‖ < ε / 2 := by
        simpa [dist_eq_norm] using hδ hxdist
      calc
        ‖φ_seq n x * (ψ x - 1)‖ = ‖φ_seq n x‖ * ‖ψ x - 1‖ := by
          rw [norm_mul]
        _ ≤ ‖φ_seq n x‖ * (ε / 2) := by
          gcongr
          simpa [hψ0] using hψx.le
        _ = (ε / 2) * ‖φ_seq n x‖ := by
          ring
    · have hx0 : φ_seq n x = 0 := by
        by_contra hx0
        exact hx (subset_tsupport _ (Function.mem_support.mpr hx0))
      simp [hx0]
  have hmeas : AEStronglyMeasurable (fun x => φ_seq n x * (ψ x - 1)) := by
    exact ((SchwartzMap.continuous (φ_seq n)).mul (hψ_cont.sub continuous_const)).aestronglyMeasurable
  have hIntDiff : Integrable (fun x => φ_seq n x * (ψ x - 1)) := by
    refine Integrable.mono' (((SchwartzMap.integrable (φ_seq n)).norm).const_mul (ε / 2)) hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd : Integrable (fun x => φ_seq n x * ψ x) := by
    have hEq : (fun x => φ_seq n x * ψ x) = fun x => φ_seq n x * (ψ x - 1) + φ_seq n x := by
      funext x
      ring
    rw [hEq]
    exact hIntDiff.add (SchwartzMap.integrable (φ_seq n))
  have hEqInt :
      (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - 1 =
        ∫ x : SpacetimeDim d, φ_seq n x * (ψ x - 1) := by
    calc
      (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - 1
          = (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ∫ x : SpacetimeDim d, φ_seq n x := by
              rw [hφ_int n]
      _ = ∫ x : SpacetimeDim d, ((φ_seq n x * ψ x) - φ_seq n x) := by
            rw [← MeasureTheory.integral_sub hIntProd (SchwartzMap.integrable (φ_seq n))]
      _ = ∫ x : SpacetimeDim d, φ_seq n x * (ψ x - 1) := by
            congr with x
            ring
  calc
    dist (∫ x : SpacetimeDim d, φ_seq n x * ψ x) 1
        = ‖(∫ x : SpacetimeDim d, φ_seq n x * ψ x) - 1‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ x : SpacetimeDim d, φ_seq n x * (ψ x - 1)‖ := by
          rw [hEqInt]
    _ ≤ ∫ x : SpacetimeDim d, ‖φ_seq n x * (ψ x - 1)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : SpacetimeDim d, (ε / 2) * ‖φ_seq n x‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (φ_seq n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ x : SpacetimeDim d, ‖φ_seq n x‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]
    _ < ε := by
          linarith

/-- The Laplace-Fourier kernel of a finite measure on `[0,∞) × ℝ^d` is bounded
by the total mass of the measure on positive Euclidean time. -/
theorem laplaceFourier_kernel_bounded
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [hfin : IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (ξ : SpacetimeDim d) (hξ : 0 < ξ 0) :
    ‖∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)))
        ∂μ‖ ≤ (μ Set.univ).toReal := by
  calc ‖∫ p, Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i, p.2 i * ξ (Fin.succ i))) ∂μ‖
      ≤ ∫ p, ‖Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i, p.2 i * ξ (Fin.succ i)))‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ × (Fin d → ℝ), (1 : ℝ) ∂μ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
        · exact integrable_const 1
        · have hae_nonneg : ∀ᵐ (a : ℝ × (Fin d → ℝ)) ∂μ, 0 ≤ a.1 := by
            rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
            suffices h : {x : ℝ × (Fin d → ℝ) | 0 ≤ x.1}ᶜ ⊆ (Set.Iio 0).prod Set.univ by
              exact le_antisymm (le_trans (μ.mono h) (le_of_eq hsupp)) (zero_le _)
            intro x hx
            rcases x with ⟨E, p⟩
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
            exact Set.mk_mem_prod hx (Set.mem_univ _)
          exact hae_nonneg.mono (fun a hE => by
            rcases a with ⟨E, p⟩
            show ‖Complex.exp (-(↑(ξ 0 * E) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i, p i * ξ (Fin.succ i)))‖ ≤ 1
            rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
            simp only [Complex.neg_re, Complex.ofReal_re,
              Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
            ring_nf
            simp only [Real.exp_zero, mul_one]
            rw [Real.exp_le_one_iff]
            nlinarith [mul_nonneg (le_of_lt hξ) hE])
    _ = (μ Set.univ).toReal := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real_def]

end
