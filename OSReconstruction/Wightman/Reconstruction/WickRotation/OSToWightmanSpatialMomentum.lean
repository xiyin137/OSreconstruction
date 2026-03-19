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

noncomputable section

open MeasureTheory Complex

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

private def compactApproxPositiveTimeBorchers
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

private theorem compactApproxPositiveTimeBorchers_component_compact
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

private theorem tendsto_compactApproxPositiveTimeBorchers_component
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
    simpa [hdense.closure_eq] using (show x ∈ (Set.univ : Set (OSHilbertSpace OS)) from by simp)
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
        simpa [xF0_pre, Real.dist_eq] using (Metric.tendsto_nhds.1 hcore (ε / 5) hε5)
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

end
