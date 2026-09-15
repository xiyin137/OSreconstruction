/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.SCV.LaplaceHolomorphic
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup




















set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Complex

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

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
  change Filter.Tendsto
    ((unflattenSchwartzNPoint (d := d)) ∘ fun N =>
      OSReconstruction.bumpTruncationRadius
        (flattenSchwartzNPoint (d := d)
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))) N)
    Filter.atTop
    (nhds (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))
  rw [unflatten_flattenSchwartzNPoint_local] at hunflat
  exact hunflat

/-- Lower-layer positive-time OS Hilbert vector.  This duplicates the direct
completion representative under a name available before
`OSToWightmanPositivity.lean`, so theorem-3 closure support can be used by
`OSToWightmanBoundaryValues.lean` without an import cycle. -/
noncomputable def positiveTimeBorchersVectorCore
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))

/- Full semigroup-group positive-definiteness of the compact-support extension
of the OS matrix kernel. -/
section semigroupGroupPDExtension

end semigroupGroupPDExtension

end
