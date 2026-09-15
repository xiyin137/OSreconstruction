import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransformCarrier
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits

/-!
# Section 4.3 Fourier-Laplace Closure

This file contains the finite-support closure step that is downstream of the
compiled transform-image positivity theorem.  It deliberately keeps the
remaining density assumption explicit and pairwise on the Section 4.3 frequency
quotient: once a sequence of transform-component carriers converges on all
finite Wightman tensor terms, positivity passes to the limiting public
`BorchersSequence`.
-/

noncomputable section

open scoped Topology FourierTransform BigOperators
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem borchersConj_continuous_closure {n : ℕ} :
    Continuous (fun f : SchwartzNPoint d n => f.borchersConj) := by
  let revCLE : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    { toFun := fun y i => y (Fin.rev i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y i => y (Fin.rev i)
      left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      right_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i)
      continuous_invFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i) }
  let revCLM : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ revCLE
  have hrev : ∀ f : SchwartzNPoint d n, revCLM f = f.reverse := by
    intro f
    ext x
    simp [revCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.reverse_apply, revCLE]
  have hconj_cont : Continuous (fun f : SchwartzNPoint d n => f.conj) := by
    let conjL : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
      { toFun := SchwartzMap.conj
        map_add' := fun f g => by
          ext x
          simp [SchwartzMap.conj_apply]
        map_smul' := fun c f => by
          simpa using (SchwartzMap.conj_smul (c := (c : ℂ)) f) }
    exact WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      conjL (fun q => by
        rcases q with ⟨k, l⟩
        refine ⟨{(k, l)}, 1, ?_⟩
        intro f
        calc
          _ = (SchwartzMap.seminorm ℝ k l) (conjL f) := rfl
          _ = (SchwartzMap.seminorm ℝ k l) f.conj := rfl
          _ ≤ (SchwartzMap.seminorm ℝ k l) f :=
            SchwartzMap.seminorm_conj_le k l f
          _ = _ := by
            simp only [one_smul, Finset.sup_singleton,
              SchwartzMap.schwartzSeminormFamily_apply])
  show Continuous (fun f => (revCLM f).conj)
  exact hconj_cont.comp revCLM.continuous |>.congr (fun f => by
    show (revCLM f).conj = f.borchersConj
    rw [hrev]
    rfl)

omit [NeZero d] in
theorem conjTensorProduct_continuous_closure {n m : ℕ} :
    Continuous
      (fun p : SchwartzNPoint d n × SchwartzNPoint d m => p.1.conjTensorProduct p.2) := by
  have hpair :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          (p.1.borchersConj, p.2)) :=
    ((borchersConj_continuous_closure (d := d)).comp continuous_fst).prodMk continuous_snd
  let h :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          p.1.borchersConj.tensorProduct p.2) :=
    SchwartzMap.tensorProduct_continuous.comp hpair
  simpa [SchwartzMap.conjTensorProduct] using h

/-- In degree zero, equality of Section 4.3 frequency projections is equality
of the unique scalar value. -/
theorem section43FrequencyProjection_zero_eval_eq
    (φ ψ : SchwartzNPoint d 0)
    (hproj :
      section43FrequencyProjection (d := d) 0 φ =
        section43FrequencyProjection (d := d) 0 ψ) :
    φ 0 = ψ 0 := by
  have hquot :
      section43PositiveEnergyQuotientMap (d := d) 0
          (section43FrequencyRepresentative (d := d) 0 φ) =
        section43PositiveEnergyQuotientMap (d := d) 0
          (section43FrequencyRepresentative (d := d) 0 ψ) := by
    simpa [section43FrequencyProjection] using hproj
  have hEqOn :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hquot
  have h0 : (0 : NPointDomain d 0) ∈ section43PositiveEnergyRegion d 0 := by
    simp [section43PositiveEnergyRegion]
  have hpoint := hEqOn h0
  rw [section43FrequencyRepresentative_zero_apply d φ 0] at hpoint
  rw [section43FrequencyRepresentative_zero_apply d ψ 0] at hpoint
  exact hpoint

/-- The finite product of Section 4.3 component frequency quotients up to
degree `B`. -/
abbrev Section43FiniteComponentProduct (d B : ℕ) [NeZero d] :=
  (n : Fin (B + 1)) → Section43PositiveEnergyComponent (d := d) n.val

/-- A compact ordered Euclidean source for one Section 4.3 Fourier-Laplace
transform component. -/
structure Section43CompactOrderedSource (d n : ℕ) [NeZero d] where
  f : SchwartzNPoint d n
  ordered :
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n
  compact : HasCompactSupport (f : NPointDomain d n → ℂ)

/-- The genuine Section 4.3 Fourier-Laplace transform component as a map from
compact ordered sources to the positive-energy quotient. -/
noncomputable def section43FourierLaplaceTransformComponentMap
    (d n : ℕ) [NeZero d] :
    Section43CompactOrderedSource d n →
      Section43PositiveEnergyComponent (d := d) n :=
  fun src =>
    section43FourierLaplaceTransformComponent d n
      src.f src.ordered src.compact

/-- If the preimage of the compact ordered Fourier-Laplace transform image is
dense in ambient Schwartz space, then the transform component map has dense
range in the Section 4.3 positive-energy quotient.  This is the quotient-map
form of the remaining analytic density theorem. -/
theorem denseRange_section43FourierLaplaceTransformComponentMap_of_dense_preimage
    (d n : ℕ) [NeZero d]
    (hpre :
      Dense
        ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
          Set.range (section43FourierLaplaceTransformComponentMap d n))) :
    DenseRange (section43FourierLaplaceTransformComponentMap d n) := by
  have hq :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap (d := d) n :
          SchwartzNPoint d n → Section43PositiveEnergyComponent (d := d) n) := by
    simpa [section43PositiveEnergyQuotientMap] using
      (section43PositiveEnergyVanishingSubmodule (d := d) n).isOpenQuotientMap_mkQ
  exact hq.dense_preimage_iff.mp hpre

/-- The finite product of genuine compact ordered Section 4.3 transform
components up to degree `B`. -/
noncomputable def section43FiniteTransformComponentMap
    (d B : ℕ) [NeZero d] :
    ((n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) →
      Section43FiniteComponentProduct d B :=
  fun src n => section43FourierLaplaceTransformComponentMap d n.val (src n)

/-- Componentwise dense range implies dense range of the finite transform
component product.  This isolates the pure product-topology step from the
analytic Fourier-Laplace density theorem. -/
theorem denseRange_section43FiniteTransformComponentMap_of_components
    (d B : ℕ) [NeZero d]
    (hdense :
      ∀ n : Fin (B + 1),
        DenseRange (section43FourierLaplaceTransformComponentMap d n.val)) :
    DenseRange (section43FiniteTransformComponentMap d B) := by
  change DenseRange
    (Pi.map
      (fun n : Fin (B + 1) =>
        section43FourierLaplaceTransformComponentMap d n.val))
  exact DenseRange.piMap hdense

/-- The positive-time Borchers sequence associated to a finite compact ordered
source tuple, padded by zero above the finite bound. -/
noncomputable def section43FiniteSource_to_positiveTimeBorchersSequence
    (d B : ℕ) [NeZero d]
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    PositiveTimeBorchersSequence d where
  toBorchersSequence :=
    { funcs := fun n =>
        if h : n ≤ B then
          (src ⟨n, Nat.lt_succ_of_le h⟩).f
        else
          0
      bound := B
      bound_spec := by
        intro n hn
        have hnot : ¬ n ≤ B := by omega
        simp [hnot] }
  ordered_tsupport := by
    intro n
    by_cases h : n ≤ B
    · simpa [h] using (src ⟨n, Nat.lt_succ_of_le h⟩).ordered
    · simp only [h, ↓reduceDIte]
      change tsupport (fun _ : NPointDomain d n => (0 : ℂ)) ⊆
        OrderedPositiveTimeRegion d n
      simp

/-- Compactness of each padded component of
`section43FiniteSource_to_positiveTimeBorchersSequence`. -/
theorem section43FiniteSource_to_positiveTimeBorchersSequence_compact
    (d B : ℕ) [NeZero d]
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    ∀ n,
      HasCompactSupport
        ((((section43FiniteSource_to_positiveTimeBorchersSequence d B src :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  intro n
  by_cases h : n ≤ B
  · simpa [section43FiniteSource_to_positiveTimeBorchersSequence, h] using
      (src ⟨n, Nat.lt_succ_of_le h⟩).compact
  · simp only [section43FiniteSource_to_positiveTimeBorchersSequence, h, ↓reduceDIte]
    change HasCompactSupport (fun _ : NPointDomain d n => (0 : ℂ))
    exact HasCompactSupport.zero

/-- The source-decorated transform-component carrier associated to a finite
compact ordered source tuple, padded by zero above the finite bound. -/
noncomputable def section43FiniteSource_to_BvtTransformComponentSequence
    (d B : ℕ) [NeZero d]
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    BvtTransformComponentSequence d where
  toBorchers :=
    { funcs := fun n =>
        if h : n ≤ B then
          section43TransformComponentTarget d n
            (src ⟨n, Nat.lt_succ_of_le h⟩).f
            (src ⟨n, Nat.lt_succ_of_le h⟩).ordered
            (src ⟨n, Nat.lt_succ_of_le h⟩).compact
        else
          0
      bound := B
      bound_spec := by
        intro n hn
        have hnot : ¬ n ≤ B := by omega
        simp [hnot] }
  source := section43FiniteSource_to_positiveTimeBorchersSequence d B src
  source_compact :=
    section43FiniteSource_to_positiveTimeBorchersSequence_compact d B src
  freq_eq := by
    intro n
    by_cases h : n ≤ B
    · simpa [section43FiniteSource_to_positiveTimeBorchersSequence,
        section43FourierLaplaceTransformComponentMap, h] using
        section43TransformComponentTarget_freq_eq d n
          (src ⟨n, Nat.lt_succ_of_le h⟩).f
          (src ⟨n, Nat.lt_succ_of_le h⟩).ordered
          (src ⟨n, Nat.lt_succ_of_le h⟩).compact
    · have hzero_ord :
          tsupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
            OrderedPositiveTimeRegion d n := by
        change tsupport (fun _ : NPointDomain d n => (0 : ℂ)) ⊆
          OrderedPositiveTimeRegion d n
        simp
      have hzero_compact :
          HasCompactSupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
        HasCompactSupport.zero
      simp only [section43FiniteSource_to_positiveTimeBorchersSequence, h,
        ↓reduceDIte]
      change section43FrequencyProjection (d := d) n (0 : SchwartzNPoint d n) =
        section43FourierLaplaceTransformComponent d n
          (0 : SchwartzNPoint d n) hzero_ord hzero_compact
      rw [section43FourierLaplaceTransformComponent_zero]
      exact map_zero (section43FrequencyProjection (d := d) n)

end OSReconstruction
