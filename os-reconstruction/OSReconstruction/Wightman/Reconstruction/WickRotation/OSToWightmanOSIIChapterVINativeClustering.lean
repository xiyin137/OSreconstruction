import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativePositivity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanClusterSection43
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwartzClusterClosure

/-!
# Native clustering from the original Euclidean cluster axiom

The all-degree source identity supplies both scalar factors, including the
vacuum. Spatial translation transports the exact Fourier-Laplace source
class. Original E4 gives clustering there; the positive-form estimate gives
the translation-uniform Schwartz completion.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedFullBoundary_sourceFactor_reflected
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat) (phi : SchwartzNPoint d n)
    (f : Section43CompactOrderedSource d n)
    (hphi : section43FrequencyProjection d n phi = section43FourierLaplaceTransformComponentMap d n f) :
    starRingEnd Complex (initial.strictGeneratedFullBoundary lgc n phi) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical f.f.osConj) := by
  let e := (Reconstruction.vacuumSequence (d := d)).funcs 0
  have he (x : NPointDomain d 0) : e x = 1 := rfl
  have heord : tsupport (e : NPointDomain d 0 -> Complex) ⊆ OrderedPositiveTimeRegion d 0 := by
    intro x _
    simp [OrderedPositiveTimeRegion]
  have hecompact : HasCompactSupport (e : NPointDomain d 0 -> Complex) :=
    HasCompactSupport.of_compactSpace _
  let psi := section43TransformComponentTarget d 0 e heord hecompact
  have hpsi := section43TransformComponentTarget_freq_eq d 0 e heord hecompact
  have hpsi0 : psi 0 = 1 :=
    (section43TransformComponent_zero_eval_eq d psi e heord hecompact hpsi).trans (he 0)
  have hpair := initial.strictGeneratedFullBoundary_sourcePairing lgc n 0 phi psi
    ⟨f.f, f.ordered⟩ ⟨e, heord⟩ f.compact hecompact hphi hpsi
  have htensor : phi.conjTensorProduct psi = phi.borchersConj := by
    ext x
    change starRingEnd Complex (phi (fun i => splitFirst n 0 x (Fin.rev i))) *
      psi (splitLast n 0 x) = starRingEnd Complex (phi (fun i => x (Fin.rev i)))
    have hlast : splitLast n 0 x = 0 := Subsingleton.elim _ _
    have hfirst : splitFirst n 0 x = x := by ext i; rfl
    rw [hfirst, hlast, hpsi0, mul_one]
  have hsource : f.f.osConjTensorProduct e = f.f.osConj := by
    ext x
    simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply, he, mul_one]
    rfl
  rw [htensor, hsource] at hpair
  exact (initial.strictGeneratedFullBoundary_hermitian lgc n phi phi.borchersConj
    (fun x => SchwartzMap.borchersConj_apply phi x)).symm.trans hpair

theorem strictGeneratedFullBoundary_sourceFactor
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat) (phi : SchwartzNPoint d n)
    (f : Section43CompactOrderedSource d n)
    (hphi : section43FrequencyProjection d n phi = section43FourierLaplaceTransformComponentMap d n f) :
    initial.strictGeneratedFullBoundary lgc n phi = OS.S n (ZeroDiagonalSchwartz.ofClassical f.f) := by
  have hf := VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
    f.f f.ordered
  have hfc : VanishesToInfiniteOrderOnCoincidence f.f.osConj := by
    let e := (Reconstruction.vacuumSequence (d := d)).funcs 0
    have he (x : NPointDomain d 0) : e x = 1 := rfl
    have heq : f.f.osConjTensorProduct e = f.f.osConj := by
      ext x
      simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply, he, mul_one]
      rfl
    rw [← heq]
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      f.f e f.ordered (by intro x _; simp [OrderedPositiveTimeRegion])
  have hreal := OS.E0_reality n (ZeroDiagonalSchwartz.ofClassical f.f)
    (ZeroDiagonalSchwartz.ofClassical f.f.osConj) (by
      intro x
      rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes f.f hf,
        ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes f.f.osConj hfc]
      exact SchwartzNPoint.osConj_apply f.f x)
  have h := initial.strictGeneratedFullBoundary_sourceFactor_reflected lgc n phi f hphi
  rw [← hreal] at h
  exact (starRingEnd Complex).injective h

private theorem strictGeneratedFullBoundary_cluster_source
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat) (hm : 0 < m)
    (phi : SchwartzNPoint d n) (psi : SchwartzNPoint d m)
    (f : Section43CompactOrderedSource d n) (g : Section43CompactOrderedSource d m)
    (hphi : section43FrequencyProjection d n phi = section43FourierLaplaceTransformComponentMap d n f)
    (hpsi : section43FrequencyProjection d m psi = section43FourierLaplaceTransformComponentMap d m g)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Real, 0 < R ∧ ∀ a : Fin d -> Real, (∑ i, (a i)^2) > R^2 ->
      ‖initial.strictGeneratedFullBoundary lgc (n + m)
          (phi.conjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) psi)) -
        starRingEnd Complex (initial.strictGeneratedFullBoundary lgc n phi) *
          initial.strictGeneratedFullBoundary lgc m psi‖ < epsilon := by
  obtain ⟨R, hR, hcluster⟩ := schwinger_cluster_osConjTensorProduct_translate_spatial_right_local
    OS n m f.f f.ordered g.f g.ordered epsilon hepsilon
  refine ⟨R, hR, ?_⟩
  intro a ha
  have hga := translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    (d := d) (Fin.cons 0 a) (by simp) g.f g.ordered
  have hgac := translateSchwartzNPoint_hasCompactSupport (Fin.cons 0 a) g.f g.compact
  have hpsia := section43FrequencyProjection_translate_spatial_of_transformComponent
    m hm a psi g.f g.ordered g.compact hga hgac hpsi
  rw [initial.strictGeneratedFullBoundary_sourcePairing lgc n m phi
      (translateSchwartzNPoint (Fin.cons 0 a) psi) ⟨f.f, f.ordered⟩
      ⟨translateSchwartzNPoint (Fin.cons 0 a) g.f, hga⟩ f.compact hgac hphi hpsia,
    initial.strictGeneratedFullBoundary_sourceFactor_reflected lgc n phi f hphi,
    initial.strictGeneratedFullBoundary_sourceFactor lgc m psi g hpsi]
  exact hcluster a ha

/-- Literal full-Schwartz spatial clustering of the native family. -/
theorem strictGeneratedFullBoundary_cluster
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Real, 0 < R ∧ ∀ a : SpacetimeDim d, a 0 = 0 ->
      (∑ i : Fin d, (a i.succ)^2) > R^2 -> ∀ ga : SchwartzNPoint d m,
        (∀ x, ga x = g (fun i => x i - a)) ->
        ‖initial.strictGeneratedFullBoundary lgc (n + m) (f.tensorProduct ga) -
          initial.strictGeneratedFullBoundary lgc n f * initial.strictGeneratedFullBoundary lgc m g‖ < epsilon := by
  cases m with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro a _ _ ga hga
      have hga0 : ga 0 = g 0 := (hga 0).trans (congrArg g (Subsingleton.elim _ _))
      have hprod : f.tensorProduct ga = (g 0) • f := by
        ext x
        rw [SchwartzMap.tensorProduct_apply]
        have hlast : splitLast n 0 x = 0 := Subsingleton.elim _ _
        have hfirst : splitFirst n 0 x = x := by ext i; rfl
        rw [hlast, hga0, hfirst]
        simp [smul_eq_mul, mul_comm]
      rw [hprod, map_smul]
      change ‖(g 0) • initial.strictGeneratedFullBoundary lgc n f -
        initial.strictGeneratedFullBoundary lgc n f * g 0‖ < epsilon
      simpa [smul_eq_mul, mul_comm] using hepsilon
  | succ m =>
      obtain ⟨R, hR, hcluster⟩ := schwartz_cluster_of_dense_conjTensor
        (initial.strictGeneratedFullBoundary lgc)
        (initial.strictGeneratedFullBoundary_hermitian lgc)
        (initial.strictGeneratedFullBoundary_positive lgc)
        (initial.strictGeneratedFullBoundary_translationInvariant lgc) n (m + 1)
        _ _ (dense_section43FourierLaplace_compact_ordered_frequency_preimage d n)
        (dense_section43FourierLaplace_compact_ordered_frequency_preimage d (m + 1))
        (by
          rintro phi ⟨fsrc, hphi⟩ psi ⟨gsrc, hpsi⟩ eps heps
          exact initial.strictGeneratedFullBoundary_cluster_source lgc n (m + 1) (Nat.succ_pos m)
            phi psi fsrc gsrc hphi.symm hpsi.symm eps heps)
        f.borchersConj g epsilon hepsilon
      refine ⟨R, hR, ?_⟩
      intro a ha0 ha ga hga
      have haeq : Fin.cons 0 (fun i : Fin d => a i.succ) = a := by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [ha0]
      have hgaeq : ga = translateSchwartzNPoint a g := by
        ext x
        exact hga x
      have h := hcluster (fun i => a i.succ) ha
      rw [haeq, ← hgaeq, SchwartzMap.conjTensorProduct,
        SchwartzMap.borchersConj_borchersConj,
        initial.strictGeneratedFullBoundary_hermitian lgc n f f.borchersConj
          (fun x => SchwartzMap.borchersConj_apply f x), starRingEnd_self_apply] at h
      exact h

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
