import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapSelectedSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIConfigurationTranslation

/-!
# OS II Chapter VI: Radial Multi-Gap Translations

Frozen spectator gaps act on a radial endpoint source by independent
translations of its absolute configuration points.  The adjacent increments
are exactly the axis-pair gap vectors.  This file proves the resulting source
covariance and shows that one common slope continues to control all oriented
supports after every such translation.
-/

noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

/-- Flatten the physical spacetime translation represented by each
axis-pair gap. -/
def osiiStep4AxisPairGapTranslationFlat
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    Fin (k * (d + 1)) -> Real :=
  fun a =>
    let p := finProdFinEquiv.symm a
    osiiAxisPairChronologicalGapTranslation T x p.1 p.2

@[simp] theorem osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (mu : Fin (d + 1)) :
    osiiStep4AxisPairGapTranslationFlat d T x
        (finProdFinEquiv (i, mu)) =
      osiiAxisPairChronologicalGapTranslation T x i mu := by
  simp [osiiStep4AxisPairGapTranslationFlat]

/-- Every physical gap translation has strictly positive time component in
every oriented frame at the same slope. -/
theorem axisPairChronologicalGapTranslation_rotated_time_pos
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    0 < ((osiiAxisPairRotationData T a).matrix.mulVec
      (osiiAxisPairChronologicalGapTranslation T x i)) 0 := by
  simp only [osiiAxisPairChronologicalGapTranslation,
    Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply,
    Pi.smul_apply]
  apply Finset.sum_pos
  · intro b hb
    exact mul_pos (osiiAxisPairPositiveCoefficients_pos (x i) b)
      ((osiiAxisPairRotationData T a).mulVec_dir_time_pos hT b)
  · exact ⟨((0 : Fin d), false), Finset.mem_univ _⟩

/-- Prefix point translations are strictly increasing in every oriented time
coordinate. -/
theorem axisPairChronologicalPointTranslation_rotated_time_strictMono
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (a : osiiAxisPairIndex d) :
    StrictMono (fun j : Fin (k + 1) =>
      ((osiiAxisPairRotationData T a).matrix.mulVec
        (osiiAxisPairChronologicalPointTranslation T x j)) 0) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hgap := axisPairChronologicalGapTranslation_rotated_time_pos
    d k T hT x i a
  have hdiff := congrArg
    (fun v : SpacetimeDim d =>
      ((osiiAxisPairRotationData T a).matrix.mulVec v) 0)
    (osiiAxisPairChronologicalPointTranslation_sub_castSucc T x i)
  change
    ((osiiAxisPairRotationData T a).matrix.mulVec
        (osiiAxisPairChronologicalPointTranslation T x i.succ -
          osiiAxisPairChronologicalPointTranslation T x i.castSucc)) 0 =
      ((osiiAxisPairRotationData T a).matrix.mulVec
        (osiiAxisPairChronologicalGapTranslation T x i)) 0 at hdiff
  rw [Matrix.mulVec_sub] at hdiff
  dsimp at hdiff
  linarith

/-- Independently translating absolute points by negative chronological
prefixes preserves support in every oriented positive-time region. -/
theorem translateConfiguration_axisPairGaps_preserves_all_orientedPositive
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (f : SchwartzNPoint d (k + 1))
    (hf : forall a : osiiAxisPairIndex d,
      tsupport (f : NPointDomain d (k + 1) -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := k + 1)
          (osiiAxisPairRotationData T a).matrix) :
    forall a : osiiAxisPairIndex d,
      tsupport
          ((translateSchwartzConfiguration
            (fun j => -osiiAxisPairChronologicalPointTranslation T x j) f :
              SchwartzNPoint d (k + 1)) :
                NPointDomain d (k + 1) -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := k + 1)
          (osiiAxisPairRotationData T a).matrix := by
  intro a u hu
  let p : NPointDomain d (k + 1) := fun j =>
    osiiAxisPairChronologicalPointTranslation T x j
  have hcontinuous : Continuous (fun v : NPointDomain d (k + 1) =>
      v + fun j => -p j) := by
    fun_prop
  have hupre : u + (fun j => -p j) ∈
      tsupport (f : NPointDomain d (k + 1) -> Complex) := by
    exact tsupport_comp_subset_preimage
      (f : NPointDomain d (k + 1) -> Complex) hcontinuous hu
  have hbase := hf a hupre
  have hpmono :=
    (axisPairChronologicalPointTranslation_rotated_time_strictMono
      d k T hT x a).monotone
  have hpzero :
      ((osiiAxisPairRotationData T a).matrix.mulVec
        (p (0 : Fin (k + 1)))) 0 = 0 := by
    simp [p, osiiAxisPairChronologicalPointTranslation_zero]
  intro i
  constructor
  · have hbi := (hbase i).1
    change
      0 < ((osiiAxisPairRotationData T a).matrix.mulVec
        (u i + -p i)) 0 at hbi
    rw [Matrix.mulVec_add, Matrix.mulVec_neg] at hbi
    simp only [Pi.add_apply, Pi.neg_apply] at hbi
    have hpi : 0 <=
        ((osiiAxisPairRotationData T a).matrix.mulVec (p i)) 0 := by
      calc
        0 = ((osiiAxisPairRotationData T a).matrix.mulVec (p 0)) 0 :=
          hpzero.symm
        _ <= ((osiiAxisPairRotationData T a).matrix.mulVec (p i)) 0 :=
          hpmono (Fin.zero_le i)
    change 0 < ((osiiAxisPairRotationData T a).matrix.mulVec (u i)) 0
    linarith
  · intro j hij
    have hbij := (hbase i).2 j hij
    change
      ((osiiAxisPairRotationData T a).matrix.mulVec
          (u i + -p i)) 0 <
        ((osiiAxisPairRotationData T a).matrix.mulVec
          (u j + -p j)) 0 at hbij
    rw [Matrix.mulVec_add, Matrix.mulVec_neg,
      Matrix.mulVec_add, Matrix.mulVec_neg] at hbij
    simp only [Pi.add_apply, Pi.neg_apply] at hbij
    have hpij :
        ((osiiAxisPairRotationData T a).matrix.mulVec (p i)) 0 <=
          ((osiiAxisPairRotationData T a).matrix.mulVec (p j)) 0 :=
      hpmono hij.le
    change
      ((osiiAxisPairRotationData T a).matrix.mulVec (u i)) 0 <
        ((osiiAxisPairRotationData T a).matrix.mulVec (u j)) 0
    linarith

/-- Adjacent reduced differences of a translated absolute configuration are
the original differences minus the corresponding gap translations. -/
theorem reducedDiffMapReal_sub_axisPairChronologicalPointTranslation
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (u : NPointDomain d (k + 1)) :
    BHW.reducedDiffMapReal (k + 1) d
        (fun j => u j - osiiAxisPairChronologicalPointTranslation T x j) =
      fun i => BHW.reducedDiffMapReal (k + 1) d u i -
        osiiAxisPairChronologicalGapTranslation T x i := by
  funext i mu
  have hgap := congrFun
    (osiiAxisPairChronologicalPointTranslation_sub_castSucc T x i) mu
  simp only [Pi.sub_apply] at hgap
  let A : Real := u i.succ mu
  let B : Real := u i.castSucc mu
  let P : Real :=
    osiiAxisPairChronologicalPointTranslation T x i.succ mu
  let Q : Real :=
    osiiAxisPairChronologicalPointTranslation T x i.castSucc mu
  let G : Real := osiiAxisPairChronologicalGapTranslation T x i mu
  change (A - P) - (B - Q) = (A - B) - G
  have hG : P - Q = G := by
    simpa [P, Q, G] using hgap
  rw [← hG]
  ring

/-- Translating the absolute normalized lift by chronological prefixes is
exactly translation of its reduced source by the corresponding gap vectors.
The basepoint cutoff is unchanged because the zeroth prefix is zero. -/
theorem translateConfiguration_reducedTestLift_axisPairGaps
    (d k : Nat) [NeZero d] [NeZero k]
    (chi : SchwartzMap (SpacetimeDim d) Complex)
    (phi : SchwartzNPoint d k)
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    translateSchwartzConfiguration
        (fun j => -osiiAxisPairChronologicalPointTranslation T x j)
        (BHW.reducedTestLift k d chi phi) =
      BHW.reducedTestLift k d chi
        (translateSchwartzConfiguration
          (fun i => -osiiAxisPairChronologicalGapTranslation T x i) phi) := by
  ext u
  rw [translateSchwartzConfiguration_apply]
  rw [BHW.reducedTestLift_apply, BHW.reducedTestLift_apply]
  have hzero :
      osiiAxisPairChronologicalPointTranslation T x
          (0 : Fin (k + 1)) = 0 :=
    osiiAxisPairChronologicalPointTranslation_zero T x
  have hu :
      u + (fun j => -osiiAxisPairChronologicalPointTranslation T x j) =
        fun j => u j - osiiAxisPairChronologicalPointTranslation T x j := by
    ext j mu
    simp [sub_eq_add_neg]
  rw [hu,
    reducedDiffMapReal_sub_axisPairChronologicalPointTranslation d k T x u]
  simp only [hzero, sub_zero, translateSchwartzConfiguration_apply]
  congr 2

/-- Exact covariance of a radial endpoint source under simultaneous
axis-pair translations of all of its reduced gaps. -/
theorem translateConfiguration_radialEndpoint_axisPairGaps
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    translateSchwartzConfiguration
        (fun j => -osiiAxisPairChronologicalPointTranslation T x j)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho endpointCenter endpointImag center y y') =
      osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag
        (center + osiiStep4AxisPairGapTranslationFlat d T x) y y' := by
  ext u
  rw [translateSchwartzConfiguration_apply]
  rw [
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_apply,
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_apply]
  have hzero :
      osiiAxisPairChronologicalPointTranslation T x
          (0 : Fin (k + 1)) = 0 :=
    osiiAxisPairChronologicalPointTranslation_zero T x
  have hred :=
    reducedDiffMapReal_sub_axisPairChronologicalPointTranslation d k T x u
  have hu :
      u + (fun j => -osiiAxisPairChronologicalPointTranslation T x j) =
        fun j => u j - osiiAxisPairChronologicalPointTranslation T x j := by
    ext j mu
    simp [sub_eq_add_neg]
  rw [hu, hred]
  simp only [hzero, sub_zero]
  congr 1
  rw [
    osiiStep4CenteredPartialConvolutionKernelFullSource_apply,
    osiiStep4CenteredPartialConvolutionKernelFullSource_apply]
  congr 2
  funext a
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  have hi : (finProdFinEquiv (i, mu)).divNat = i :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, mu))
  have hmu : (finProdFinEquiv (i, mu)).modNat = mu :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, mu))
  apply Complex.ext
  · simp only [osiiStep4ComplexOfRealImag_re, Pi.sub_apply, Pi.add_apply]
    rw [finProdFinEquiv.symm_apply_apply]
    simp [osiiStep4AxisPairGapTranslationFlat]
    ring
  · simp

/-- Version of oriented-support preservation which also covers an endpoint
source with no internal reduced gaps. -/
theorem translateConfiguration_axisPairGaps_preserves_all_orientedPositive_all
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (f : SchwartzNPoint d (k + 1))
    (hf : forall a : osiiAxisPairIndex d,
      tsupport (f : NPointDomain d (k + 1) -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := k + 1)
          (osiiAxisPairRotationData T a).matrix) :
    forall a : osiiAxisPairIndex d,
      tsupport
          ((translateSchwartzConfiguration
            (fun j => -osiiAxisPairChronologicalPointTranslation T x j) f :
              SchwartzNPoint d (k + 1)) :
                NPointDomain d (k + 1) -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := k + 1)
          (osiiAxisPairRotationData T a).matrix := by
  by_cases hk : k = 0
  · subst k
    have hp :
        (fun j : Fin (0 + 1) =>
          -osiiAxisPairChronologicalPointTranslation T x j) = 0 := by
      funext j
      simp [osiiAxisPairChronologicalPointTranslation]
    rw [hp, translateSchwartzConfiguration_zero]
    exact hf
  · letI : NeZero k := ⟨hk⟩
    exact translateConfiguration_axisPairGaps_preserves_all_orientedPositive
      d k T hT x f hf

/-- Version of radial endpoint covariance which also covers an endpoint
source with no internal reduced gaps. -/
theorem translateConfiguration_radialEndpoint_axisPairGaps_all
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    translateSchwartzConfiguration
        (fun j => -osiiAxisPairChronologicalPointTranslation T x j)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho endpointCenter endpointImag center y y') =
      osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag
        (center + osiiStep4AxisPairGapTranslationFlat d T x) y y' := by
  by_cases hk : k = 0
  · subst k
    have hp :
        (fun j : Fin (0 + 1) =>
          -osiiAxisPairChronologicalPointTranslation T x j) = 0 := by
      funext j
      simp [osiiAxisPairChronologicalPointTranslation]
    have hgap : osiiStep4AxisPairGapTranslationFlat d T x = 0 := by
      funext a
      exact Fin.elim0 (Fin.cast (Nat.zero_mul (d + 1)) a)
    rw [hp, translateSchwartzConfiguration_zero, hgap, add_zero]
  · letI : NeZero k := ⟨hk⟩
    exact translateConfiguration_radialEndpoint_axisPairGaps
      d k hrho endpointCenter endpointImag center y y' T x

end OSReconstruction
