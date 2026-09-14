/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapSourcewise

















noncomputable section

open Complex Filter Topology
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d]

/-- Joint evaluation is continuous when the functionals are uniformly
equicontinuous, every fixed-test pairing is continuous in the parameter, and
the test itself varies continuously. -/
theorem continuous_joint_apply_of_uniformEquicontinuous
    {Z X E : Type*}
    [TopologicalSpace Z] [TopologicalSpace X] [UniformSpace E]
    (T : Z → E → ℂ)
    (f : X → E)
    (hT_equi : UniformEquicontinuous T)
    (hT_fixed : ∀ e : E, Continuous (fun z => T z e))
    (hf : Continuous f) :
    Continuous (fun p : Z × X => T p.1 (f p.2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hequi :
      ∀ᶠ e in 𝓝 (f p.2), ∀ z : Z,
        dist (T z (f p.2)) (T z e) < ε / 2 := by
    exact
      (Metric.equicontinuousAt_iff_right.mp
        (hT_equi.equicontinuous (f p.2))) (ε / 2) (by positivity)
  have hequi_prod :
      ∀ᶠ q in 𝓝 p, ∀ z : Z,
        dist (T z (f p.2)) (T z (f q.2)) < ε / 2 :=
    (hf.continuousAt.tendsto.comp
      continuous_snd.continuousAt.tendsto).eventually hequi
  have hfixed :
      ∀ᶠ q in 𝓝 p,
        dist (T q.1 (f p.2)) (T p.1 (f p.2)) < ε / 2 := by
    have hz :
        ∀ᶠ z in 𝓝 p.1,
          dist (T z (f p.2)) (T p.1 (f p.2)) < ε / 2 :=
      (Metric.tendsto_nhds.mp
        (hT_fixed (f p.2)).continuousAt.tendsto)
        (ε / 2) (by positivity)
    exact continuous_fst.continuousAt.tendsto.eventually hz
  filter_upwards [hequi_prod, hfixed] with q hq_equi hq_fixed
  calc
    dist (T q.1 (f q.2)) (T p.1 (f p.2))
        ≤ dist (T q.1 (f q.2)) (T q.1 (f p.2)) +
            dist (T q.1 (f p.2)) (T p.1 (f p.2)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add (by simpa [dist_comm] using hq_equi q.1) hq_fixed
    _ = ε := by ring

/-- A jointly continuous family indexed by a subtype gives continuity of any
total extension on the original carrier, provided the two formulas agree
there. -/
theorem continuousOn_joint_of_subtype
    {Z X Y : Type*}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set Z} {V : Set X}
    (f : S → X → Y)
    (g : Z → X → Y)
    (hf : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ V))
    (hfg : ∀ z (hz : z ∈ S) x, g z x = f ⟨z, hz⟩ x) :
    ContinuousOn (Function.uncurry g) (S ×ˢ V) := by
  rw [continuousOn_iff_continuous_restrict]
  let lift :
      {p : Z × X // p ∈ S ×ˢ V} → S × X :=
    fun p => (⟨p.1.1, p.2.1⟩, p.1.2)
  have hlift : Continuous lift := by
    apply Continuous.prodMk
    · exact
        (continuous_fst.comp continuous_subtype_val).subtype_mk
          (fun p => p.2.1)
    · exact continuous_snd.comp continuous_subtype_val
  have hmaps :
      Set.MapsTo lift Set.univ (Set.univ ×ˢ V) := by
    intro p _
    exact ⟨Set.mem_univ _, p.2.2⟩
  have hcomp :
      Continuous
        (fun p : {p : Z × X // p ∈ S ×ˢ V} =>
          f ⟨p.1.1, p.2.1⟩ p.1.2) := by
    exact continuousOn_univ.mp
      (hf.comp hlift.continuousOn hmaps)
  convert hcomp using 1
  funext p
  exact hfg p.1.1 p.2.1 p.1.2

namespace OSIIAxisPairMultiGapSourcewiseMZFamily

/-- Flatten the nested finite multi-gap coordinate family without imposing a
nonempty-gap hypothesis. -/
def nestedCoordinateCLE :
    (Fin k → osiiAxisPairIndex d → ℂ) ≃L[ℂ]
      ((Fin k × osiiAxisPairIndex d) → ℂ) := by
  apply LinearEquiv.toContinuousLinearEquiv
  exact
    { toFun := fun z p => z p.1 p.2
      invFun := fun z i a => z (i, a)
      left_inv := by
        intro z
        rfl
      right_inv := by
        intro z
        rfl
      map_add' := by
        intro z w
        rfl
      map_smul' := by
        intro c z
        rfl }

/-- A coherent choice of the unique full Schwartz distribution at every
interior point of a multi-gap sourcewise MZ family. -/
structure SchwartzDistributionFamily
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k) where
  distribution :
    {z : Fin k → osiiAxisPairIndex d → ℂ //
      z ∈ osiiAxisPairMultiGapLogDomain d k} →
      SchwartzNPoint d n →L[ℂ] ℂ
  productTensor :
    ∀ z (fs : Fin n → SchwartzSpacetime d),
      distribution z (SchwartzMap.productTensor fs) =
        P.toFun fs z.1

/-- Pointwise existence and uniqueness choose the canonical distribution
family. -/
noncomputable def schwartzDistributionFamilyOfExistsUnique
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (hexists :
      ∀ z : {z : Fin k → osiiAxisPairIndex d → ℂ //
        z ∈ osiiAxisPairMultiGapLogDomain d k},
        ∃! W : SchwartzNPoint d n →L[ℂ] ℂ,
          ∀ fs : Fin n → SchwartzSpacetime d,
            W (SchwartzMap.productTensor fs) = P.toFun fs z.1) :
    P.SchwartzDistributionFamily where
  distribution := fun z => Classical.choose (hexists z)
  productTensor := by
    intro z fs
    exact (Classical.choose_spec (hexists z)).1 fs

namespace SchwartzDistributionFamily

variable {P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k}

/-- Totalized pairing with one full Schwartz test.  Outside the carrier the
value is zero; all analytic statements are restricted to the carrier. -/
noncomputable def pairing
    (A : P.SchwartzDistributionFamily)
    (f : SchwartzNPoint d n)
    (z : Fin k → osiiAxisPairIndex d → ℂ) : ℂ :=
  if hz : z ∈ osiiAxisPairMultiGapLogDomain d k then
    A.distribution ⟨z, hz⟩ f
  else
    0

@[simp] theorem pairing_of_mem
    (A : P.SchwartzDistributionFamily)
    (f : SchwartzNPoint d n)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    A.pairing f z = A.distribution ⟨z, hz⟩ f := by
  simp [pairing, hz]

/-- Pure product tensors recover the original sourcewise MZ scalar branch. -/
theorem pairing_productTensor
    (A : P.SchwartzDistributionFamily)
    (fs : Fin n → SchwartzSpacetime d)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    A.pairing (SchwartzMap.productTensor fs) z =
      P.toFun fs z := by
  rw [A.pairing_of_mem _ z hz]
  exact A.productTensor ⟨z, hz⟩ fs

@[simp] theorem pairing_zero
    (A : P.SchwartzDistributionFamily)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    A.pairing (0 : SchwartzNPoint d n) z = 0 := by
  by_cases hz : z ∈ osiiAxisPairMultiGapLogDomain d k
  · simp [A.pairing_of_mem _ z hz]
  · simp [pairing, hz]

@[simp] theorem pairing_add
    (A : P.SchwartzDistributionFamily)
    (f g : SchwartzNPoint d n)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    A.pairing (f + g) z = A.pairing f z + A.pairing g z := by
  by_cases hz : z ∈ osiiAxisPairMultiGapLogDomain d k
  · simp [A.pairing_of_mem _ z hz]
  · simp [pairing, hz]

@[simp] theorem pairing_smul
    (A : P.SchwartzDistributionFamily)
    (c : ℂ)
    (f : SchwartzNPoint d n)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    A.pairing (c • f) z = c * A.pairing f z := by
  by_cases hz : z ∈ osiiAxisPairMultiGapLogDomain d k
  · simp [A.pairing_of_mem _ z hz]
  · simp [pairing, hz]

/-- Pairings with product tensors are holomorphic on the multi-gap carrier. -/
theorem differentiableOn_pairing_productTensor
    (A : P.SchwartzDistributionFamily)
    (fs : Fin n → SchwartzSpacetime d) :
    DifferentiableOn ℂ
      (A.pairing (SchwartzMap.productTensor fs))
      (osiiAxisPairMultiGapLogDomain d k) := by
  apply (P.holomorphic fs).congr
  intro z hz
  exact A.pairing_productTensor fs z hz

/-- Holomorphy extends algebraically to the span of product tensors. -/
theorem differentiableOn_pairing_of_mem_productTensor_span
    (A : P.SchwartzDistributionFamily)
    (f : SchwartzNPoint d n)
    (hf :
      f ∈ Submodule.span ℂ
        {F : SchwartzNPoint d n |
          ∃ fs : Fin n → SchwartzSpacetime d,
            F = SchwartzMap.productTensor fs}) :
    DifferentiableOn ℂ (A.pairing f)
      (osiiAxisPairMultiGapLogDomain d k) := by
  let D : Set (SchwartzNPoint d n) :=
    {F | ∃ fs : Fin n → SchwartzSpacetime d,
      F = SchwartzMap.productTensor fs}
  change f ∈ Submodule.span ℂ D at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨fs, rfl⟩
    exact A.differentiableOn_pairing_productTensor fs
  · apply (differentiableOn_const (c := (0 : ℂ))).congr
    intro z _hz
    exact A.pairing_zero z
  · intro g h _hg _hh hdiffg hdiffh
    apply (hdiffg.add hdiffh).congr
    intro z _hz
    exact A.pairing_add g h z
  · intro c g _hg hdiff
    apply ((differentiableOn_const (c := c)).mul hdiff).congr
    intro z _hz
    exact A.pairing_smul c g z

/-- The exact compact boundedness condition needed to pass from product
tensors to arbitrary full Schwartz tests. -/
def LocallyPointwiseBounded
    (A : P.SchwartzDistributionFamily) : Prop :=
  ∀ (K : Set (Fin k → osiiAxisPairIndex d → ℂ)),
    IsCompact K →
    K ⊆ osiiAxisPairMultiGapLogDomain d k →
    ∀ f : SchwartzNPoint d n, ∃ C : ℝ,
      ∀ z ∈ K, ‖A.pairing f z‖ ≤ C

namespace NuclearApproximation

end NuclearApproximation

/-- Compact pointwise boundedness gives uniform equicontinuity of the
recovered full Schwartz distributions. -/
theorem uniformEquicontinuous_distribution_on_compact
    (A : P.SchwartzDistributionFamily)
    (hA : A.LocallyPointwiseBounded)
    (K : Set (Fin k → osiiAxisPairIndex d → ℂ))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ osiiAxisPairMultiGapLogDomain d k) :
    UniformEquicontinuous
      (fun z : K => fun f : SchwartzNPoint d n =>
        A.distribution ⟨z.1, hK_domain z.2⟩ f) := by
  let T : K → SchwartzNPoint d n →L[ℝ] ℂ :=
    fun z =>
      (A.distribution ⟨z.1, hK_domain z.2⟩).restrictScalars ℝ
  have hT :
      ∀ f : SchwartzNPoint d n, ∃ C : ℝ,
        ∀ z : K, ‖T z f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := hA K hK_compact hK_domain f
    refine ⟨C, fun z => ?_⟩
    simpa [T, A.pairing_of_mem f z.1 (hK_domain z.2)] using
      hC z.1 z.2
  simpa [T] using
    (SchwartzMap.tempered_equicontinuous
      (E := NPointDomain d n) (F := ℂ) (G := ℂ) (T := T) hT)

/-- Convergent Schwartz tests converge uniformly after pairing on a compact
carrier subset. -/
theorem tendstoUniformlyOn_pairing_of_tendsto
    (A : P.SchwartzDistributionFamily)
    (hA : A.LocallyPointwiseBounded)
    {fN : ℕ → SchwartzNPoint d n}
    {f : SchwartzNPoint d n}
    (hfN : Tendsto fN atTop (nhds f))
    (K : Set (Fin k → osiiAxisPairIndex d → ℂ))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ osiiAxisPairMultiGapLogDomain d k) :
    TendstoUniformlyOn
      (fun q z => A.pairing (fN q) z)
      (A.pairing f) atTop K := by
  have hequi :=
    A.uniformEquicontinuous_distribution_on_compact
      hA K hK_compact hK_domain
  intro U hU
  have hpair :
      Tendsto (fun q => (f, fN q)) atTop
        (uniformity (SchwartzNPoint d n)) :=
    Uniform.tendsto_nhds_right.mp hfN
  filter_upwards [hpair (hequi U hU)] with q hq
  intro z hz
  simpa only [
    A.pairing_of_mem f z (hK_domain hz),
    A.pairing_of_mem (fN q) z (hK_domain hz)] using
    hq ⟨z, hz⟩

/-- The preceding convergence is locally uniform throughout the open
multi-gap carrier. -/
theorem tendstoLocallyUniformlyOn_pairing_of_tendsto
    (A : P.SchwartzDistributionFamily)
    (hA : A.LocallyPointwiseBounded)
    {fN : ℕ → SchwartzNPoint d n}
    {f : SchwartzNPoint d n}
    (hfN : Tendsto fN atTop (nhds f)) :
    TendstoLocallyUniformlyOn
      (fun q z => A.pairing (fN q) z)
      (A.pairing f) atTop
      (osiiAxisPairMultiGapLogDomain d k) := by
  rw [
    tendstoLocallyUniformlyOn_iff_forall_isCompact
      isOpen_osiiAxisPairMultiGapLogDomain]
  intro K hK_domain hK_compact
  exact A.tendstoUniformlyOn_pairing_of_tendsto
    hA hfN K hK_compact hK_domain

/-- Compact pointwise boundedness upgrades sourcewise product holomorphy to
weak holomorphy against every full Schwartz test. -/
theorem differentiableOn_pairing
    (A : P.SchwartzDistributionFamily)
    (hA : A.LocallyPointwiseBounded)
    (f : SchwartzNPoint d n) :
    DifferentiableOn ℂ (A.pairing f)
      (osiiAxisPairMultiGapLogDomain d k) := by
  let D : Set (SchwartzNPoint d n) :=
    {F | ∃ fs : Fin n → SchwartzSpacetime d,
      F = SchwartzMap.productTensor fs}
  let M : Submodule ℂ (SchwartzNPoint d n) := Submodule.span ℂ D
  have hf_closure : f ∈ closure (M : Set (SchwartzNPoint d n)) := by
    have hM : Dense (M : Set (SchwartzNPoint d n)) := by
      simpa [M, D] using productTensor_span_dense d n
    simpa [hM.closure_eq]
  obtain ⟨fN, hfN_mem, hfN⟩ :=
    mem_closure_iff_seq_limit.mp hf_closure
  have hlocally :=
    A.tendstoLocallyUniformlyOn_pairing_of_tendsto hA hfN
  let L :=
    nestedCoordinateCLE (d := d) (k := k)
  let V : Set ((Fin k × osiiAxisPairIndex d) → ℂ) :=
    L.symm ⁻¹' osiiAxisPairMultiGapLogDomain d k
  have hlocally_flat :
      TendstoLocallyUniformlyOn
        (fun q => A.pairing (fN q) ∘ L.symm)
        (A.pairing f ∘ L.symm) atTop V := by
    exact hlocally.comp L.symm (Set.mapsTo_preimage _ _)
      L.symm.continuous.continuousOn
  have hdiff_flat :
      DifferentiableOn ℂ (A.pairing f ∘ L.symm) V := by
    apply hlocally_flat.differentiableOn_finite
    · exact Filter.Eventually.of_forall fun q =>
        (A.differentiableOn_pairing_of_mem_productTensor_span
          (fN q) (by simpa [M, D] using hfN_mem q)).comp
            L.symm.differentiable.differentiableOn
            (Set.mapsTo_preimage _ _)
    · exact isOpen_osiiAxisPairMultiGapLogDomain.preimage
        L.symm.continuous
  have hcomp :=
    hdiff_flat.comp L.differentiable.differentiableOn
      (show Set.MapsTo L
        (osiiAxisPairMultiGapLogDomain d k) V by
          intro z hz
          simpa [V, L] using hz)
  simpa [Function.comp_apply, V, L] using hcomp

end SchwartzDistributionFamily

end OSIIAxisPairMultiGapSourcewiseMZFamily

namespace OSIIChronologicalCompactFactors

variable [NeZero k]

section OriginalOSSourceFamily

variable (F : OSIIChronologicalCompactFactors d k)
  (OS : OsterwalderSchraderAxioms d)
  (T : ℝ) (hT : 1 < T)
  (hordered :
    ∀ a : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            ((F.factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((F.factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)

/-- The growth-free sourcewise flat cross canonically supplies one full
Schwartz distribution at every point of its genuine logarithmic carrier. -/
noncomputable def schwartzDistributionFamilyAtSlopeOfOS :
    (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS T hT hordered).toMZFamily.SchwartzDistributionFamily :=
  (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
    OS T hT hordered).toMZFamily
      |>.schwartzDistributionFamilyOfExistsUnique
        (fun z =>
          F.existsUnique_schwartzDistributionAtOfOS
            OS T hT hordered z.1 z.2)

/-- The genuine original-OS distribution family recovers its sourcewise
holomorphic continuation on every pure Schwartz product tensor. -/
@[simp] theorem schwartzDistributionFamilyAtSlopeOfOS_productTensor
    (z : {z : Fin k → osiiAxisPairIndex d → ℂ //
      z ∈ osiiAxisPairMultiGapLogDomain d k})
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    (F.schwartzDistributionFamilyAtSlopeOfOS
      OS T hT hordered).distribution z
        (SchwartzMap.productTensor fs) =
      (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
        OS T hT hordered).toMZFamily.toFun fs z.1 :=
  (F.schwartzDistributionFamilyAtSlopeOfOS
    OS T hT hordered).productTensor z fs

end OriginalOSSourceFamily

end OSIIChronologicalCompactFactors

namespace OSIIChronologicalSourcewisePacketData

variable {OS : OsterwalderSchraderAxioms d}
  {lgc : OSLinearGrowthCondition d OS} [NeZero k]

/-- The existing chronological packet producer canonically supplies the
pointwise multi-gap full-Schwartz distribution family. -/
noncomputable def schwartzDistributionFamily
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc) :
    D.toSourcewiseCoshGrowthData.toMZFamily.SchwartzDistributionFamily :=
  D.toSourcewiseCoshGrowthData.toMZFamily
    |>.schwartzDistributionFamilyOfExistsUnique
      (fun z => D.existsUnique_schwartzDistributionAt z.1 z.2)

end OSIIChronologicalSourcewisePacketData

end OSReconstruction
