/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceClosure









noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction BigOperators
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Push a compact strict-positive source in difference coordinates back to an
ordered compact Euclidean source. -/
noncomputable def section43OrderedSourceOfTimeSpatialSource
    (d n : ℕ) [NeZero d]
    (G : Section43CompactStrictPositiveTimeSpatialSource d n) :
    Section43CompactOrderedSource d n where
  f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43DiffCoordRealCLE d n) G.f
  ordered := by
    intro y hy
    have hpre :
        section43DiffCoordRealCLE d n y ∈
          tsupport (G.f : NPointDomain d n → ℂ) := by
      exact tsupport_comp_subset_preimage
        (G.f : NPointDomain d n → ℂ)
        (section43DiffCoordRealCLE d n).continuous hy
    have hpos : ∀ i : Fin n, 0 < (section43DiffCoordRealCLE d n y) i 0 :=
      G.positive hpre
    have hy_ordered :=
      section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
        d n (δ := section43DiffCoordRealCLE d n y) hpos
    simpa using hy_ordered
  compact := by
    let e := section43DiffCoordRealCLE d n
    change HasCompactSupport
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e G.f :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)
    have htsupport :
        tsupport
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e G.f :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) =
          e.toHomeomorph ⁻¹' tsupport (G.f : NPointDomain d n → ℂ) := by
      simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] using
        (tsupport_comp_eq_preimage
          (g := (G.f : NPointDomain d n → ℂ)) e.toHomeomorph)
    have hpre_eq :
        e.toHomeomorph ⁻¹' tsupport (G.f : NPointDomain d n → ℂ) =
          e.symm '' tsupport (G.f : NPointDomain d n → ℂ) := by
      ext y
      constructor
      · intro hy
        refine ⟨e y, hy, ?_⟩
        simp [e]
      · rintro ⟨δ, hδ, rfl⟩
        simpa [e] using hδ
    rw [HasCompactSupport, htsupport, hpre_eq]
    exact G.compact.isCompact.image e.symm.continuous

/-- Pulling back the ordered pushforward recovers the original
difference-coordinate source. -/
theorem section43DiffPullbackCLM_orderedSourceOfTimeSpatialSource
    (d n : ℕ) [NeZero d]
    (G : Section43CompactStrictPositiveTimeSpatialSource d n) :
    section43DiffPullbackCLM d n
      ⟨(section43OrderedSourceOfTimeSpatialSource d n G).f,
        (section43OrderedSourceOfTimeSpatialSource d n G).ordered⟩ =
      G.f := by
  ext δ
  rw [section43DiffPullbackCLM_apply]
  change
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43DiffCoordRealCLE d n) G.f)
        ((section43DiffCoordRealCLE d n).symm δ) =
    G.f δ
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- A time-Laplace / spatial-Fourier representative for a difference source is
an OS-I Fourier-Laplace representative for its ordered pushforward. -/
theorem section43FourierLaplaceRepresentative_of_timeSpatialRepresentative
    (d n : ℕ) [NeZero d]
    {G : Section43CompactStrictPositiveTimeSpatialSource d n}
    {Ψ : SchwartzNPoint d n}
    (hΨ : section43TimeLaplaceSpatialFourierRepresentative d n G Ψ) :
    section43FourierLaplaceRepresentative d n
      ⟨(section43OrderedSourceOfTimeSpatialSource d n G).f,
        (section43OrderedSourceOfTimeSpatialSource d n G).ordered⟩ Ψ := by
  intro q hq
  rw [hΨ q hq]
  rw [section43FourierLaplaceIntegral]
  congr with τ
  rw [section43DiffPullbackCLM_orderedSourceOfTimeSpatialSource]

/-- The Layer-3 representative target lies in the preimage of the genuine
compact ordered Fourier-Laplace transform component image. -/
theorem section43TimeLaplaceSpatialFourierTarget_subset_component_preimage
    (d n : ℕ) [NeZero d] :
    section43TimeLaplaceSpatialFourierTarget d n ⊆
      (section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
        Set.range (section43FourierLaplaceTransformComponentMap d n) := by
  intro Φ hΦ
  rcases hΦ with ⟨G, Ψ, hΨrep, hΦq⟩
  let src := section43OrderedSourceOfTimeSpatialSource d n G
  have hΨFL :
      section43FourierLaplaceRepresentative d n
        ⟨src.f, src.ordered⟩ Ψ := by
    simpa [src] using
      section43FourierLaplaceRepresentative_of_timeSpatialRepresentative
        d n hΨrep
  rcases
    section43FourierLaplaceTransformComponent_has_representative
      d n src.f src.ordered src.compact with
    ⟨Φc, hΦc_rep, hΦc_q⟩
  have hΨΦc :
      section43PositiveEnergyQuotientMap (d := d) n Ψ =
        section43PositiveEnergyQuotientMap (d := d) n Φc := by
    apply section43PositiveEnergyQuotientMap_eq_of_eqOn_region (d := d)
    intro q hq
    exact (hΨFL q hq).trans (hΦc_rep q hq).symm
  have hΦ_component :
      section43PositiveEnergyQuotientMap (d := d) n Φ =
        section43FourierLaplaceTransformComponent d n
          src.f src.ordered src.compact :=
    hΦq.trans (hΨΦc.trans hΦc_q)
  change
    section43PositiveEnergyQuotientMap (d := d) n Φ ∈
      Set.range (section43FourierLaplaceTransformComponentMap d n)
  refine ⟨src, ?_⟩
  simpa [section43FourierLaplaceTransformComponentMap, src] using hΦ_component.symm

/-- The compact ordered Fourier-Laplace transform component image has dense
ambient preimage under the positive-energy quotient map. -/
theorem dense_section43FourierLaplace_compact_ordered_preimage_raw
    (d n : ℕ) [NeZero d] :
    Dense
      ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
        Set.range (section43FourierLaplaceTransformComponentMap d n)) :=
  Dense.mono
    (section43TimeLaplaceSpatialFourierTarget_subset_component_preimage d n)
    (by
      simpa [section43TimeLaplaceSpatialFourierTarget] using
        dense_section43TimeLaplaceSpatialFourier_compact_preimage d n)

set_option backward.isDefEq.respectTransparency false in
/-- The existing explicit inverse also recovers the original spacetime test. -/
theorem section43FrequencyRepresentativeInv_left
    (d n : Nat) [NeZero d] (phi : SchwartzNPoint d n) :
    section43FrequencyRepresentativeInv d n (section43FrequencyRepresentative d n phi) = phi := by
  have hcomp :
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (section43CumulativeTailMomentumCLE d n)
          (section43FrequencyRepresentative d n phi) =
        physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) phi) := by
    ext p
    simp [section43FrequencyRepresentative]
  change unflattenSchwartzNPoint (physicsFourierFlatInvCLM _) = phi
  have h := congrArg (fun F => unflattenSchwartzNPoint (d := d)
    (physicsFourierFlatInvCLM F)) hcomp
  refine h.trans ?_
  calc
    _ = unflattenSchwartzNPoint (flattenSchwartzNPoint (d := d) phi) :=
      congrArg (unflattenSchwartzNPoint (d := d))
        (physicsFourierFlatInvCLM_left (flattenSchwartzNPoint (d := d) phi))
    _ = phi := by
      ext x
      simp

/-- Compact Euclidean transform classes have dense preimage in the actual
Minkowski test space, not only in the ambient frequency space. -/
theorem dense_section43FourierLaplace_compact_ordered_frequency_preimage
    (d n : Nat) [NeZero d] :
    Dense ((section43FrequencyProjection d n) ⁻¹'
      Set.range (section43FourierLaplaceTransformComponentMap d n)) := by
  have hsurj : Function.Surjective (section43FrequencyRepresentativeInv d n) :=
    fun phi => ⟨section43FrequencyRepresentative d n phi,
      section43FrequencyRepresentativeInv_left d n phi⟩
  have hdense := hsurj.denseRange.dense_image
    (section43FrequencyRepresentativeInv d n).continuous
    (dense_section43FourierLaplace_compact_ordered_preimage_raw d n)
  apply hdense.mono
  rintro _ ⟨Phi, hPhi, rfl⟩
  simpa only [Set.mem_preimage, section43FrequencyProjection,
    ContinuousLinearMap.comp_apply, section43FrequencyRepresentativeInv_right] using hPhi

end OSReconstruction
