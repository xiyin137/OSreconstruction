import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceClosure

/-!
# Section 4.3 ordered-source density bridge

This downstream companion transports the compiled time-Laplace /
spatial-Fourier density packet from difference coordinates back to compact
ordered Euclidean sources.
-/

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

/-- Product one-sided Laplace time factors with a compact spatial Fourier
factor lie in the compact ordered Fourier-Laplace component preimage. -/
theorem section43NPointTimeSpatialTensor_productSource_mem_ordered_component_preimage
    (d n : ℕ) [NeZero d]
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ : χ ∈ section43SpatialFourierCompactRange d n) :
    section43NPointTimeSpatialTensor d n
      (section43TimeProductTensor
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
      χ ∈
        (section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
          Set.range (section43FourierLaplaceTransformComponentMap d n) := by
  exact
    section43TimeLaplaceSpatialFourierTarget_subset_component_preimage d n
      (section43NPointTimeSpatialTensor_productSource_mem_timeLaplaceSpatialFourierTarget
        d n gs χ hχ)

/-- Product one-sided Laplace time factors with a compact spatial Fourier
factor have a concrete compact ordered Fourier-Laplace representative. -/
theorem section43NPointTimeSpatialTensor_productSource_has_orderedFourierLaplaceRepresentative
    (d n : ℕ) [NeZero d]
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ : χ ∈ section43SpatialFourierCompactRange d n) :
    ∃ (src : Section43CompactOrderedSource d n)
      (Ψ : SchwartzNPoint d n),
      section43FourierLaplaceRepresentative d n
        ⟨src.f, src.ordered⟩ Ψ ∧
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
          χ) =
      section43PositiveEnergyQuotientMap (d := d) n Ψ := by
  rcases
    section43NPointTimeSpatialTensor_productSource_mem_timeLaplaceSpatialFourierTarget
      d n gs χ hχ with
    ⟨G, Ψ, hΨ, hq⟩
  let src : Section43CompactOrderedSource d n :=
    section43OrderedSourceOfTimeSpatialSource d n G
  refine ⟨src, Ψ, ?_, hq⟩
  simpa [src] using
    section43FourierLaplaceRepresentative_of_timeSpatialRepresentative
      d n hΨ

/-- Product one-sided Laplace time factors with a compact spatial Fourier
factor equal the transform component of a concrete compact ordered source in
the positive-energy quotient. -/
theorem section43NPointTimeSpatialTensor_productSource_eq_orderedTransformComponent
    (d n : ℕ) [NeZero d]
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ : χ ∈ section43SpatialFourierCompactRange d n) :
    ∃ (src : Section43CompactOrderedSource d n),
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
          χ) =
      section43FourierLaplaceTransformComponent d n
        src.f src.ordered src.compact := by
  rcases
    section43NPointTimeSpatialTensor_productSource_has_orderedFourierLaplaceRepresentative
      d n gs χ hχ with
    ⟨src, Ψ, hΨ, hq⟩
  refine ⟨src, hq.trans ?_⟩
  exact
    section43FourierLaplaceRepresentative_quotient_eq_transformComponent
      d n src.f src.ordered src.compact Ψ hΨ

/-- Product one-sided time factors and an explicit compact spatial source give
the transform component of the explicit ordered source obtained from their
time/spatial product source. -/
theorem section43NPointTimeSpatialTensor_productSource_eq_explicitOrderedTransformComponent
    (d n : ℕ) [NeZero d]
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (κ : Section43SpatialCompactSource d n) :
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
        (SchwartzMap.fourierTransformCLM ℂ κ.1)) =
      section43FourierLaplaceTransformComponent d n
        (section43OrderedSourceOfTimeSpatialSource d n
          (section43TimeSpatialProductSource d n
            (section43TimeProductSource gs) κ)).f
        (section43OrderedSourceOfTimeSpatialSource d n
          (section43TimeSpatialProductSource d n
            (section43TimeProductSource gs) κ)).ordered
        (section43OrderedSourceOfTimeSpatialSource d n
          (section43TimeSpatialProductSource d n
            (section43TimeProductSource gs) κ)).compact := by
  let g : Section43CompactStrictPositiveTimeSource n :=
    section43TimeProductSource gs
  let G : Section43CompactStrictPositiveTimeSpatialSource d n :=
    section43TimeSpatialProductSource d n g κ
  let src : Section43CompactOrderedSource d n :=
    section43OrderedSourceOfTimeSpatialSource d n G
  let Ψt : SchwartzMap (Fin n → ℝ) ℂ :=
    section43IteratedLaplaceSchwartzRepresentative n g
  let Ψ : SchwartzNPoint d n :=
    section43NPointTimeSpatialTensor d n Ψt
      (SchwartzMap.fourierTransformCLM ℂ κ.1)
  have hΨrep_time :
      section43IteratedLaplaceRepresentative n g Ψt := by
    intro σ hσ
    exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ
  have hcompact_Ψt :
      section43IteratedLaplaceCompactTransform n g =
        section43TimePositiveQuotientMap n Ψt :=
    section43IteratedLaplaceCompactTransform_eq_quotient n g Ψt hΨrep_time
  have htime_eq :
      section43TimePositiveQuotientMap n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
        section43TimePositiveQuotientMap n Ψt := by
    exact (section43IteratedLaplaceCompactTransform_productSource gs).symm.trans
      hcompact_Ψt
  have hq :
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
          (SchwartzMap.fourierTransformCLM ℂ κ.1)) =
        section43PositiveEnergyQuotientMap (d := d) n Ψ := by
    change section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
          (SchwartzMap.fourierTransformCLM ℂ κ.1)) =
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n Ψt
          (SchwartzMap.fourierTransformCLM ℂ κ.1))
    exact
      section43NPointTimeSpatialTensor_positiveEnergyQuotient_eq_of_timeQuotient_eq
        d n (SchwartzMap.fourierTransformCLM ℂ κ.1) htime_eq
  have hΨFL :
      section43FourierLaplaceRepresentative d n
        ⟨src.f, src.ordered⟩ Ψ := by
    simpa [src, G, g, Ψ] using
      section43FourierLaplaceRepresentative_of_timeSpatialRepresentative
        d n (section43TimeLaplaceSpatialFourierRepresentative_productSource
          d n g κ)
  calc
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
        (SchwartzMap.fourierTransformCLM ℂ κ.1))
        =
      section43PositiveEnergyQuotientMap (d := d) n Ψ := hq
    _ =
      section43FourierLaplaceTransformComponent d n src.f src.ordered src.compact :=
        section43FourierLaplaceRepresentative_quotient_eq_transformComponent
          d n src.f src.ordered src.compact Ψ hΨFL

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

end OSReconstruction
