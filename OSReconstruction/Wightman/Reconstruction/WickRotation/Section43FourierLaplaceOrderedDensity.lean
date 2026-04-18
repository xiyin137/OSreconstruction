import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceSpatialDensity
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

/-- Positive time-difference coordinates give ordered positive Euclidean
times after applying the inverse difference-coordinate map. -/
theorem section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
    (d n : ℕ) [NeZero d]
    {δ : NPointDomain d n}
    (hδ : ∀ i : Fin n, 0 < δ i 0) :
    (section43DiffCoordRealCLE d n).symm δ ∈
      OrderedPositiveTimeRegion d n := by
  intro i
  constructor
  · rw [section43DiffCoordRealCLE_symm_apply]
    rw [Finset.sum_fin_eq_sum_range]
    have hnonempty : (Finset.range (i.val + 1)).Nonempty := by
      exact ⟨0, by simp⟩
    refine Finset.sum_pos ?_ hnonempty
    intro r hr
    have hrlt : r < i.val + 1 := Finset.mem_range.mp hr
    simpa [hrlt] using hδ ⟨r, by
        have hr' := Finset.mem_range.mp hr
        omega⟩
  · intro j hij
    rw [section43DiffCoordRealCLE_symm_apply,
      section43DiffCoordRealCLE_symm_apply]
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
    have hijv : i.val < j.val := by exact hij
    have hle : i.val + 1 ≤ j.val + 1 := Nat.succ_le_succ hijv.le
    let fj : ℕ → ℝ := fun r =>
      if h : r < j.val + 1 then
        δ ⟨(⟨r, h⟩ : Fin (j.val + 1)).val, by
          have hj := j.isLt
          omega⟩ 0
      else 0
    have hblock_nonempty :
        (Finset.Ico (i.val + 1) (j.val + 1)).Nonempty := by
      refine ⟨i.val + 1, ?_⟩
      exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.succ_lt_succ hijv⟩
    have hleft :
        (∑ r ∈ Finset.range (i.val + 1),
          if h : r < i.val + 1 then
            δ ⟨(⟨r, h⟩ : Fin (i.val + 1)).val, by
              have hi := i.isLt
              omega⟩ 0
          else 0) =
        (∑ r ∈ Finset.range (i.val + 1), fj r) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      have hri : r < i.val + 1 := Finset.mem_range.mp hr
      have hrj : r < j.val + 1 := lt_of_lt_of_le hri hle
      have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
      rw [dif_pos hri]
      simp [fj, hrjle]
    have hblock_pos :
        0 < ∑ r ∈ Finset.Ico (i.val + 1) (j.val + 1), fj r := by
      refine Finset.sum_pos ?_ hblock_nonempty
      intro r hr
      have hrj : r < j.val + 1 := (Finset.mem_Ico.mp hr).2
      have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
      simpa [fj, hrjle] using hδ ⟨r, by
        have hj := j.isLt
        omega⟩
    rw [hleft]
    change (∑ r ∈ Finset.range (i.val + 1), fj r) <
      ∑ r ∈ Finset.range (j.val + 1), fj r
    rw [← Finset.sum_range_add_sum_Ico fj hle]
    exact lt_add_of_pos_right _ hblock_pos

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

end OSReconstruction
