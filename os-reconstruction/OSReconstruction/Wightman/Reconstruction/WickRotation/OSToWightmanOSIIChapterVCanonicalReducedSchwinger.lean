/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced















noncomputable section

open Complex Filter MeasureTheory
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

/-- The normalized reduced-test lift is a right inverse to basepoint fiber
reduction. -/
theorem diffVarReduction_reducedTestLift
    (χ : BHW.NormalizedBasepointCutoff d)
    (φ : SchwartzNPoint d m) :
    diffVarReduction d m
        (BHW.reducedTestLift m d χ.toSchwartz φ) =
      φ := by
  ext ξ
  change
    (∫ a : SpacetimeDim d,
      BHW.reducedTestLift m d χ.toSchwartz φ
        (fun k μ => a μ + diffVarSection d m ξ k μ)) =
      φ ξ
  have hdiff :
      ∀ a : SpacetimeDim d,
        BHW.reducedDiffMapReal (m + 1) d
            (fun k μ => a μ + diffVarSection d m ξ k μ) =
          ξ := by
    exact fun a => reducedDiffMapReal_diffVarSection a ξ
  simp_rw [BHW.reducedTestLift_apply, hdiff]
  have hhead :
      ∀ a : SpacetimeDim d,
        (fun k μ => a μ + diffVarSection d m ξ k μ) 0 = a := by
    intro a
    ext μ
    simp
  simp_rw [hhead]
  calc
    (∫ a : SpacetimeDim d, χ.toSchwartz a * φ ξ) =
        ∫ a : SpacetimeDim d, φ ξ * χ.toSchwartz a := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with a
          exact mul_comm _ _
    _ = φ ξ * ∫ a : SpacetimeDim d, χ.toSchwartz a := by
          exact
            MeasureTheory.integral_const_mul
              (μ := (volume : Measure (SpacetimeDim d)))
              (φ ξ) (fun a : SpacetimeDim d => χ.toSchwartz a)
    _ = φ ξ := by rw [χ.integral_eq_one, mul_one]

/-- Canonical reduced Schwinger distribution for a positive difference-time
cutoff, obtained by testing the absolute cutoff functional on one normalized
basepoint lift. -/
noncomputable def canonicalReducedTimeCutoffSchwingerCLM
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m) :
    SchwartzNPoint d m →L[ℂ] ℂ :=
  (reducedTimeCutoffSchwingerCLM OS η hη).comp
    (BHW.reducedTestLift m d
      (BHW.normalizedCutoffOfBump d).toSchwartz)

/-- The canonical reduced cutoff distribution factors the absolute
translation-invariant cutoff Schwinger functional. -/
theorem canonicalReducedTimeCutoffSchwingerCLM_factors
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m)
    (f : SchwartzNPoint d (m + 1)) :
    reducedTimeCutoffSchwingerCLM OS η hη f =
      canonicalReducedTimeCutoffSchwingerCLM OS η hη
        (diffVarReduction d m f) := by
  obtain ⟨W, hW⟩ :=
    exists_reducedTimeCutoffSchwingerCLM OS η hη
  let χ : BHW.NormalizedBasepointCutoff d :=
    BHW.normalizedCutoffOfBump d
  have hright :
      diffVarReduction d m
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f)) =
        diffVarReduction d m f :=
    diffVarReduction_reducedTestLift χ _
  calc
    reducedTimeCutoffSchwingerCLM OS η hη f =
        W (diffVarReduction d m f) := hW f
    _ =
        W (diffVarReduction d m
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f))) := by rw [hright]
    _ =
        reducedTimeCutoffSchwingerCLM OS η hη
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f)) := (hW _).symm
    _ =
        canonicalReducedTimeCutoffSchwingerCLM OS η hη
          (diffVarReduction d m f) := rfl

/-- If the reduced-time cutoff fixes a full source, then the canonical
reduced distribution recovers its Schwinger value after basepoint
reduction. -/
theorem
    canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m)
    (f : SchwartzNPoint d (m + 1))
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hcutoff :
      SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) η) f =
        f) :
    canonicalReducedTimeCutoffSchwingerCLM OS η hη
        (diffVarReduction d m f) =
      OS.S (m + 1) ⟨f, hf⟩ := by
  rw [← canonicalReducedTimeCutoffSchwingerCLM_factors OS η hη f]
  have hz :
      reducedTimeCutoffZeroCLM η hη f =
        (⟨f, hf⟩ : ZeroDiagonalSchwartz d (m + 1)) := by
    apply SetCoe.ext
    exact hcutoff
  change
    OS.S (m + 1) (reducedTimeCutoffZeroCLM η hη f) =
      OS.S (m + 1) ⟨f, hf⟩
  rw [hz]

/-- Canonical displacement-germ data selected from an explicit compact
reduced-time carrier, with the cutoff support retained inside a prescribed
open region. -/
theorem
    exists_canonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ_of_compactCarrier_subset_open
    {ι : Type*} {p : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (φ : ι → SchwartzNPoint d (m + 1))
    (K : Set (Fin m → ℝ))
    (hK_comp : IsCompact K)
    (hφK :
      ∀ i x, x ∈ tsupport
          (φ i : NPointDomain d (m + 1) → ℂ) →
        reducedTimeProjectionCLM d m x ∈ K)
    (O : Set (Fin m → ℝ))
    (hO_open : IsOpen O)
    (hO_positive :
      O ⊆ section43TimeStrictPositiveRegion m)
    (hKO : K ⊆ O)
    (A : (Fin p → ℝ) → NPointDomain d (m + 1))
    (hA : Continuous A)
    (hA_zero : A 0 = 0) :
    ∃ (η : SchwartzMap (Fin m → ℝ) ℂ)
      (hη :
        tsupport (η : (Fin m → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion m)
      (_hη_region :
        tsupport (η : (Fin m → ℝ) → ℂ) ⊆ O)
      (_hη_comp :
        HasCompactSupport (η : (Fin m → ℝ) → ℂ))
      (U : Set (Fin p → ℝ)),
      U ∈ 𝓝 0 ∧
        ∀ i u, u ∈ U →
          SchwartzMap.smulLeftCLM ℂ
              (section43NPointTimeCutoffWeight d m η)
              (diffVarReduction d m
                (translateSchwartzConfiguration (A u) (φ i))) =
              diffVarReduction d m
                (translateSchwartzConfiguration (A u) (φ i)) ∧
            canonicalReducedTimeCutoffSchwingerCLM OS η hη
                (diffVarReduction d m
                  (translateSchwartzConfiguration (A u) (φ i))) =
              OS.S (m + 1)
                (ZeroDiagonalSchwartz.ofClassical
                  (translateSchwartzConfiguration (A u) (φ i))) ∧
            ∀ x ∈ tsupport
                ((translateSchwartzConfiguration (A u) (φ i) :
                  SchwartzNPoint d (m + 1)) :
                NPointDomain d (m + 1) → ℂ),
              reducedTimeCutoffWeight (d := d) η x = 1 := by
  obtain ⟨η, hη_region, hη_comp, U, hU, hone⟩ :=
    exists_reducedTimeCutoff_family_displacement_germ_of_compactCarrier_subset_open
      φ K hK_comp hφK O hO_open hKO A hA hA_zero
  have hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m :=
    hη_region.trans hO_positive
  refine ⟨η, hη, hη_region, hη_comp, U, hU, ?_⟩
  intro i u hu
  let ψ : SchwartzNPoint d (m + 1) :=
    translateSchwartzConfiguration (A u) (φ i)
  have honeψ :
      ∀ x ∈ tsupport (ψ : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) η x = 1 := by
    intro x hx
    exact hone i u hu x hx
  have hψ_disj :
      Disjoint
        (tsupport (ψ : NPointDomain d (m + 1) → ℂ))
        (CoincidenceLocus d (m + 1)) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    have hweight : reducedTimeCutoffWeight (d := d) η x = 1 :=
      honeψ x hx
    have hxweight :
        x ∈ tsupport (reducedTimeCutoffWeight (d := d) η) :=
      subset_closure (by
        simp only [Function.mem_support]
        rw [hweight]
        exact one_ne_zero)
    exact
      Set.disjoint_left.mp
        (reducedTimeCutoffWeight_tsupport_disjoint η hη)
        hxweight hcoin
  have hψ_zero : VanishesToInfiniteOrderOnCoincidence ψ :=
    VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      ψ hψ_disj
  refine ⟨?_, ?_, honeψ⟩
  · exact
      reducedTimeCutoff_smul_diffVarReduction_eq_of_one_on_tsupport
        η ψ honeψ
  · rw [← canonicalReducedTimeCutoffSchwingerCLM_factors OS η hη ψ]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes ψ hψ_zero]
    exact
      reducedTimeCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
        OS η hη ψ hψ_zero honeψ

/-- Unit-bounded form of the canonical reduced Schwinger displacement germ.
The selected cutoff has zeroth Schwartz seminorm at most one, uniformly in
the compact carrier and prescribed open support region. -/
theorem
    exists_unitBoundedCanonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ_of_compactCarrier_subset_open
    {ι : Type*} {p : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (φ : ι → SchwartzNPoint d (m + 1))
    (K : Set (Fin m → ℝ))
    (hK_comp : IsCompact K)
    (hφK :
      ∀ i x, x ∈ tsupport
          (φ i : NPointDomain d (m + 1) → ℂ) →
        reducedTimeProjectionCLM d m x ∈ K)
    (O : Set (Fin m → ℝ))
    (hO_open : IsOpen O)
    (hO_positive :
      O ⊆ section43TimeStrictPositiveRegion m)
    (hKO : K ⊆ O)
    (A : (Fin p → ℝ) → NPointDomain d (m + 1))
    (hA : Continuous A)
    (hA_zero : A 0 = 0) :
    ∃ (η : SchwartzMap (Fin m → ℝ) ℂ)
      (hη :
        tsupport (η : (Fin m → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion m)
      (_hη_region :
        tsupport (η : (Fin m → ℝ) → ℂ) ⊆ O)
      (_hη_comp :
        HasCompactSupport (η : (Fin m → ℝ) → ℂ))
      (_hη_bound : SchwartzMap.seminorm ℂ 0 0 η ≤ 1)
      (U : Set (Fin p → ℝ)),
      U ∈ 𝓝 0 ∧
        ∀ i u, u ∈ U →
          SchwartzMap.smulLeftCLM ℂ
              (section43NPointTimeCutoffWeight d m η)
              (diffVarReduction d m
                (translateSchwartzConfiguration (A u) (φ i))) =
              diffVarReduction d m
                (translateSchwartzConfiguration (A u) (φ i)) ∧
            canonicalReducedTimeCutoffSchwingerCLM OS η hη
                (diffVarReduction d m
                  (translateSchwartzConfiguration (A u) (φ i))) =
              OS.S (m + 1)
                (ZeroDiagonalSchwartz.ofClassical
                  (translateSchwartzConfiguration (A u) (φ i))) ∧
            ∀ x ∈ tsupport
                ((translateSchwartzConfiguration (A u) (φ i) :
                  SchwartzNPoint d (m + 1)) :
                NPointDomain d (m + 1) → ℂ),
              reducedTimeCutoffWeight (d := d) η x = 1 := by
  obtain ⟨G⟩ :=
    nonempty_unitBoundedReducedTimeCutoffFamilyDisplacementGermData_of_compactCarrier_subset_open
      φ K hK_comp hφK O hO_open hKO A hA hA_zero
  have hη :
      tsupport (G.η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m :=
    G.η_support_region.trans hO_positive
  refine ⟨G.η, hη, G.η_support_region, G.η_compact,
    G.η_seminorm_zero_le_one, G.neighborhood, G.neighborhood_mem, ?_⟩
  intro i u hu
  let ψ : SchwartzNPoint d (m + 1) :=
    translateSchwartzConfiguration (A u) (φ i)
  have honeψ :
      ∀ x ∈ tsupport (ψ : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) G.η x = 1 := by
    intro x hx
    exact G.cutoff_one i u hu x hx
  have hψ_disj :
      Disjoint
        (tsupport (ψ : NPointDomain d (m + 1) → ℂ))
        (CoincidenceLocus d (m + 1)) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    have hweight : reducedTimeCutoffWeight (d := d) G.η x = 1 :=
      honeψ x hx
    have hxweight :
        x ∈ tsupport (reducedTimeCutoffWeight (d := d) G.η) :=
      subset_closure (by
        simp only [Function.mem_support]
        rw [hweight]
        exact one_ne_zero)
    exact
      Set.disjoint_left.mp
        (reducedTimeCutoffWeight_tsupport_disjoint G.η hη)
        hxweight hcoin
  have hψ_zero : VanishesToInfiniteOrderOnCoincidence ψ :=
    VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      ψ hψ_disj
  refine ⟨?_, ?_, honeψ⟩
  · exact
      reducedTimeCutoff_smul_diffVarReduction_eq_of_one_on_tsupport
        G.η ψ honeψ
  · rw [← canonicalReducedTimeCutoffSchwingerCLM_factors
      OS G.η hη ψ]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes ψ hψ_zero]
    exact
      reducedTimeCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
        OS G.η hη ψ hψ_zero honeψ

/-- Canonical form of the uniformly supported displacement-germ
construction.  The reduced distribution is no longer an opaque existential
choice. -/
theorem
    exists_canonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ
    {ι : Type*} {p : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (φ : ι → SchwartzNPoint d (m + 1))
    (hφ : HasUniformCompactStrictPositiveReducedTimeSupport φ)
    (A : (Fin p → ℝ) → NPointDomain d (m + 1))
    (hA : Continuous A)
    (hA_zero : A 0 = 0) :
    ∃ (η : SchwartzMap (Fin m → ℝ) ℂ)
      (hη :
        tsupport (η : (Fin m → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion m)
      (_hη_comp :
        HasCompactSupport (η : (Fin m → ℝ) → ℂ))
      (U : Set (Fin p → ℝ)),
      U ∈ 𝓝 0 ∧
        ∀ i u, u ∈ U →
          SchwartzMap.smulLeftCLM ℂ
              (section43NPointTimeCutoffWeight d m η)
              (diffVarReduction d m
                (translateSchwartzConfiguration (A u) (φ i))) =
              diffVarReduction d m
                (translateSchwartzConfiguration (A u) (φ i)) ∧
            canonicalReducedTimeCutoffSchwingerCLM OS η hη
                (diffVarReduction d m
                  (translateSchwartzConfiguration (A u) (φ i))) =
              OS.S (m + 1)
                (ZeroDiagonalSchwartz.ofClassical
                  (translateSchwartzConfiguration (A u) (φ i))) ∧
            ∀ x ∈ tsupport
                ((translateSchwartzConfiguration (A u) (φ i) :
                  SchwartzNPoint d (m + 1)) :
                  NPointDomain d (m + 1) → ℂ),
              reducedTimeCutoffWeight (d := d) η x = 1 := by
  obtain ⟨K, hK_comp, hK_pos, hφK⟩ := hφ
  obtain ⟨η, hη, _hη_region, hη_comp, U, hU, hrecover⟩ :=
    exists_canonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ_of_compactCarrier_subset_open
      OS φ K hK_comp hφK
      (section43TimeStrictPositiveRegion m)
      (isOpen_section43TimeStrictPositiveRegion m)
      Set.Subset.rfl hK_pos A hA hA_zero
  exact ⟨η, hη, hη_comp, U, hU, hrecover⟩

end OSIIChapterV
end OSReconstruction
