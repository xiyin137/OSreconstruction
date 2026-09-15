/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSupportCore












open Complex Topology MeasureTheory Metric Set
open scoped Classical Manifold

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

/-- Compact-support refinement of the finite-dimensional cutoff selector used
by the reduced Chapter V construction. -/
theorem exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
    {K U : Set (Fin m → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ x ∈ K, χ x = 1) ∧
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ U ∧
      HasCompactSupport (χ : (Fin m → ℝ) → ℂ) := by
  classical
  rcases hK.isBounded.subset_closedBall (0 : Fin m → ℝ) with ⟨R, hKR⟩
  let B : ℝ := max R 0 + 1
  let Ubounded : Set (Fin m → ℝ) := U ∩ Metric.ball 0 B
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right R 0]
  have hUbounded_open : IsOpen Ubounded :=
    hU.inter Metric.isOpen_ball
  have hK_sub_Ubounded : K ⊆ Ubounded := by
    intro x hx
    refine ⟨hKU hx, ?_⟩
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
    have hxB : ‖x‖ < B := by
      dsimp [B]
      linarith [le_max_left R 0]
    simpa [Metric.mem_ball, dist_zero_right] using hxB
  rcases
    SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open
      hK hUbounded_open hK_sub_Ubounded with
    ⟨χ, hχ_one, hχ_support⟩
  refine ⟨χ, hχ_one, ?_, ?_⟩
  · intro x hx
    exact (hχ_support hx).1
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Fin m → ℝ) B) ?_
    intro x hx
    have hxUbounded :
        x ∈ Ubounded :=
      hχ_support (subset_tsupport (χ : (Fin m → ℝ) → ℂ) hx)
    exact Metric.ball_subset_closedBall hxUbounded.2

/-- Quantitative refinement of
`exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open`.  The cutoff
is selected from Mathlib's unit-interval-valued smooth bump, so its zeroth
Schwartz seminorm is at most one independently of the compact set and open
neighborhood. -/
theorem exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open_seminorm_le_one
    {K U : Set (Fin m → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ x ∈ K, χ x = 1) ∧
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ U ∧
      HasCompactSupport (χ : (Fin m → ℝ) → ℂ) ∧
      SchwartzMap.seminorm ℂ 0 0 χ ≤ 1 := by
  classical
  rcases hK.isBounded.subset_closedBall (0 : Fin m → ℝ) with ⟨R, hKR⟩
  let B : ℝ := max R 0 + 1
  let Ubounded : Set (Fin m → ℝ) := U ∩ Metric.ball 0 B
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right R 0]
  have hUbounded_open : IsOpen Ubounded :=
    hU.inter Metric.isOpen_ball
  have hK_sub_Ubounded : K ⊆ Ubounded := by
    intro x hx
    refine ⟨hKU hx, ?_⟩
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
    have hxB : ‖x‖ < B := by
      dsimp [B]
      linarith [le_max_left R 0]
    simpa [Metric.mem_ball, dist_zero_right] using hxB
  obtain ⟨r, hrpos, hrsub⟩ :=
    hK.exists_cthickening_subset_open hUbounded_open hK_sub_Ubounded
  let r₂ : ℝ := r / 2
  have hr₂pos : 0 < r₂ := half_pos hrpos
  have hr₂le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let r₁ : ℝ := r₂ / 2
  have hr₁pos : 0 < r₁ := half_pos hr₂pos
  have hr₁lt₂ : r₁ < r₂ := half_lt_self hr₂pos
  let V₁ : Set (Fin m → ℝ) := Metric.thickening r₁ K
  let V₂ : Set (Fin m → ℝ) := Metric.thickening r₂ K
  have hK_sub_V₁ : K ⊆ V₁ := self_subset_thickening hr₁pos K
  have hclV₁_sub_V₂ : closure V₁ ⊆ V₂ := by
    exact (closure_thickening_subset_cthickening r₁ K).trans
      (cthickening_subset_thickening' hr₂pos hr₁lt₂ K)
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, Fin m → ℝ)) (n := (⊤ : ℕ∞))
      isOpen_thickening isClosed_closure hclV₁_sub_V₂
  have hχ_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ := hχsmooth.contDiff
  have hχ_tsupport_cthickening :
      tsupport χ ⊆ Metric.cthickening r₂ K := by
    rw [tsupport, hχsupport]
    exact closure_thickening_subset_cthickening r₂ K
  have hχ_compact : HasCompactSupport χ := by
    exact IsCompact.of_isClosed_subset (hK.cthickening)
      (isClosed_tsupport χ) hχ_tsupport_cthickening
  have hχ_tsupport_Ubounded : tsupport χ ⊆ Ubounded := by
    exact hχ_tsupport_cthickening.trans
      ((cthickening_mono hr₂le K).trans hrsub)
  let f : (Fin m → ℝ) → ℂ := fun x ↦ (χ x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp hχ_contDiff
  have hf_compact : HasCompactSupport f :=
    hχ_compact.comp_left Complex.ofReal_zero
  let χS : SchwartzMap (Fin m → ℝ) ℂ :=
    hf_compact.toSchwartzMap hf_smooth
  have hχS_apply : ∀ x, χS x = f x :=
    HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth
  refine ⟨χS, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hχS_apply]
    have hχx : χ x = 1 :=
      (hχone x).1 (subset_closure (hK_sub_V₁ hx))
    simp [f, hχx]
  · intro x hx
    have hxf : x ∈ tsupport f := by
      have hχS_fun : (χS : (Fin m → ℝ) → ℂ) = f :=
        funext hχS_apply
      rw [hχS_fun] at hx
      exact hx
    have hsupport : Function.support f = Function.support χ := by
      ext y
      simp [Function.mem_support, f]
    have htsupport : tsupport f = tsupport χ := by
      simp only [tsupport, hsupport]
    rw [htsupport] at hxf
    exact (hχ_tsupport_Ubounded hxf).1
  · exact hf_compact
  · refine SchwartzMap.seminorm_le_bound ℂ 0 0 χS (by positivity) ?_
    intro x
    have hχx := hχrange ⟨x, rfl⟩
    simp only [pow_zero, one_mul]
    rw [norm_iteratedFDeriv_zero, hχS_apply]
    simpa [f, Real.norm_eq_abs, abs_of_nonneg hχx.1] using hχx.2

/-- Pull a cutoff in consecutive difference times back to an absolute
configuration. This multiplier is constant along common translation orbits. -/
noncomputable def reducedTimeCutoffWeight
    (η : SchwartzMap (Fin m → ℝ) ℂ) :
    NPointDomain d (m + 1) → ℂ :=
  fun x =>
    η (section43QTime (d := d) (n := m)
      (BHW.reducedDiffMapReal (m + 1) d x))

theorem reducedTimeCutoffWeight_hasTemperateGrowth
    (η : SchwartzMap (Fin m → ℝ) ℂ) :
    Function.HasTemperateGrowth
      (reducedTimeCutoffWeight (d := d) η) := by
  change Function.HasTemperateGrowth
    ((η : (Fin m → ℝ) → ℂ) ∘ reducedTimeProjectionCLM d m)
  exact η.hasTemperateGrowth.comp
    (reducedTimeProjectionCLM d m).hasTemperateGrowth

/-- Multiplication by a cutoff in consecutive time differences commutes
exactly with basepoint fiber reduction. -/
theorem diffVarReduction_smul_reducedTimeCutoffWeight
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzNPoint d (m + 1)) :
    diffVarReduction d m
        (SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) η) f) =
      SchwartzMap.smulLeftCLM ℂ
        (section43NPointTimeCutoffWeight d m η)
        (diffVarReduction d m f) := by
  ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (section43NPointTimeCutoffWeight_hasTemperateGrowth d m η)]
  change
    (∫ a : SpacetimeDim d,
      (SchwartzMap.smulLeftCLM ℂ
        (reducedTimeCutoffWeight (d := d) η) f)
          (fun k μ => a μ + diffVarSection d m ξ k μ)) =
      section43NPointTimeCutoffWeight d m η ξ *
        ∫ a : SpacetimeDim d,
          f (fun k μ => a μ + diffVarSection d m ξ k μ)
  simp_rw [SchwartzMap.smulLeftCLM_apply_apply
    (reducedTimeCutoffWeight_hasTemperateGrowth η)]
  have hweight :
      ∀ a : SpacetimeDim d,
        reducedTimeCutoffWeight (d := d) η
            (fun k μ => a μ + diffVarSection d m ξ k μ) =
          section43NPointTimeCutoffWeight d m η ξ := by
    intro a
    simp only [reducedTimeCutoffWeight,
      section43NPointTimeCutoffWeight]
    rw [reducedDiffMapReal_diffVarSection]
  simp_rw [hweight]
  exact MeasureTheory.integral_const_mul _ _

/-- If the absolute-coordinate cutoff is one on a source support, its full
multiplier acts as the identity. -/
theorem reducedTimeCutoff_smul_eq_of_one_on_tsupport
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzNPoint d (m + 1))
    (hone :
      ∀ x ∈ tsupport (f : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) η x = 1) :
    SchwartzMap.smulLeftCLM ℂ
        (reducedTimeCutoffWeight (d := d) η) f =
      f := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (reducedTimeCutoffWeight_hasTemperateGrowth η)]
  by_cases hx : x ∈ tsupport
      (f : NPointDomain d (m + 1) → ℂ)
  · simp [hone x hx]
  · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hfx]

/-- If the absolute-coordinate cutoff is one on a source support, its reduced
time multiplier acts as the identity after fiber reduction. -/
theorem reducedTimeCutoff_smul_diffVarReduction_eq_of_one_on_tsupport
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzNPoint d (m + 1))
    (hone :
      ∀ x ∈ tsupport (f : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) η x = 1) :
    SchwartzMap.smulLeftCLM ℂ
        (section43NPointTimeCutoffWeight d m η)
        (diffVarReduction d m f) =
      diffVarReduction d m f := by
  have hfull :
      SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) η) f =
        f :=
    reducedTimeCutoff_smul_eq_of_one_on_tsupport η f hone
  rw [← diffVarReduction_smul_reducedTimeCutoffWeight, hfull]

/-- A family of sources has uniform compact strict-positive reduced-time
support when one compact carrier works for every member. This is the
uniformity needed before summing an infinite spatial Hermite family. -/
def HasUniformCompactStrictPositiveReducedTimeSupport
    {ι : Type*}
    (φ : ι → SchwartzNPoint d (m + 1)) : Prop :=
  ∃ K : Set (Fin m → ℝ),
    IsCompact K ∧
      K ⊆ section43TimeStrictPositiveRegion m ∧
      ∀ i x, x ∈ tsupport (φ i : NPointDomain d (m + 1) → ℂ) →
        reducedTimeProjectionCLM d m x ∈ K

/-- Two uniformly supported source families may be combined without changing
the reduced-time support contract. -/
theorem HasUniformCompactStrictPositiveReducedTimeSupport.sum
    {ι κ : Type*}
    {φ : ι → SchwartzNPoint d (m + 1)}
    {ψ : κ → SchwartzNPoint d (m + 1)}
    (hφ : HasUniformCompactStrictPositiveReducedTimeSupport φ)
    (hψ : HasUniformCompactStrictPositiveReducedTimeSupport ψ) :
    HasUniformCompactStrictPositiveReducedTimeSupport
      (Sum.elim φ ψ) := by
  obtain ⟨Kφ, hKφ_compact, hKφ_positive, hφK⟩ := hφ
  obtain ⟨Kψ, hKψ_compact, hKψ_positive, hψK⟩ := hψ
  refine
    ⟨Kφ ∪ Kψ, hKφ_compact.union hKψ_compact,
      union_subset hKφ_positive hKψ_positive, ?_⟩
  intro a x hx
  cases a with
  | inl i =>
      exact Or.inl (hφK i x hx)
  | inr j =>
      exact Or.inr (hψK j x hx)

/-- The consecutive-gap projection is the tail of the full ordered
difference-time coordinate. -/
theorem reducedTimeProjectionCLM_eq_tail_section43QTime
    (x : NPointDomain d (m + 1)) :
    reducedTimeProjectionCLM d m x =
      Fin.tail
        (section43QTime (d := d) (n := m + 1)
          (section43DiffCoordRealCLE d (m + 1) x)) := by
  ext i
  change
    x i.succ 0 - x i.castSucc 0 =
      section43DiffCoordRealCLE d (m + 1) x i.succ 0
  rw [section43DiffCoordRealCLE_apply]
  have hpred :
      (⟨i.succ.val - 1, by omega⟩ : Fin (m + 1)) =
        i.castSucc := by
    apply Fin.ext
    simp
  rw [dif_neg (by simp), hpred]

/-- An explicitly chosen compact reduced-time carrier admits one cutoff
supported in any prescribed open neighborhood of that carrier. The cutoff
remains one on every member of the family under the same small continuous
displacement germ. -/
theorem
    exists_reducedTimeCutoff_family_displacement_germ_of_compactCarrier_subset_open
    {ι : Type*} {p : ℕ}
    (φ : ι → SchwartzNPoint d (m + 1))
    (K : Set (Fin m → ℝ))
    (hK_comp : IsCompact K)
    (hφK :
      ∀ i x, x ∈ tsupport
          (φ i : NPointDomain d (m + 1) → ℂ) →
        reducedTimeProjectionCLM d m x ∈ K)
    (O : Set (Fin m → ℝ))
    (hO_open : IsOpen O)
    (hKO : K ⊆ O)
    (A : (Fin p → ℝ) → NPointDomain d (m + 1))
    (hA : Continuous A)
    (hA_zero : A 0 = 0) :
    ∃ η : SchwartzMap (Fin m → ℝ) ℂ,
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆ O ∧
        HasCompactSupport (η : (Fin m → ℝ) → ℂ) ∧
        ∃ U ∈ 𝓝 (0 : Fin p → ℝ), ∀ i u, u ∈ U →
          ∀ x ∈ tsupport
              ((translateSchwartzConfiguration (A u) (φ i) :
                SchwartzNPoint d (m + 1)) :
                NPointDomain d (m + 1) → ℂ),
              reducedTimeCutoffWeight (d := d) η x = 1 := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hK_comp.exists_cthickening_subset_open
      hO_open hKO
  let r₂ : ℝ := r / 2
  have hr₂_pos : 0 < r₂ := half_pos hr_pos
  have hr₂_le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let K₂ : Set (Fin m → ℝ) := Metric.cthickening r₂ K
  have hK₂_comp : IsCompact K₂ := hK_comp.cthickening
  have hK₂O : K₂ ⊆ O :=
    (Metric.cthickening_mono hr₂_le K).trans hr_sub
  obtain ⟨η, hη_one, hηO, hη_comp⟩ :=
    exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
      hK₂_comp hO_open hK₂O
  let L := reducedTimeProjectionCLM d m
  have hLA : Continuous (fun u : Fin p → ℝ => L (A u)) :=
    L.continuous.comp hA
  have hLA_zero : L (A (0 : Fin p → ℝ)) = 0 := by
    rw [hA_zero]
    exact map_zero L
  have hball :
      Metric.ball (0 : Fin m → ℝ) r₂ ∈
        𝓝 (L (A (0 : Fin p → ℝ))) := by
    rw [hLA_zero]
    exact Metric.ball_mem_nhds 0 hr₂_pos
  let U : Set (Fin p → ℝ) :=
    (fun u => L (A u)) ⁻¹' Metric.ball 0 r₂
  have hU : U ∈ 𝓝 (0 : Fin p → ℝ) :=
    hLA.continuousAt hball
  refine ⟨η, hηO, hη_comp, U, hU, ?_⟩
  intro i u hu x hx
  have hx_source :
      x + A u ∈ tsupport
        (φ i : NPointDomain d (m + 1) → ℂ) := by
    rw [tsupport_translateSchwartzConfiguration_eq_preimage] at hx
    exact hx
  have hL_source : L (x + A u) ∈ K :=
    hφK i (x + A u) hx_source
  have hshift_lt : ‖L (A u)‖ < r₂ := by
    have hu' : L (A u) ∈ Metric.ball (0 : Fin m → ℝ) r₂ := hu
    simpa [Metric.mem_ball, dist_zero_right] using hu'
  have hLx_K₂ : L x ∈ K₂ := by
    apply Metric.mem_cthickening_of_dist_le
      (L x) (L (x + A u)) r₂ K hL_source
    rw [map_add, dist_eq_norm]
    simpa [norm_neg] using hshift_lt.le
  simpa [reducedTimeCutoffWeight, L] using hη_one (L x) hLx_K₂

/-- A compactly supported reduced-time cutoff, normalized in zeroth Schwartz
seminorm, which remains one on a complete source family under one common
small displacement germ. -/
structure UnitBoundedReducedTimeCutoffFamilyDisplacementGermData
    {ι : Type*} {p : ℕ}
    (φ : ι → SchwartzNPoint d (m + 1))
    (O : Set (Fin m → ℝ))
    (A : (Fin p → ℝ) → NPointDomain d (m + 1)) where
  η : SchwartzMap (Fin m → ℝ) ℂ
  η_support_region :
    tsupport (η : (Fin m → ℝ) → ℂ) ⊆ O
  η_compact : HasCompactSupport (η : (Fin m → ℝ) → ℂ)
  η_seminorm_zero_le_one : SchwartzMap.seminorm ℂ 0 0 η ≤ 1
  neighborhood : Set (Fin p → ℝ)
  neighborhood_mem : neighborhood ∈ 𝓝 (0 : Fin p → ℝ)
  cutoff_one : ∀ i u, u ∈ neighborhood →
    ∀ x ∈ tsupport
        ((translateSchwartzConfiguration (A u) (φ i) :
          SchwartzNPoint d (m + 1)) :
          NPointDomain d (m + 1) → ℂ),
      reducedTimeCutoffWeight (d := d) η x = 1

/-- Quantitative compact-carrier cutoff selection.  Unlike the qualitative
existential above, this package retains the chart-independent zeroth
seminorm bound needed by the normalized VI.2 envelope. -/
theorem
    nonempty_unitBoundedReducedTimeCutoffFamilyDisplacementGermData_of_compactCarrier_subset_open
    {ι : Type*} {p : ℕ}
    (φ : ι → SchwartzNPoint d (m + 1))
    (K : Set (Fin m → ℝ))
    (hK_comp : IsCompact K)
    (hφK :
      ∀ i x, x ∈ tsupport
          (φ i : NPointDomain d (m + 1) → ℂ) →
        reducedTimeProjectionCLM d m x ∈ K)
    (O : Set (Fin m → ℝ))
    (hO_open : IsOpen O)
    (hKO : K ⊆ O)
    (A : (Fin p → ℝ) → NPointDomain d (m + 1))
    (hA : Continuous A)
    (hA_zero : A 0 = 0) :
    Nonempty
      (UnitBoundedReducedTimeCutoffFamilyDisplacementGermData
        φ O A) := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hK_comp.exists_cthickening_subset_open hO_open hKO
  let r₂ : ℝ := r / 2
  have hr₂_pos : 0 < r₂ := half_pos hr_pos
  have hr₂_le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let K₂ : Set (Fin m → ℝ) := Metric.cthickening r₂ K
  have hK₂_comp : IsCompact K₂ := hK_comp.cthickening
  have hK₂O : K₂ ⊆ O :=
    (Metric.cthickening_mono hr₂_le K).trans hr_sub
  obtain ⟨η, hη_one, hηO, hη_comp, hη_bound⟩ :=
    exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open_seminorm_le_one
      hK₂_comp hO_open hK₂O
  let L := reducedTimeProjectionCLM d m
  have hLA : Continuous (fun u : Fin p → ℝ ↦ L (A u)) :=
    L.continuous.comp hA
  have hLA_zero : L (A (0 : Fin p → ℝ)) = 0 := by
    rw [hA_zero]
    exact map_zero L
  have hball :
      Metric.ball (0 : Fin m → ℝ) r₂ ∈
        𝓝 (L (A (0 : Fin p → ℝ))) := by
    rw [hLA_zero]
    exact Metric.ball_mem_nhds 0 hr₂_pos
  let U : Set (Fin p → ℝ) :=
    (fun u ↦ L (A u)) ⁻¹' Metric.ball 0 r₂
  have hU : U ∈ 𝓝 (0 : Fin p → ℝ) :=
    hLA.continuousAt hball
  refine ⟨{
    η := η
    η_support_region := hηO
    η_compact := hη_comp
    η_seminorm_zero_le_one := hη_bound
    neighborhood := U
    neighborhood_mem := hU
    cutoff_one := ?_ }⟩
  intro i u hu x hx
  have hx_source :
      x + A u ∈ tsupport
        (φ i : NPointDomain d (m + 1) → ℂ) := by
    rw [tsupport_translateSchwartzConfiguration_eq_preimage] at hx
    exact hx
  have hL_source : L (x + A u) ∈ K :=
    hφK i (x + A u) hx_source
  have hshift_lt : ‖L (A u)‖ < r₂ := by
    have hu' : L (A u) ∈ Metric.ball (0 : Fin m → ℝ) r₂ := hu
    simpa [Metric.mem_ball, dist_zero_right] using hu'
  have hLx_K₂ : L x ∈ K₂ := by
    apply Metric.mem_cthickening_of_dist_le
      (L x) (L (x + A u)) r₂ K hL_source
    rw [map_add, dist_eq_norm]
    simpa [norm_neg] using hshift_lt.le
  simpa [reducedTimeCutoffWeight, L] using hη_one (L x) hLx_K₂

/-- Strictly positive consecutive difference times force all absolute time
coordinates to be distinct, hence avoid the coincidence locus. -/
theorem reducedTimeCutoffWeight_tsupport_disjoint
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m) :
    Disjoint
      (tsupport (reducedTimeCutoffWeight (d := d) η))
      (CoincidenceLocus d (m + 1)) := by
  let L : NPointDomain d (m + 1) →L[ℝ] (Fin m → ℝ) :=
    (section43QTimeCLM d m).comp
      (BHW.reducedDiffMapRealCLM (m + 1) d)
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hweight :
      reducedTimeCutoffWeight (d := d) η =
        (η : (Fin m → ℝ) → ℂ) ∘ L := by
    funext y
    change η (section43QTime (d := d) (n := m)
      (BHW.reducedDiffMapReal (m + 1) d y)) = η (L y)
    congr 1
  have hL_support :
      L x ∈ tsupport (η : (Fin m → ℝ) → ℂ) := by
    rw [hweight] at hx
    exact tsupport_comp_subset_preimage
      (η : (Fin m → ℝ) → ℂ) L.continuous hx
  have hgap : ∀ i : Fin m, 0 < x i.succ 0 - x i.castSucc 0 := by
    intro i
    have hi := hη hL_support i
    have hi' :
        0 <
          BHW.reducedDiffMapReal (m + 1) d x
            ⟨i.val, by omega⟩ 0 := by
      simpa [L, section43QTimeCLM_apply,
        BHW.reducedDiffMapRealCLM, section43QTime,
        nPointTimeSpatialCLE] using hi
    change 0 < x i.succ 0 - x i.castSucc 0 at hi'
    exact hi'
  have htime : StrictMono (fun i : Fin (m + 1) => x i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact sub_pos.mp (hgap i)
  rcases hcoin with ⟨i, j, hij, hxeq⟩
  have htEq : x i 0 = x j 0 :=
    congrArg (fun y : SpacetimeDim d => y 0) hxeq
  exact hij (htime.injective htEq)

/-- Multiplication by a positive-difference cutoff sends every full Schwartz
test into the zero-diagonal Schwinger domain. -/
noncomputable def reducedTimeCutoffZeroCLM
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m) :
    SchwartzNPoint d (m + 1) →L[ℂ]
      ZeroDiagonalSchwartz d (m + 1) :=
  (SchwartzMap.smulLeftCLM ℂ
      (reducedTimeCutoffWeight (d := d) η)).codRestrict
    (zeroDiagonalSubmodule d (m + 1))
    (fun f => by
      apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      refine Set.disjoint_left.2 ?_
      intro x hx hcoin
      have hxweight :
          x ∈ tsupport (reducedTimeCutoffWeight (d := d) η) :=
        (SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := reducedTimeCutoffWeight (d := d) η)
          (f := f) hx).2
      exact
        Set.disjoint_left.mp
          (reducedTimeCutoffWeight_tsupport_disjoint η hη)
          hxweight hcoin)

@[simp] theorem reducedTimeCutoffZeroCLM_coe
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m)
    (f : SchwartzNPoint d (m + 1)) :
    (reducedTimeCutoffZeroCLM η hη f).1 =
      SchwartzMap.smulLeftCLM ℂ
        (reducedTimeCutoffWeight (d := d) η) f := rfl

/-- The full Schwartz functional obtained by applying the OS Schwinger
functional after the translation-invariant positive-difference cutoff. -/
noncomputable def reducedTimeCutoffSchwingerCLM
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m) :
    SchwartzNPoint d (m + 1) →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (m + 1)).comp
    (reducedTimeCutoffZeroCLM η hη)

theorem reducedTimeCutoffSchwingerCLM_translation_invariant
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m)
    (a : SpacetimeDim d)
    (f g : SchwartzNPoint d (m + 1))
    (hfg : ∀ x, g.toFun x = f.toFun (fun i => x i + a)) :
    reducedTimeCutoffSchwingerCLM OS η hη f =
      reducedTimeCutoffSchwingerCLM OS η hη g := by
  apply OS.E1_translation_invariant (m + 1) a
  intro x
  change
    (SchwartzMap.smulLeftCLM ℂ
      (reducedTimeCutoffWeight (d := d) η) g) x =
    (SchwartzMap.smulLeftCLM ℂ
      (reducedTimeCutoffWeight (d := d) η) f)
        (fun i => x i + a)
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (reducedTimeCutoffWeight_hasTemperateGrowth η),
    SchwartzMap.smulLeftCLM_apply_apply
      (reducedTimeCutoffWeight_hasTemperateGrowth η)]
  change
    reducedTimeCutoffWeight (d := d) η x * g x =
      reducedTimeCutoffWeight (d := d) η
        (fun i => x i + a) * f (fun i => x i + a)
  have hfgx : g x = f (fun i => x i + a) := hfg x
  rw [hfgx]
  congr 1
  simp only [reducedTimeCutoffWeight]
  congr 2
  symm
  exact
    BHW.reducedDiffMapReal_translate_uniform_eq
      (m + 1) d x a

/-- The translation-invariant cutoff Schwinger functional descends to a
tempered functional on consecutive difference variables. -/
theorem exists_reducedTimeCutoffSchwingerCLM
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m) :
    ∃ W : SchwartzNPoint d m →L[ℂ] ℂ,
      ∀ f : SchwartzNPoint d (m + 1),
        reducedTimeCutoffSchwingerCLM OS η hη f =
          W (diffVarReduction d m f) := by
  exact
    exists_diffVar_distribution_fixed d m
      (reducedTimeCutoffSchwingerCLM OS η hη).continuous
      (reducedTimeCutoffSchwingerCLM OS η hη).isLinear
      (reducedTimeCutoffSchwingerCLM_translation_invariant
        OS η hη)

/-- On a zero-diagonal source where the reduced cutoff equals one, the cutoff
functional is the original Schwinger value. -/
theorem reducedTimeCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m)
    (f : SchwartzNPoint d (m + 1))
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hone :
      ∀ x ∈ tsupport (f : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) η x = 1) :
    reducedTimeCutoffSchwingerCLM OS η hη f =
      OS.S (m + 1) ⟨f, hf⟩ := by
  have hz :
      reducedTimeCutoffZeroCLM η hη f =
        (⟨f, hf⟩ : ZeroDiagonalSchwartz d (m + 1)) := by
    apply SetCoe.ext
    ext x
    rw [reducedTimeCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (reducedTimeCutoffWeight_hasTemperateGrowth η)]
    by_cases hx : x ∈ tsupport
        (f : NPointDomain d (m + 1) → ℂ)
    · simp [smul_eq_mul, hone x hx]
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [smul_eq_mul, hfx]
  change
    OS.S (m + 1) (reducedTimeCutoffZeroCLM η hη f) =
      OS.S (m + 1) ⟨f, hf⟩
  rw [hz]

/-- A reduced tempered Schwinger functional exists and recovers every
zero-diagonal source on which the chosen positive-difference cutoff is one. -/
theorem exists_reducedTimeCutoffSchwingerCLM_recover
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m) :
    ∃ W : SchwartzNPoint d m →L[ℂ] ℂ,
      ∀ (f : SchwartzNPoint d (m + 1))
        (hf : VanishesToInfiniteOrderOnCoincidence f),
        (∀ x ∈ tsupport (f : NPointDomain d (m + 1) → ℂ),
          reducedTimeCutoffWeight (d := d) η x = 1) →
        W (diffVarReduction d m f) =
          OS.S (m + 1) ⟨f, hf⟩ := by
  obtain ⟨W, hW⟩ :=
    exists_reducedTimeCutoffSchwingerCLM OS η hη
  refine ⟨W, ?_⟩
  intro f hf hone
  rw [← hW f]
  exact
    reducedTimeCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
      OS η hη f hf hone

/-- Two zero-diagonal full sources with compact strict-positive reduced-time
support have the same Schwinger value whenever their difference-variable
reductions agree.  The common compact carrier supplies one reduced-time
cutoff, so translation invariance removes the arbitrary absolute basepoint
representative. -/
theorem schwinger_eq_of_diffVarReduction_eq
    (OS : OsterwalderSchraderAxioms d)
    (f g : SchwartzNPoint d (m + 1))
    (hf_support : HasCompactStrictPositiveReducedTimeSupport f)
    (hg_support : HasCompactStrictPositiveReducedTimeSupport g)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hg : VanishesToInfiniteOrderOnCoincidence g)
    (hred : diffVarReduction d m f = diffVarReduction d m g) :
    OS.S (m + 1) ⟨f, hf⟩ = OS.S (m + 1) ⟨g, hg⟩ := by
  obtain ⟨Kf, hKf_comp, hKf_pos, hfK⟩ := hf_support
  obtain ⟨Kg, hKg_comp, hKg_pos, hgK⟩ := hg_support
  obtain ⟨η, hη_one, hη_pos, _hη_comp⟩ :=
    exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
      (hKf_comp.union hKg_comp)
      (isOpen_section43TimeStrictPositiveRegion m)
      (Set.union_subset hKf_pos hKg_pos)
  obtain ⟨W, hW⟩ :=
    exists_reducedTimeCutoffSchwingerCLM_recover OS η hη_pos
  have hf_one :
      ∀ x ∈ tsupport (f : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) η x = 1 := by
    intro x hx
    simpa [reducedTimeCutoffWeight] using
      hη_one (reducedTimeProjectionCLM d m x) (Or.inl (hfK x hx))
  have hg_one :
      ∀ x ∈ tsupport (g : NPointDomain d (m + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) η x = 1 := by
    intro x hx
    simpa [reducedTimeCutoffWeight] using
      hη_one (reducedTimeProjectionCLM d m x) (Or.inr (hgK x hx))
  calc
    OS.S (m + 1) ⟨f, hf⟩ =
        W (diffVarReduction d m f) := (hW f hf hf_one).symm
    _ = W (diffVarReduction d m g) := by rw [hred]
    _ = OS.S (m + 1) ⟨g, hg⟩ := hW g hg hg_one

end OSIIChapterV
end OSReconstruction
