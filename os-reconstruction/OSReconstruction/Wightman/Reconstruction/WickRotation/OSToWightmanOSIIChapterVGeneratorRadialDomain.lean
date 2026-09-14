/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates


















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- The union of all open convex subsets of `U` which contain the origin. -/
def openZeroConvexKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) : Set E :=
  {x | ∃ V : Set E,
    IsOpen V ∧ Convex ℝ V ∧ 0 ∈ V ∧ V ⊆ U ∧ x ∈ V}

theorem openZeroConvexKernel_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) :
    IsOpen (openZeroConvexKernel U) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨V, hV_open, hV_convex, h0V, hVU, hxV⟩
  exact Filter.mem_of_superset (hV_open.mem_nhds hxV) fun y hy =>
    ⟨V, hV_open, hV_convex, h0V, hVU, hy⟩

theorem openZeroConvexKernel_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) :
    openZeroConvexKernel U ⊆ U := by
  rintro x ⟨V, _hV_open, _hV_convex, _h0V, hVU, hxV⟩
  exact hVU hxV

/-- The zero-based open convex kernel preserves binary intersections.  A
common point has open convex witnesses through zero in each domain, whose
intersection is again such a witness. -/
theorem openZeroConvexKernel_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U V : Set E) :
    openZeroConvexKernel (U ∩ V) =
      openZeroConvexKernel U ∩ openZeroConvexKernel V := by
  apply Set.Subset.antisymm
  · rintro x ⟨W, hWOpen, hWConvex, hzeroW, hWUV, hxW⟩
    exact
      ⟨⟨W, hWOpen, hWConvex, hzeroW,
          fun y hy => (hWUV hy).1, hxW⟩,
        ⟨W, hWOpen, hWConvex, hzeroW,
          fun y hy => (hWUV hy).2, hxW⟩⟩
  · rintro x
      ⟨⟨W, hWOpen, hWConvex, hzeroW, hWU, hxW⟩,
        ⟨Z, hZOpen, hZConvex, hzeroZ, hZV, hxZ⟩⟩
    exact
      ⟨W ∩ Z, hWOpen.inter hZOpen, hWConvex.inter hZConvex,
        ⟨hzeroW, hzeroZ⟩,
        fun y hy => ⟨hWU hy.1, hZV hy.2⟩,
        ⟨hxW, hxZ⟩⟩

theorem zero_mem_openZeroConvexKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E}
    (hU_open : IsOpen U)
    (h0U : (0 : E) ∈ U) :
    (0 : E) ∈ openZeroConvexKernel U := by
  obtain ⟨r, hr, hball⟩ :=
    SCV.exists_metric_ball_subset_of_mem_open hU_open h0U
  exact
    ⟨Metric.ball 0 r, Metric.isOpen_ball, convex_ball 0 r,
      Metric.mem_ball_self hr, hball, Metric.mem_ball_self hr⟩

theorem openZeroConvexKernel_starConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) :
    StarConvex ℝ 0 (openZeroConvexKernel U) := by
  rw [starConvex_iff_segment_subset]
  intro x hx
  rcases hx with ⟨V, hV_open, hV_convex, h0V, hVU, hxV⟩
  intro y hy
  exact
    ⟨V, hV_open, hV_convex, h0V, hVU,
      hV_convex.segment_subset h0V hxV hy⟩

theorem real_smul_mem_openZeroConvexKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E}
    {x : E}
    (hx : x ∈ openZeroConvexKernel U)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    t • x ∈ openZeroConvexKernel U :=
  (openZeroConvexKernel_starConvex U).smul_mem hx ht0 ht1

/-- A point whose segment from zero stays in an open set belongs to its open
zero-convex kernel.  A small thickening of the compact segment supplies the
open convex witness. -/
theorem mem_openZeroConvexKernel_of_segment_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E}
    (hU_open : IsOpen U)
    {x : E}
    (hsegment : segment ℝ 0 x ⊆ U) :
    x ∈ openZeroConvexKernel U := by
  have hcompact : IsCompact (segment ℝ 0 x) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨r, hr, hthick⟩ :=
    hcompact.exists_thickening_subset_open hU_open hsegment
  refine
    ⟨Metric.thickening r (segment ℝ 0 x),
      Metric.isOpen_thickening,
      (convex_segment (0 : E) x).thickening r,
      ?_, hthick, ?_⟩
  · exact Metric.self_subset_thickening hr _ (left_mem_segment ℝ 0 x)
  · exact Metric.self_subset_thickening hr _ (right_mem_segment ℝ 0 x)

theorem convex_conjugateFieldDomain
    {m : ℕ}
    {U : Set (Fin m → ℂ)}
    (hU : Convex ℝ U) :
    Convex ℝ (conjugateFieldDomain U) := by
  intro x hx y hy a b ha hb hab
  change star (a • x + b • y) ∈ U
  simpa using hU hx hy ha hb hab

private theorem exists_pos_le_one_mem_of_isOpen_zero_mem
    {U : Set ℝ}
    (hU_open : IsOpen U)
    (h0U : (0 : ℝ) ∈ U) :
    ∃ t ∈ U, 0 < t ∧ t ≤ 1 := by
  obtain ⟨r, hr, hball⟩ :=
    SCV.exists_metric_ball_subset_of_mem_open hU_open h0U
  let t : ℝ := min (r / 2) (1 / 2)
  have ht : 0 < t :=
    lt_min (half_pos hr) (by norm_num)
  have htr : t < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨t, hball ?_, ht, ?_⟩
  · simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using htr
  · exact (min_le_right _ _).trans (by norm_num)

@[simp]
theorem generatorChronologicalParameterComplexCLE_real_smul
    {k : ℕ}
    (i : GeneratorIndex k)
    (t : ℝ)
    (z : OSIITimeGapSpace k) :
    generatorChronologicalParameterComplexCLE i (t • z) =
      t • generatorChronologicalParameterComplexCLE i z := by
  ext q
  by_cases hq : q < i.toGap
  · simp [generatorChronologicalParameterComplexCLE, hq]
  · simp [generatorChronologicalParameterComplexCLE, hq]

theorem convex_chronologicalGeneratorSemigroupDomain
    {k : ℕ}
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU : Convex ℝ U)
    (hV : Convex ℝ V) :
    Convex ℝ
      (generatorChronologicalParameterComplexCLE i ⁻¹'
        generatorSemigroupDomain i U V) := by
  have hnative :
      Convex ℝ (generatorSemigroupDomain i U V) :=
    convex_generatorSemigroupDomain i
      (convex_conjugateFieldDomain hU) hV
  exact
    hnative.linear_preimage
      ((generatorChronologicalParameterComplexCLE i).toContinuousLinearMap
        |>.restrictScalars ℝ).toLinearMap

namespace GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The open zero-convex core of a left block domain. -/
def radialLeftDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.n - 1) → ℂ) :=
  openZeroConvexKernel (E.leftDomain i)

/-- The open zero-convex core of a right block domain. -/
def radialRightDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    Set (Fin (i.m - 1) → ℂ) :=
  openZeroConvexKernel (E.rightDomain i)

/-- The split-native generator domain formed from the radial block cores. -/
def radialNativeDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  generatorSemigroupDomain i
    (E.radialLeftDomain i) (E.radialRightDomain i)

/-- The radial generator domain in common chronological coordinates. -/
def radialChronologicalDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  generatorChronologicalParameterComplexCLE i ⁻¹'
    E.radialNativeDomain i

theorem radialLeftDomain_open
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    IsOpen (E.radialLeftDomain i) :=
  openZeroConvexKernel_open _

theorem radialRightDomain_open
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    IsOpen (E.radialRightDomain i) :=
  openZeroConvexKernel_open _

theorem radialNativeDomain_open
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    IsOpen (E.radialNativeDomain i) :=
  isOpen_generatorSemigroupDomain i
    (E.radialLeftDomain_open i) (E.radialRightDomain_open i)

theorem radialChronologicalDomain_open
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    IsOpen (E.radialChronologicalDomain i) :=
  (E.radialNativeDomain_open i).preimage
    (generatorChronologicalParameterComplexCLE i).continuous

theorem radialLeftDomain_subset
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    E.radialLeftDomain i ⊆ E.leftDomain i :=
  openZeroConvexKernel_subset _

theorem radialRightDomain_subset
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    E.radialRightDomain i ⊆ E.rightDomain i :=
  openZeroConvexKernel_subset _

theorem radialNativeDomain_subset_domain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    E.radialNativeDomain i ⊆ E.domain i := by
  rintro z ⟨hbridge, hleft, hright⟩
  exact
    ⟨hbridge, E.radialLeftDomain_subset i hleft,
      E.radialRightDomain_subset i hright⟩

theorem radialChronologicalDomain_subset
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    E.radialChronologicalDomain i ⊆
      generatorChronologicalParameterComplexCLE i ⁻¹' E.domain i :=
  fun _ hz => E.radialNativeDomain_subset_domain i hz

theorem chronologicalWitnessDomain_subset_radialChronologicalDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U)
    (h0U : 0 ∈ U)
    (hU_subset : U ⊆ E.leftDomain i)
    (hV_open : IsOpen V)
    (hV_convex : Convex ℝ V)
    (h0V : 0 ∈ V)
    (hV_subset : V ⊆ E.rightDomain i) :
    generatorChronologicalParameterComplexCLE i ⁻¹'
        generatorSemigroupDomain i U V ⊆
      E.radialChronologicalDomain i := by
  rintro z ⟨hbridge, hleft, hright⟩
  refine ⟨hbridge, ?_, ?_⟩
  · change
      star
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i z)).2.1 ∈
        E.radialLeftDomain i
    change
      star
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i z)).2.1 ∈
        U at hleft
    exact
      ⟨U, hU_open, hU_convex, h0U, hU_subset, hleft⟩
  · exact
      ⟨V, hV_open, hV_convex, h0V, hV_subset, hright⟩

theorem zero_mem_radialLeftDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    (0 : Fin (i.n - 1) → ℂ) ∈ E.radialLeftDomain i :=
  zero_mem_openZeroConvexKernel
    (E.leftDomain_open i) (E.left_zero_mem_domain i)

theorem zero_mem_radialRightDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    (0 : Fin (i.m - 1) → ℂ) ∈ E.radialRightDomain i :=
  zero_mem_openZeroConvexKernel
    (E.rightDomain_open i) (E.right_zero_mem_domain i)

theorem real_smul_mem_radialChronologicalDomain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ E.radialChronologicalDomain i)
    {t : ℝ}
    (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    t • z ∈ E.radialChronologicalDomain i := by
  rcases hz with ⟨hbridge, hleft, hright⟩
  have hleft_eq :
      star
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i (t • z))).2.1 =
        t •
          star
            (i.splitCoordinatesCLM
              (generatorChronologicalParameterComplexCLE i z)).2.1 := by
    rw [generatorChronologicalParameterComplexCLE_real_smul]
    ext a
    simp
  have hright_eq :
      (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i (t • z))).2.2 =
        t •
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i z)).2.2 := by
    rw [generatorChronologicalParameterComplexCLE_real_smul]
    ext b
    simp
  refine ⟨?_, ?_, ?_⟩
  · change
      0 <
        ((i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i (t • z))).1).re
    rw [generatorChronologicalParameterComplexCLE_real_smul]
    simpa using mul_pos ht0 hbridge
  · have hscaled :=
      real_smul_mem_openZeroConvexKernel hleft ht0.le ht1
    change
      star
          (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i (t • z))).2.1 ∈
        E.radialLeftDomain i
    rw [hleft_eq]
    exact hscaled
  · have hscaled :=
      real_smul_mem_openZeroConvexKernel hright ht0.le ht1
    rw [hright_eq]
    exact hscaled

/-- Two radial chronological generator domains have path-connected overlap
as soon as they share one point. -/
theorem radialChronologicalDomain_inter_isPathConnected
    (E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i j : GeneratorIndex k)
    {c : OSIITimeGapSpace k}
    (hcE : c ∈ E.radialChronologicalDomain i)
    (hcF : c ∈ F.radialChronologicalDomain j) :
    IsPathConnected
      (E.radialChronologicalDomain i ∩
        F.radialChronologicalDomain j) := by
  refine ⟨c, ⟨hcE, hcF⟩, ?_⟩
  intro z hz
  rcases hz.1 with ⟨hzE_bridge, hzE_left, hzE_right⟩
  change
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i z)).2.1 ∈
      openZeroConvexKernel (E.leftDomain i) at hzE_left
  rcases hzE_left with
    ⟨UE_left, hUE_left_open, hUE_left_convex, h0UE_left,
      hUE_left_subset, hzUE_left⟩
  rcases hzE_right with
    ⟨UE_right, hUE_right_open, hUE_right_convex, h0UE_right,
      hUE_right_subset, hzUE_right⟩
  rcases hz.2 with ⟨hzF_bridge, hzF_left, hzF_right⟩
  change
    star
        (j.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE j z)).2.1 ∈
      openZeroConvexKernel (F.leftDomain j) at hzF_left
  rcases hzF_left with
    ⟨UF_left, hUF_left_open, hUF_left_convex, h0UF_left,
      hUF_left_subset, hzUF_left⟩
  rcases hzF_right with
    ⟨UF_right, hUF_right_open, hUF_right_convex, h0UF_right,
      hUF_right_subset, hzUF_right⟩
  let cE_left : Fin (i.n - 1) → ℂ :=
    star
      (i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i c)).2.1
  let cE_right : Fin (i.m - 1) → ℂ :=
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i c)).2.2
  let cF_left : Fin (j.n - 1) → ℂ :=
    star
      (j.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE j c)).2.1
  let cF_right : Fin (j.m - 1) → ℂ :=
    (j.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE j c)).2.2
  let T : Set ℝ :=
    (((fun t : ℝ => t • cE_left) ⁻¹' UE_left) ∩
      ((fun t : ℝ => t • cE_right) ⁻¹' UE_right)) ∩
    (((fun t : ℝ => t • cF_left) ⁻¹' UF_left) ∩
      ((fun t : ℝ => t • cF_right) ⁻¹' UF_right))
  have hT_open : IsOpen T := by
    exact
      ((hUE_left_open.preimage (by fun_prop)).inter
        (hUE_right_open.preimage (by fun_prop))).inter
        ((hUF_left_open.preimage (by fun_prop)).inter
          (hUF_right_open.preimage (by fun_prop)))
  have h0T : (0 : ℝ) ∈ T := by
    simp [T, h0UE_left, h0UE_right, h0UF_left, h0UF_right]
  obtain ⟨t, htT, ht0, ht1⟩ :=
    exists_pos_le_one_mem_of_isOpen_zero_mem hT_open h0T
  rcases htT with
    ⟨⟨htUE_left, htUE_right⟩, ⟨htUF_left, htUF_right⟩⟩
  have hcE' := hcE
  rcases hcE' with ⟨hcE_bridge, _hcE_left, _hcE_right⟩
  have hcF' := hcF
  rcases hcF' with ⟨hcF_bridge, _hcF_left, _hcF_right⟩
  let DE : Set (OSIITimeGapSpace k) :=
    generatorChronologicalParameterComplexCLE i ⁻¹'
      generatorSemigroupDomain i UE_left UE_right
  let DF : Set (OSIITimeGapSpace k) :=
    generatorChronologicalParameterComplexCLE j ⁻¹'
      generatorSemigroupDomain j UF_left UF_right
  have hDE_convex : Convex ℝ DE :=
    convex_chronologicalGeneratorSemigroupDomain i
      hUE_left_convex hUE_right_convex
  have hDF_convex : Convex ℝ DF :=
    convex_chronologicalGeneratorSemigroupDomain j
      hUF_left_convex hUF_right_convex
  have hDE_subset :
      DE ⊆ E.radialChronologicalDomain i :=
    E.chronologicalWitnessDomain_subset_radialChronologicalDomain i
      hUE_left_open hUE_left_convex h0UE_left hUE_left_subset
      hUE_right_open hUE_right_convex h0UE_right hUE_right_subset
  have hDF_subset :
      DF ⊆ F.radialChronologicalDomain j :=
    F.chronologicalWitnessDomain_subset_radialChronologicalDomain j
      hUF_left_open hUF_left_convex h0UF_left hUF_left_subset
      hUF_right_open hUF_right_convex h0UF_right hUF_right_subset
  have hzDE : z ∈ DE :=
    ⟨hzE_bridge, hzUE_left, hzUE_right⟩
  have hzDF : z ∈ DF :=
    ⟨hzF_bridge, hzUF_left, hzUF_right⟩
  have htcDE : t • c ∈ DE := by
    refine ⟨?_, ?_, ?_⟩
    · change
        0 <
          ((i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i (t • c))).1).re
      rw [generatorChronologicalParameterComplexCLE_real_smul]
      simpa using mul_pos ht0 hcE_bridge
    · change
        star
            (i.splitCoordinatesCLM
              (generatorChronologicalParameterComplexCLE i (t • c))).2.1 ∈
          UE_left
      simpa [cE_left] using htUE_left
    · change
        (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i (t • c))).2.2 ∈
          UE_right
      simpa [cE_right] using htUE_right
  have htcDF : t • c ∈ DF := by
    refine ⟨?_, ?_, ?_⟩
    · change
        0 <
          ((j.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE j (t • c))).1).re
      rw [generatorChronologicalParameterComplexCLE_real_smul]
      simpa using mul_pos ht0 hcF_bridge
    · change
        star
            (j.splitCoordinatesCLM
              (generatorChronologicalParameterComplexCLE j (t • c))).2.1 ∈
          UF_left
      simpa [cF_left] using htUF_left
    · change
        (j.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE j (t • c))).2.2 ∈
          UF_right
      simpa [cF_right] using htUF_right
  have hsegment :
      segment ℝ z (t • c) ⊆
        E.radialChronologicalDomain i ∩
          F.radialChronologicalDomain j := by
    intro w hw
    exact
      ⟨hDE_subset (hDE_convex.segment_subset hzDE htcDE hw),
        hDF_subset (hDF_convex.segment_subset hzDF htcDF hw)⟩
  have hjoin_z_tc :
      JoinedIn
        (E.radialChronologicalDomain i ∩
          F.radialChronologicalDomain j)
        z (t • c) :=
    JoinedIn.of_segment_subset hsegment
  let pathToEdge : ℝ → OSIITimeGapSpace k :=
    fun s => ((1 - s) * t + s) • c
  have hjoin_tc_c :
      JoinedIn
        (E.radialChronologicalDomain i ∩
          F.radialChronologicalDomain j)
        (t • c) c := by
    apply JoinedIn.ofLine (f := pathToEdge)
    · fun_prop
    · simp [pathToEdge]
    · simp [pathToEdge]
    · rintro _ ⟨s, hs, rfl⟩
      have hscale_pos : 0 < (1 - s) * t + s := by
        nlinarith [hs.1, hs.2]
      have hscale_le : (1 - s) * t + s ≤ 1 := by
        nlinarith [hs.1, hs.2, ht1]
      exact
        ⟨E.real_smul_mem_radialChronologicalDomain
            i hcE hscale_pos hscale_le,
          F.real_smul_mem_radialChronologicalDomain
            j hcF hscale_pos hscale_le⟩
  exact (hjoin_z_tc.trans hjoin_tc_c).symm

/-- A radial chronological generator domain has path-connected intersection
with a convex chart whenever the chart contains the positive radial segment
through one common point. -/
theorem radialChronologicalDomain_inter_convex_isPathConnected
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    {C : Set (OSIITimeGapSpace k)}
    (hC_convex : Convex ℝ C)
    {c : OSIITimeGapSpace k}
    (hcE : c ∈ E.radialChronologicalDomain i)
    (hcC : c ∈ C)
    (hsmulC :
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → t • c ∈ C) :
    IsPathConnected (E.radialChronologicalDomain i ∩ C) := by
  refine ⟨c, ⟨hcE, hcC⟩, ?_⟩
  intro z hz
  rcases hz.1 with ⟨hz_bridge, hz_left, hz_right⟩
  change
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i z)).2.1 ∈
      openZeroConvexKernel (E.leftDomain i) at hz_left
  rcases hz_left with
    ⟨U_left, hU_left_open, hU_left_convex, h0U_left,
      hU_left_subset, hzU_left⟩
  rcases hz_right with
    ⟨U_right, hU_right_open, hU_right_convex, h0U_right,
      hU_right_subset, hzU_right⟩
  let c_left : Fin (i.n - 1) → ℂ :=
    star
      (i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i c)).2.1
  let c_right : Fin (i.m - 1) → ℂ :=
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i c)).2.2
  let T : Set ℝ :=
    ((fun t : ℝ => t • c_left) ⁻¹' U_left) ∩
      ((fun t : ℝ => t • c_right) ⁻¹' U_right)
  have hT_open : IsOpen T :=
    (hU_left_open.preimage (by fun_prop)).inter
      (hU_right_open.preimage (by fun_prop))
  have h0T : (0 : ℝ) ∈ T := by
    simp [T, h0U_left, h0U_right]
  obtain ⟨t, ⟨htU_left, htU_right⟩, ht0, ht1⟩ :=
    exists_pos_le_one_mem_of_isOpen_zero_mem hT_open h0T
  have hcE' := hcE
  rcases hcE' with ⟨hc_bridge, _hc_left, _hc_right⟩
  let D : Set (OSIITimeGapSpace k) :=
    generatorChronologicalParameterComplexCLE i ⁻¹'
      generatorSemigroupDomain i U_left U_right
  have hD_convex : Convex ℝ D :=
    convex_chronologicalGeneratorSemigroupDomain i
      hU_left_convex hU_right_convex
  have hD_subset :
      D ⊆ E.radialChronologicalDomain i :=
    E.chronologicalWitnessDomain_subset_radialChronologicalDomain i
      hU_left_open hU_left_convex h0U_left hU_left_subset
      hU_right_open hU_right_convex h0U_right hU_right_subset
  have hzD : z ∈ D :=
    ⟨hz_bridge, hzU_left, hzU_right⟩
  have htcD : t • c ∈ D := by
    refine ⟨?_, ?_, ?_⟩
    · change
        0 <
          ((i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i (t • c))).1).re
      rw [generatorChronologicalParameterComplexCLE_real_smul]
      simpa using mul_pos ht0 hc_bridge
    · change
        star
            (i.splitCoordinatesCLM
              (generatorChronologicalParameterComplexCLE i (t • c))).2.1 ∈
          U_left
      simpa [c_left] using htU_left
    · change
        (i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i (t • c))).2.2 ∈
          U_right
      simpa [c_right] using htU_right
  have htcC : t • c ∈ C :=
    hsmulC ht0 ht1
  have hsegment :
      segment ℝ z (t • c) ⊆
        E.radialChronologicalDomain i ∩ C := by
    intro w hw
    exact
      ⟨hD_subset (hD_convex.segment_subset hzD htcD hw),
        hC_convex.segment_subset hz.2 htcC hw⟩
  have hjoin_z_tc :
      JoinedIn (E.radialChronologicalDomain i ∩ C)
        z (t • c) :=
    JoinedIn.of_segment_subset hsegment
  let pathToEdge : ℝ → OSIITimeGapSpace k :=
    fun s => ((1 - s) * t + s) • c
  have hjoin_tc_c :
      JoinedIn (E.radialChronologicalDomain i ∩ C)
        (t • c) c := by
    apply JoinedIn.ofLine (f := pathToEdge)
    · fun_prop
    · simp [pathToEdge]
    · simp [pathToEdge]
    · rintro _ ⟨s, hs, rfl⟩
      have hscale_pos : 0 < (1 - s) * t + s := by
        nlinarith [hs.1, hs.2]
      have hscale_le : (1 - s) * t + s ≤ 1 := by
        nlinarith [hs.1, hs.2, ht1]
      exact
        ⟨E.real_smul_mem_radialChronologicalDomain
            i hcE hscale_pos hscale_le,
          hsmulC hscale_pos hscale_le⟩
  exact (hjoin_z_tc.trans hjoin_tc_c).symm

end GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

end OSIIChapterV
end OSReconstruction
