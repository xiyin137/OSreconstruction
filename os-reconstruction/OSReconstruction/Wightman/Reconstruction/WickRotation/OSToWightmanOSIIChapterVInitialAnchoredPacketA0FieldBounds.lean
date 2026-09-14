/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketA0PolynomialBounds






















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

/-- Non-circular continuous field data for one shrinking reflected A0 block.

The finite-scale field is continuous linear in the spatial Schwartz test.
For every fixed test, it is locally uniformly Cauchy on one common parameter
domain. The `zero_eq` field ties this parameterized package back to the
concrete positive-time source family controlled by the zero-displacement A0
contract. This is the minimal input needed for compact real-translation
bounds; no scalar Gram limit, holomorphy, or openness is required.
-/
structure LocalReflectedA0ContinuousFieldData
    {d : ℕ} [NeZero d]
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (source :
      ℕ → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n) where
  domain : Set (Fin m → ℂ)
  zero_mem_domain : (0 : Fin m → ℂ) ∈ domain
  field :
    ℕ → (Fin m → ℂ) →
      SchwartzMap E ℂ →L[ℂ] OSHilbertSpace OS
  field_continuous :
    ∀ N χ, ContinuousOn (fun z => field N z χ) domain
  cauchy :
    ∀ χ,
      LocallyUniformCauchyData
        (fun N z => field N z χ) domain
  zero_eq :
    ∀ N χ,
      field N 0 χ =
        osiiPositiveTimeSingleVectorCLM OS n (source N χ)

/-- Continuous reflected A0 fields with an honest real chronological-
translation trace.

The compact bounds use the inherited field data.  The `realEdge` identity is
the separate source-comparison input that identifies those abstract field
values with the translated positive-time vectors occurring in the packet.
-/
structure LocalReflectedA0ContinuousTranslationFieldData
    {d : ℕ} [NeZero d]
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (translatedSource :
      ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n)
    extends
      LocalReflectedA0ContinuousFieldData OS n m
        (fun N χ => translatedSource N 0 χ) where
  realRegion : Set (Fin m → ℝ)
  realRegion_nhds : realRegion ∈ 𝓝 0
  realRegion_to_domain :
    ∀ x ∈ realRegion, (fun j => (x j : ℂ)) ∈ domain
  realEdge :
    ∀ N χ x, x ∈ realRegion →
      field N (fun j => (x j : ℂ)) χ =
        osiiPositiveTimeSingleVectorCLM OS n
          (translatedSource N x χ)

namespace LocalReflectedA0ContinuousFieldData

variable {d n m : ℕ} [NeZero d]
variable
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  {OS : OsterwalderSchraderAxioms d}
  {source :
    ℕ → SchwartzMap E ℂ →
      euclideanPositiveTimeSubmodule (d := d) n}

/-- On a compact part of the common parameter domain, all scale-indexed
field maps obey one finite Schwartz-seminorm estimate. -/
theorem field_uniform_schwartzBound_on_compact
    (D : LocalReflectedA0ContinuousFieldData OS n m source)
    (K : Set (Fin m → ℂ))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ D.domain) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ N z, z ∈ K → ∀ χ,
        ‖D.field N z χ‖ ≤
          (C •
            s.sup (schwartzSeminormFamily ℝ E ℂ)) χ := by
  let J := ℕ × K
  let T : J → SchwartzMap E ℂ →L[ℝ] OSHilbertSpace OS :=
    fun j => (D.field j.1 j.2.1).restrictScalars ℝ
  have hpointwise :
      ∀ χ : SchwartzMap E ℂ,
        ∃ C : ℝ, ∀ j : J, ‖T j χ‖ ≤ C := by
    intro χ
    obtain ⟨C, hC, hbound⟩ :=
      (D.cauchy χ).exists_norm_sq_bound_on_compact_of_continuousOn
        (D.field_continuous · χ)
        K hK_compact hK_subset
    refine ⟨Real.sqrt C, ?_⟩
    intro j
    have hj := hbound j.1 j.2.1 j.2.2
    have hsqrt_sq : (Real.sqrt C) ^ 2 = C :=
      Real.sq_sqrt hC
    have hsqrt_nonneg : 0 ≤ Real.sqrt C :=
      Real.sqrt_nonneg C
    have hnorm_nonneg : 0 ≤ ‖T j χ‖ :=
      norm_nonneg _
    change ‖D.field j.1 j.2.1 χ‖ ^ 2 ≤ C at hj
    change ‖D.field j.1 j.2.1 χ‖ ≤ Real.sqrt C
    nlinarith
  obtain ⟨s, C, hC, hbound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound hpointwise
  refine ⟨s, C, hC, ?_⟩
  intro N z hz χ
  simpa [T, J] using hbound (N, ⟨z, hz⟩) χ

/-- A bounded family of multilinear spatial block constructors followed by a
parameterized reflected A0 field has polynomial growth on every
polynomially encoded product-Hermite tuple, uniformly in scale, construction
level, and compact complex parameter. -/
theorem encodedHermite_polyBounded_on_compact
    {D₀ : Type*}
    [NormedAddCommGroup D₀] [NormedSpace ℝ D₀]
    [FiniteDimensional ℝ D₀] [Nontrivial D₀]
    [MeasurableSpace D₀] [BorelSpace D₀]
    {p : ℕ}
    (A0 : LocalReflectedA0ContinuousFieldData OS n m source)
    (K : Set (Fin m → ℂ))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ A0.domain)
    (Φ : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin p => SchwartzMap D₀ ℂ)
        (SchwartzMap E ℂ))
    (hΦ :
      ∀ fs : Fin p → SchwartzMap D₀ ℂ,
        Bornology.IsVonNBounded ℝ
          (Set.range fun level => Φ level fs))
    (βs : ℕ → Fin p → ℕ)
    (hβ : ∃ Denc > 0, ∃ q : ℕ, ∀ mode j,
      (βs mode j : ℝ) ≤
        Denc * (1 + (mode : ℝ)) ^ q) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ N level z, z ∈ K → ∀ mode,
        ‖A0.field N z
          (Φ level (fun j =>
            complexifyRealSchwartz
              (GaussianField.DyninMityaginSpace.basis
                (E := SchwartzMap D₀ ℝ) (βs mode j))))‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  obtain ⟨s, C₀, hC₀, hfield⟩ :=
    A0.field_uniform_schwartzBound_on_compact
      K hK_compact hK_subset
  let J := ℕ × (K × ℕ)
  let T : J →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin p => SchwartzMap D₀ ℂ)
        (OSHilbertSpace OS) :=
    fun j =>
      (A0.field j.1 j.2.1.1).compContinuousMultilinearMap
        (Φ j.2.2)
  have hT_pointwise :
      ∀ fs : Fin p → SchwartzMap D₀ ℂ,
        ∃ C : ℝ, ∀ j : J, ‖T j fs‖ ≤ C := by
    intro fs
    obtain ⟨R, hR, hseminorm⟩ :=
      ((schwartz_withSeminorms ℝ E ℂ
        ).isVonNBounded_iff_finset_seminorm_bounded.mp
          (hΦ fs)) s
    refine ⟨(C₀ : ℝ) * R, ?_⟩
    intro j
    have hΦj :
        s.sup (schwartzSeminormFamily ℝ E ℂ)
            (Φ j.2.2 fs) < R :=
      hseminorm (Φ j.2.2 fs) ⟨j.2.2, rfl⟩
    calc
      ‖T j fs‖ =
          ‖A0.field j.1 j.2.1.1 (Φ j.2.2 fs)‖ := rfl
      _ ≤
          (C₀ • s.sup (schwartzSeminormFamily ℝ E ℂ))
            (Φ j.2.2 fs) :=
        hfield j.1 j.2.1.1 j.2.1.2 (Φ j.2.2 fs)
      _ =
          (C₀ : ℝ) *
            s.sup (schwartzSeminormFamily ℝ E ℂ)
              (Φ j.2.2 fs) := rfl
      _ ≤ (C₀ : ℝ) * R :=
        mul_le_mul_of_nonneg_left hΦj.le C₀.coe_nonneg
  obtain ⟨C, hC, q, hbound⟩ :=
    pointwiseBounded_cmm_encodedHermite_polyBounded
      T βs hβ hT_pointwise
  refine ⟨C, hC, q, ?_⟩
  intro N level z hz mode
  simpa [T, J] using
    hbound (N, (⟨z, hz⟩, level)) mode

end LocalReflectedA0ContinuousFieldData

namespace LocalReflectedA0ContinuousTranslationFieldData

variable {d n m : ℕ} [NeZero d]
variable
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  {OS : OsterwalderSchraderAxioms d}
  {translatedSource :
    ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
      euclideanPositiveTimeSubmodule (d := d) n}

/-- Reindex the concrete translated source without changing the continuous
field or its locally uniform Gram limits. -/
noncomputable def congrTranslatedSource
    {translatedSource' :
      ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n}
    (D :
      LocalReflectedA0ContinuousTranslationFieldData
        OS n m translatedSource)
    (hsource :
      ∀ N x χ, translatedSource N x χ = translatedSource' N x χ) :
    LocalReflectedA0ContinuousTranslationFieldData
      OS n m translatedSource' where
  domain := D.domain
  zero_mem_domain := D.zero_mem_domain
  field := D.field
  field_continuous := D.field_continuous
  cauchy := D.cauchy
  zero_eq := by
    intro N χ
    rw [D.zero_eq, hsource]
  realRegion := D.realRegion
  realRegion_nhds := D.realRegion_nhds
  realRegion_to_domain := D.realRegion_to_domain
  realEdge := by
    intro N χ x hx
    rw [D.realEdge N χ x hx, hsource]

/-- A compact family of honest real chronological translations inherits the
uniform encoded product-Hermite bound of the ambient continuous Gram field.
-/
theorem translated_encodedHermite_polyBounded_on_compact
    {D₀ : Type*}
    [NormedAddCommGroup D₀] [NormedSpace ℝ D₀]
    [FiniteDimensional ℝ D₀] [Nontrivial D₀]
    [MeasurableSpace D₀] [BorelSpace D₀]
    {p : ℕ}
    (A0 :
      LocalReflectedA0ContinuousTranslationFieldData
        OS n m translatedSource)
    (K : Set (Fin m → ℝ))
    (hK_compact : IsCompact K)
    (hK_real : K ⊆ A0.realRegion)
    (Φ : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin p => SchwartzMap D₀ ℂ)
        (SchwartzMap E ℂ))
    (hΦ :
      ∀ fs : Fin p → SchwartzMap D₀ ℂ,
        Bornology.IsVonNBounded ℝ
          (Set.range fun level => Φ level fs))
    (βs : ℕ → Fin p → ℕ)
    (hβ : ∃ Denc > 0, ∃ q : ℕ, ∀ mode j,
      (βs mode j : ℝ) ≤
        Denc * (1 + (mode : ℝ)) ^ q) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ N level x, x ∈ K → ∀ mode,
        ‖osiiPositiveTimeSingleVectorCLM OS n
          (translatedSource N x
            (Φ level (fun j =>
              complexifyRealSchwartz
                (GaussianField.DyninMityaginSpace.basis
                  (E := SchwartzMap D₀ ℝ) (βs mode j)))))‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  let embed : (Fin m → ℝ) → (Fin m → ℂ) :=
    fun x j => (x j : ℂ)
  let Kℂ : Set (Fin m → ℂ) := embed '' K
  have hembed_cont : Continuous embed := by
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp (continuous_apply j)
  have hKℂ_compact : IsCompact Kℂ :=
    hK_compact.image hembed_cont
  have hKℂ_subset : Kℂ ⊆ A0.domain := by
    intro z hz
    obtain ⟨x, hxK, rfl⟩ := hz
    exact A0.realRegion_to_domain x (hK_real hxK)
  obtain ⟨C, hC, q, hbound⟩ :=
    A0.toLocalReflectedA0ContinuousFieldData
      |>.encodedHermite_polyBounded_on_compact
        Kℂ hKℂ_compact hKℂ_subset Φ hΦ βs hβ
  refine ⟨C, hC, q, ?_⟩
  intro N level x hxK mode
  rw [← A0.realEdge N
    (Φ level (fun j =>
      complexifyRealSchwartz
        (GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap D₀ ℝ) (βs mode j))))
    x (hK_real hxK)]
  exact hbound N level (embed x) ⟨x, hxK, rfl⟩ mode

end LocalReflectedA0ContinuousTranslationFieldData

namespace LocalReflectedA0ContinuousTranslationFieldRepresentationData

variable {d n m r : ℕ} [NeZero d]
variable
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {OS : OsterwalderSchraderAxioms d}
  {translatedSource :
    ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
      euclideanPositiveTimeSubmodule (d := d) n}

end LocalReflectedA0ContinuousTranslationFieldRepresentationData

namespace LocalReflectedA0HilbertFieldData

variable {d n m : ℕ} [NeZero d]
variable
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  {OS : OsterwalderSchraderAxioms d}
  {source :
    ℕ → SchwartzMap E ℂ →
      euclideanPositiveTimeSubmodule (d := d) n}

end LocalReflectedA0HilbertFieldData
end OSIIChapterV
end OSReconstruction
