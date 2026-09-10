/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertTaylor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDoubleDeltaSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertSource
import OSReconstruction.SCV.LocallyUniformLimit















noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- Uniform convergence of a two-index Gram kernel to one common scalar
function makes the underlying Hilbert-valued functions uniformly Cauchy.

This is the local-uniform version of
`cauchySeq_of_tendsto_pairwise_inner`. It is the functional-analytic bridge
needed when shrinking positive-time sources are used to construct an entire
holomorphic Hilbert field rather than one vector at a single real point. -/
theorem uniformCauchySeqOn_of_tendstoUniformlyOn_pairwise_inner
    {X H : Type*}
    [PseudoMetricSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : ℕ → X → H)
    (value : X → ℂ)
    (U : Set X)
    (hinner :
      TendstoUniformlyOn
        (fun pq : ℕ × ℕ => fun x =>
          @inner ℂ H _ (F pq.1 x) (F pq.2 x))
        value Filter.atTop U) :
    UniformCauchySeqOn F Filter.atTop U := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let δ : ℝ := ε ^ 2 / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have huniform :=
    Metric.tendstoUniformlyOn_iff.mp hinner δ hδ
  rw [Filter.eventually_atTop] at huniform
  obtain ⟨pq₀, hpq₀⟩ := huniform
  refine ⟨max pq₀.1 pq₀.2, ?_⟩
  intro m hm n hn x hx
  have hm1 : pq₀.1 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : pq₀.2 ≤ m := le_trans (le_max_right _ _) hm
  have hn1 : pq₀.1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : pq₀.2 ≤ n := le_trans (le_max_right _ _) hn
  let a : ℂ := @inner ℂ H _ (F m x) (F m x)
  let b : ℂ := @inner ℂ H _ (F m x) (F n x)
  let c : ℂ := @inner ℂ H _ (F n x) (F m x)
  let e : ℂ := @inner ℂ H _ (F n x) (F n x)
  let v : ℂ := value x
  have ha : ‖a - v‖ < δ := by
    simpa [a, v, dist_eq_norm, norm_sub_rev] using
      hpq₀ (m, m) ⟨hm1, hm2⟩ x hx
  have hb : ‖b - v‖ < δ := by
    simpa [b, v, dist_eq_norm, norm_sub_rev] using
      hpq₀ (m, n) ⟨hm1, hn2⟩ x hx
  have hc : ‖c - v‖ < δ := by
    simpa [c, v, dist_eq_norm, norm_sub_rev] using
      hpq₀ (n, m) ⟨hn1, hm2⟩ x hx
  have he : ‖e - v‖ < δ := by
    simpa [e, v, dist_eq_norm, norm_sub_rev] using
      hpq₀ (n, n) ⟨hn1, hn2⟩ x hx
  have hcomb :
      ‖a - c - (b - e)‖ < 4 * δ := by
    calc
      ‖a - c - (b - e)‖ =
          ‖(a - v) - (c - v) - ((b - v) - (e - v))‖ := by
            congr 1
            ring
      _ ≤ ‖a - v‖ + ‖c - v‖ + (‖b - v‖ + ‖e - v‖) := by
            calc
              ‖(a - v) - (c - v) - ((b - v) - (e - v))‖
                  ≤ ‖(a - v) - (c - v)‖ +
                      ‖(b - v) - (e - v)‖ :=
                    norm_sub_le _ _
              _ ≤ ‖a - v‖ + ‖c - v‖ +
                    (‖b - v‖ + ‖e - v‖) :=
                  add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ < δ + δ + (δ + δ) :=
            add_lt_add (add_lt_add ha hc) (add_lt_add hb he)
      _ = 4 * δ := by ring
  have hinner_sub :
      @inner ℂ H _ (F m x - F n x) (F m x - F n x) =
        a - c - (b - e) := by
    simp only [inner_sub_left, inner_sub_right, a, b, c, e]
  have hsq :
      ‖F m x - F n x‖ ^ 2 < ε ^ 2 := by
    calc
      ‖F m x - F n x‖ ^ 2 =
          (@inner ℂ H _ (F m x - F n x) (F m x - F n x)).re := by
            exact
              (inner_self_eq_norm_sq
                (𝕜 := ℂ) (F m x - F n x)).symm
      _ = (a - c - (b - e)).re := by rw [hinner_sub]
      _ ≤ ‖a - c - (b - e)‖ := Complex.re_le_norm _
      _ < 4 * δ := hcomb
      _ = ε ^ 2 := by
        dsimp [δ]
        ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (F m x - F n x)]

/-- The exact local convergence input needed to complete a sequence of
Hilbert-valued fields. Unlike pairwise Gram-limit data, this does not choose
or postulate a scalar limiting kernel. -/
structure LocallyUniformCauchyData
    {m : ℕ}
    {H : Type*}
    [NormedAddCommGroup H]
    (F : ℕ → (Fin m → ℂ) → H)
    (U : Set (Fin m → ℂ)) where
  locallyUniform :
    ∀ z ∈ U, ∃ V ∈ 𝓝[U] z,
      UniformCauchySeqOn F Filter.atTop V

/-- Local strong-uniform convergence data for the pairwise Gram kernels of a
sequence of Hilbert-valued fields. The neighborhood is fixed for all
entourages, which is exactly the strength needed to construct a locally
uniform vector-valued limit. -/
structure LocallyUniformPairwiseInnerLimitData
    {m : ℕ}
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : ℕ → (Fin m → ℂ) → H)
    (U : Set (Fin m → ℂ)) where
  value : (Fin m → ℂ) → ℂ
  locallyUniform :
    ∀ z ∈ U, ∃ V ∈ 𝓝[U] z,
      TendstoUniformlyOn
        (fun pq : ℕ × ℕ => fun w =>
          @inner ℂ H _ (F pq.1 w) (F pq.2 w))
        value Filter.atTop V

/-- Producer-facing local representation of a scale-indexed Hilbert field's
pairwise Gram kernels by two independently shrinking delta families.

At every complex parameter, one compact relative neighborhood and one fixed
real-coordinate ball must support a jointly continuous scalar kernel. Exact
finite-scale representation then lets the uniform tensor-delta theorem
construct `LocallyUniformPairwiseInnerLimitData`. -/
structure LocallyCompactTensorPairGramRepresentationData
    {a m : ℕ}
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : ℕ → (Fin a → ℂ) → H)
    (U : Set (Fin a → ℂ)) where
  leftTest : ℕ → SchwartzMap (Fin m → ℝ) ℂ
  rightTest : ℕ → SchwartzMap (Fin m → ℝ) ℂ
  leftRadius : ℕ → ℝ
  rightRadius : ℕ → ℝ
  left_nonnegative :
    ∀ N x, 0 ≤ (leftTest N x).re
  right_nonnegative :
    ∀ N x, 0 ≤ (rightTest N x).re
  left_real :
    ∀ N x, (leftTest N x).im = 0
  right_real :
    ∀ N x, (rightTest N x).im = 0
  left_integral_one :
    ∀ N, ∫ x : Fin m → ℝ, leftTest N x = 1
  right_integral_one :
    ∀ N, ∫ x : Fin m → ℝ, rightTest N x = 1
  left_support :
    ∀ N, Function.support (leftTest N : (Fin m → ℝ) → ℂ) ⊆
      Metric.ball 0 (leftRadius N)
  right_support :
    ∀ N, Function.support (rightTest N : (Fin m → ℝ) → ℂ) ⊆
      Metric.ball 0 (rightRadius N)
  leftRadius_tendsto :
    Filter.Tendsto leftRadius Filter.atTop (𝓝 0)
  rightRadius_tendsto :
    Filter.Tendsto rightRadius Filter.atTop (𝓝 0)
  value : (Fin a → ℂ) → ℂ
  localData :
    ∀ z ∈ U,
      ∃ K ∈ 𝓝[U] z, IsCompact K ∧
        ∃ R > 0,
          ∃ kernel :
              (Fin a → ℂ) → (Fin (m + m) → ℝ) → ℂ,
            ∃ center :
                (Fin a → ℂ) → (Fin (m + m) → ℝ),
              ContinuousOn
                  (Function.uncurry fun w y =>
                    kernel w (center w + y))
                  (K ×ˢ
                    Metric.closedBall
                      (0 : Fin (m + m) → ℝ) R) ∧
                (∀ (pq : ℕ × ℕ) w, w ∈ K →
                  MeasureTheory.Integrable
                    (fun y : Fin (m + m) → ℝ =>
                      ((leftTest pq.1).tensorProduct
                        (rightTest pq.2)) y *
                          kernel w (center w + y))) ∧
                (∀ (pq : ℕ × ℕ) w, w ∈ K →
                  @inner ℂ H _ (F pq.1 w) (F pq.2 w) =
                    ∫ y : Fin (m + m) → ℝ,
                      ((leftTest pq.1).tensorProduct
                        (rightTest pq.2)) y *
                          kernel w (center w + y)) ∧
                ∀ w ∈ K, value w = kernel w (center w)

namespace LocallyCompactTensorPairGramRepresentationData

variable {a m : ℕ}
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {F : ℕ → (Fin a → ℂ) → H}
variable {U : Set (Fin a → ℂ)}

/-- Compact local scalar representations of all pairwise reflected Gram
kernels supply the exact local-uniform inner-product data consumed by the
Hilbert-field limit theorem. -/
noncomputable def toLocallyUniformPairwiseInnerLimitData
    (D :
      @LocallyCompactTensorPairGramRepresentationData
        a m H _ _ F U) :
    LocallyUniformPairwiseInnerLimitData F U where
  value := D.value
  locallyUniform := by
    intro z hz
    obtain ⟨K, hK_nhds, hK_compact, R, hR, kernel, center,
      hkernel_cont, hintegrable, hrepresent, hvalue⟩ :=
      D.localData z hz
    refine ⟨K, hK_nhds, ?_⟩
    have hdelta :=
      tendstoUniformlyOn_integral_tensorPair_shrinking_schwartz_approx_identities_of_compact
        D.leftTest D.rightTest D.leftRadius D.rightRadius
        kernel center K hK_compact R hR
        D.left_nonnegative D.right_nonnegative
        D.left_real D.right_real
        D.left_integral_one D.right_integral_one
        D.left_support D.right_support
        D.leftRadius_tendsto D.rightRadius_tendsto
        hkernel_cont hintegrable
    have hinner :
        TendstoUniformlyOn
          (fun pq : ℕ × ℕ => fun w =>
            @inner ℂ H _ (F pq.1 w) (F pq.2 w))
          (fun w => kernel w (center w)) Filter.atTop K :=
      hdelta.congr
        (Filter.Eventually.of_forall fun pq w hw =>
          (hrepresent pq w hw).symm)
    exact hinner.congr_right fun w hw => (hvalue w hw).symm

end LocallyCompactTensorPairGramRepresentationData

namespace LocallyUniformCauchyData

variable {m : ℕ}
variable {H : Type*}
  [NormedAddCommGroup H]
variable {F : ℕ → (Fin m → ℂ) → H}
variable {U : Set (Fin m → ℂ)}

/-- A locally uniformly Cauchy field sequence has a locally uniform limit in
every complete target. -/
theorem exists_field
    [CompleteSpace H]
    (C : LocallyUniformCauchyData F U) :
    ∃ Ψ : (Fin m → ℂ) → H,
      TendstoLocallyUniformlyOn F Ψ Filter.atTop U := by
  exact
    SCV.exists_tendstoLocallyUniformlyOn_of_locally_uniformCauchy
      C.locallyUniform

/-- Continuous locally uniformly Cauchy fields have a continuous locally
uniform limit. -/
theorem exists_continuousField
    [CompleteSpace H]
    (C : LocallyUniformCauchyData F U)
    (hF_cont : ∀ N, ContinuousOn (F N) U) :
    ∃ Ψ : (Fin m → ℂ) → H,
      TendstoLocallyUniformlyOn F Ψ Filter.atTop U ∧
        ContinuousOn Ψ U := by
  obtain ⟨Ψ, hΨ⟩ := C.exists_field
  exact
    ⟨Ψ, hΨ,
      hΨ.continuousOn (Filter.Frequently.of_forall hF_cont)⟩

/-- On every compact subset of the common parameter domain, local uniform
Cauchy convergence and finite-scale continuity give one squared-norm bound
for all approximating fields. -/
theorem exists_norm_sq_bound_on_compact_of_continuousOn
    [CompleteSpace H]
    (C : LocallyUniformCauchyData F U)
    (hF_cont : ∀ N, ContinuousOn (F N) U)
    (K : Set (Fin m → ℂ))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N z, z ∈ K → ‖F N z‖ ^ 2 ≤ B := by
  obtain ⟨Ψ, hΨ, hΨ_cont⟩ :=
    C.exists_continuousField hF_cont
  have hΨK :
      TendstoUniformlyOn F Ψ Filter.atTop K := by
    exact
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        hK_compact).mp (hΨ.mono hK_subset)
  obtain ⟨RΨ, hRΨ⟩ :=
    hK_compact.exists_bound_of_continuousOn
      (hΨ_cont.mono hK_subset)
  have hclose_event :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ z ∈ K, dist (Ψ z) (F N z) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp hΨK) 1 zero_lt_one
  rw [Filter.eventually_atTop] at hclose_event
  obtain ⟨N0, hclose⟩ := hclose_event
  have hprefix :
      ∀ n : Fin N0, ∃ R : ℝ, ∀ z ∈ K, ‖F n z‖ ≤ R := by
    intro n
    exact
      hK_compact.exists_bound_of_continuousOn
        ((hF_cont n).mono hK_subset)
  choose R hR using hprefix
  let M : ℝ :=
    1 + |RΨ| + ∑ n : Fin N0, |R n|
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨M ^ 2, sq_nonneg M, ?_⟩
  intro N z hz
  have hnorm : ‖F N z‖ ≤ M := by
    by_cases hN : N0 ≤ N
    · have hcloseNz : ‖F N z - Ψ z‖ < 1 := by
        simpa [dist_eq_norm, norm_sub_rev] using hclose N hN z hz
      have htriangle :
          ‖F N z‖ ≤ ‖F N z - Ψ z‖ + ‖Ψ z‖ := by
        calc
          ‖F N z‖ = ‖(F N z - Ψ z) + Ψ z‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖F N z - Ψ z‖ + ‖Ψ z‖ := norm_add_le _ _
      have hlimit : ‖Ψ z‖ ≤ RΨ := hRΨ z hz
      have hlarge : ‖F N z‖ ≤ 1 + |RΨ| := by
        calc
          ‖F N z‖ ≤ ‖F N z - Ψ z‖ + ‖Ψ z‖ := htriangle
          _ ≤ 1 + RΨ := by linarith
          _ ≤ 1 + |RΨ| := by
            gcongr
            exact le_abs_self RΨ
      have hsum : 0 ≤ ∑ n : Fin N0, |R n| := by
        exact Finset.sum_nonneg fun n _ => abs_nonneg (R n)
      exact hlarge.trans (by
        dsimp [M]
        linarith)
    · have hNlt : N < N0 := Nat.lt_of_not_ge hN
      let n : Fin N0 := ⟨N, hNlt⟩
      have hsmall : ‖F N z‖ ≤ R n := by
        simpa [n] using hR n z hz
      have hsingle :
          |R n| ≤ ∑ j : Fin N0, |R j| := by
        exact Finset.single_le_sum
          (fun j _ => abs_nonneg (R j)) (Finset.mem_univ n)
      calc
        ‖F N z‖ ≤ R n := hsmall
        _ ≤ |R n| := le_abs_self (R n)
        _ ≤ ∑ j : Fin N0, |R j| := hsingle
        _ ≤ M := by
          dsimp [M]
          linarith [abs_nonneg RΨ]
  exact pow_le_pow_left₀ (norm_nonneg (F N z)) hnorm 2

end LocallyUniformCauchyData

namespace LocallyUniformPairwiseInnerLimitData

variable {m : ℕ}
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {F : ℕ → (Fin m → ℂ) → H}
variable {U : Set (Fin m → ℂ)}

/-- Pairwise Gram convergence supplies the local uniform Cauchy condition for
the Hilbert fields themselves. -/
theorem locallyUniformCauchy
    (G : LocallyUniformPairwiseInnerLimitData F U) :
    ∀ z ∈ U, ∃ V ∈ 𝓝[U] z,
      UniformCauchySeqOn F Filter.atTop V := by
  intro z hz
  obtain ⟨V, hV, hinner⟩ := G.locallyUniform z hz
  exact
    ⟨V, hV,
      uniformCauchySeqOn_of_tendstoUniformlyOn_pairwise_inner
        F G.value V hinner⟩

/-- Forget the scalar limiting Gram kernel and retain only the local uniform
Cauchy estimate actually used by completion and compact bounds. -/
def toLocallyUniformCauchyData
    (G : LocallyUniformPairwiseInnerLimitData F U) :
    LocallyUniformCauchyData F U where
  locallyUniform := G.locallyUniformCauchy

/-- Holomorphic Hilbert fields whose two-index Gram kernels converge locally
uniformly have a locally uniform holomorphic limit field. -/
theorem exists_holomorphicField
    [CompleteSpace H]
    (G : LocallyUniformPairwiseInnerLimitData F U)
    (hF_hol : ∀ N, DifferentiableOn ℂ (F N) U)
    (hU_open : IsOpen U) :
    ∃ Ψ : (Fin m → ℂ) → H,
      TendstoLocallyUniformlyOn F Ψ Filter.atTop U ∧
        DifferentiableOn ℂ Ψ U := by
  exact
    SCV.exists_tendstoLocallyUniformlyOn_differentiableOn_fin_of_locally_uniformCauchy
      G.locallyUniformCauchy hF_hol hU_open

/-- Continuous Hilbert fields whose two-index Gram kernels converge locally
uniformly have a locally uniform continuous limit field.

Unlike `exists_holomorphicField`, this statement does not require the
parameter domain to be open.  It is the appropriate compact-control result
for families parametrized only by real chronological translations. -/
theorem exists_continuousField
    [CompleteSpace H]
    (G : LocallyUniformPairwiseInnerLimitData F U)
    (hF_cont : ∀ N, ContinuousOn (F N) U) :
    ∃ Ψ : (Fin m → ℂ) → H,
      TendstoLocallyUniformlyOn F Ψ Filter.atTop U ∧
        ContinuousOn Ψ U := by
  obtain ⟨Ψ, hΨ⟩ :=
    SCV.exists_tendstoLocallyUniformlyOn_of_locally_uniformCauchy
      G.locallyUniformCauchy
  refine ⟨Ψ, hΨ, ?_⟩
  exact hΨ.continuousOn (Filter.Frequently.of_forall hF_cont)

/-- On every compact subset of the common parameter domain, locally uniform
pairwise Gram convergence and continuity give one squared-norm bound for all
approximating Hilbert fields. -/
theorem exists_norm_sq_bound_on_compact_of_continuousOn
    [CompleteSpace H]
    (G : LocallyUniformPairwiseInnerLimitData F U)
    (hF_cont : ∀ N, ContinuousOn (F N) U)
    (K : Set (Fin m → ℂ))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N z, z ∈ K → ‖F N z‖ ^ 2 ≤ C := by
  obtain ⟨Ψ, hΨ, hΨ_cont⟩ :=
    G.exists_continuousField hF_cont
  have hΨK :
      TendstoUniformlyOn F Ψ Filter.atTop K := by
    exact
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        hK_compact).mp (hΨ.mono hK_subset)
  obtain ⟨RΨ, hRΨ⟩ :=
    hK_compact.exists_bound_of_continuousOn
      (hΨ_cont.mono hK_subset)
  have hclose_event :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ z ∈ K, dist (Ψ z) (F N z) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp hΨK) 1 zero_lt_one
  rw [Filter.eventually_atTop] at hclose_event
  obtain ⟨N0, hclose⟩ := hclose_event
  have hprefix :
      ∀ n : Fin N0, ∃ R : ℝ, ∀ z ∈ K, ‖F n z‖ ≤ R := by
    intro n
    exact
      hK_compact.exists_bound_of_continuousOn
        ((hF_cont n).mono hK_subset)
  choose R hR using hprefix
  let B : ℝ :=
    1 + |RΨ| + ∑ n : Fin N0, |R n|
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B ^ 2, sq_nonneg B, ?_⟩
  intro N z hz
  have hnorm : ‖F N z‖ ≤ B := by
    by_cases hN : N0 ≤ N
    · have hcloseNz : ‖F N z - Ψ z‖ < 1 := by
        simpa [dist_eq_norm, norm_sub_rev] using hclose N hN z hz
      have htriangle :
          ‖F N z‖ ≤ ‖F N z - Ψ z‖ + ‖Ψ z‖ := by
        calc
          ‖F N z‖ = ‖(F N z - Ψ z) + Ψ z‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖F N z - Ψ z‖ + ‖Ψ z‖ := norm_add_le _ _
      have hlimit : ‖Ψ z‖ ≤ RΨ := hRΨ z hz
      have hlarge : ‖F N z‖ ≤ 1 + |RΨ| := by
        calc
          ‖F N z‖ ≤ ‖F N z - Ψ z‖ + ‖Ψ z‖ := htriangle
          _ ≤ 1 + RΨ := by linarith
          _ ≤ 1 + |RΨ| := by
            gcongr
            exact le_abs_self RΨ
      have hsum : 0 ≤ ∑ n : Fin N0, |R n| := by
        exact Finset.sum_nonneg fun n _ => abs_nonneg (R n)
      exact hlarge.trans (by
        dsimp [B]
        linarith)
    · have hNlt : N < N0 := Nat.lt_of_not_ge hN
      let n : Fin N0 := ⟨N, hNlt⟩
      have hsmall : ‖F N z‖ ≤ R n := by
        simpa [n] using hR n z hz
      have hsingle :
          |R n| ≤ ∑ j : Fin N0, |R j| := by
        exact Finset.single_le_sum
          (fun j _ => abs_nonneg (R j)) (Finset.mem_univ n)
      calc
        ‖F N z‖ ≤ R n := hsmall
        _ ≤ |R n| := le_abs_self (R n)
        _ ≤ ∑ j : Fin N0, |R j| := hsingle
        _ ≤ B := by
          dsimp [B]
          linarith [abs_nonneg RΨ]
  exact pow_le_pow_left₀ (norm_nonneg (F N z)) hnorm 2

/-- On every compact subset of the common parameter domain, locally uniform
pairwise Gram convergence gives one squared-norm bound for all approximating
Hilbert fields. -/
theorem exists_norm_sq_bound_on_compact
    [CompleteSpace H]
    (G : LocallyUniformPairwiseInnerLimitData F U)
    (hF_hol : ∀ N, DifferentiableOn ℂ (F N) U)
    (_hU_open : IsOpen U)
    (K : Set (Fin m → ℂ))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N z, z ∈ K → ‖F N z‖ ^ 2 ≤ C := by
  exact G.exists_norm_sq_bound_on_compact_of_continuousOn
    (fun N => (hF_hol N).continuousOn) K hK_compact hK_subset

end LocallyUniformPairwiseInnerLimitData

end OSIIChapterV
end OSReconstruction
