/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.WightmanAxioms
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Spectral Condition: Definitions and Equivalence

This file contains:
1. **Momentum-space spectral condition definitions**: Fourier transform on n-point
   Schwartz space, difference-variable reduction, `SpectralConditionDistribution`,
   `ForwardTubeAnalyticity`.
2. **Equivalence proof**: `SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W`,
   using two axioms from hard analysis:
   - `cone_fourierLaplace_extension` (Vladimirov §25 Thm 25.1 / SW Thm 2-6)
   - `converse_paleyWiener_tube` (Vladimirov §26 Thm 26.1 / RS II §IX.3)

## Main Results

- `spectralConditionDistribution_iff_forwardTubeAnalyticity`:
  `SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W`
-/

noncomputable section

open MeasureTheory Complex Filter Set

/-! ### Momentum-Space Spectral Condition Definitions -/

section SpectralConditionDefinitions

variable (d : ℕ) [NeZero d]

/-- The product of closed forward light cones V̄₊ⁿ in momentum space.
    A momentum configuration (q₁, ..., qₙ) lies in this set iff each qₖ ∈ V̄₊. -/
def ProductForwardMomentumCone (n : ℕ) : Set (Fin n → Fin (d + 1) → ℝ) :=
  { q | ∀ k : Fin n, q k ∈ ForwardMomentumCone d }

/-- The Euclidean dot product on n-point spacetime:
    `⟨p, x⟩ = ∑_k ∑_μ p(k)(μ) · x(k)(μ)`. -/
def nPointDot {n : ℕ} (p x : NPointSpacetime d n) : ℝ :=
  ∑ k : Fin n, ∑ μ : Fin (d + 1), p k μ * x k μ

/-- The pointwise Fourier transform of a function on n-point spacetime:
    `(fourierTransformNPointFun f)(p) = ∫ f(x) · exp(-2πi ⟨p, x⟩) dx` -/
noncomputable def fourierTransformNPointFun {n : ℕ}
    (f : NPointSpacetime d n → ℂ) (p : NPointSpacetime d n) : ℂ :=
  ∫ x : NPointSpacetime d n,
    f x * Complex.exp (-2 * ↑Real.pi * Complex.I * ↑(nPointDot d p x))

/-- Uncurrying `(Fin n → Fin m → ℝ)` to `(Fin n × Fin m → ℝ)` as a linear equivalence. -/
private def uncurryLinearEquiv (d n : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin n × Fin (d + 1) → ℝ) where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  left_inv _ := rfl
  right_inv _ := funext fun ⟨_, _⟩ => rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous linear equivalence from `NPointSpacetime d n` to
    `EuclideanSpace ℝ (Fin n × Fin (d + 1))`, used to transfer the Fourier
    transform from Mathlib's inner-product-space formulation. -/
private noncomputable def nPointToEuclidean (n : ℕ) :
    NPointSpacetime d n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin (d + 1)) :=
  (uncurryLinearEquiv d n).toContinuousLinearEquiv |>.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin (d + 1) => ℝ)).symm

/-- The Fourier transform of a Schwartz function on n-point spacetime,
    bundled as a `SchwartzMap`.

    Defined by transferring to `EuclideanSpace ℝ (Fin n × Fin (d + 1))` (which
    has `InnerProductSpace ℝ`), applying Mathlib's `fourierTransformCLM`, and
    transferring back. -/
noncomputable def SchwartzNPointSpace.fourierTransform {n : ℕ}
    (f : SchwartzNPointSpace d n) : SchwartzNPointSpace d n :=
  let e := nPointToEuclidean d n
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    (SchwartzMap.fourierTransformCLM ℂ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f))

/-- Zero-basepoint section: embeds n difference variables into (n+1) absolute
    spacetime coordinates by setting the basepoint to zero and taking partial sums. -/
private noncomputable def diffVarSection (n : ℕ) :
    NPointSpacetime d n →L[ℝ] NPointSpacetime d (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ k μ => ∑ j : Fin k.val, ξ ⟨j.val, by omega⟩ μ
      map_add' := by
        intro ξ η; ext k μ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c ξ; ext k μ; simp [Finset.mul_sum] }

omit [NeZero d] in
@[simp] private theorem diffVarSection_zero (n : ℕ)
    (ξ : NPointSpacetime d n) (μ : Fin (d + 1)) :
    diffVarSection d n ξ 0 μ = 0 := by
  simp [diffVarSection]

omit [NeZero d] in
@[simp] private theorem diffVarSection_succ (n : ℕ)
    (ξ : NPointSpacetime d n) (k : Fin n) (μ : Fin (d + 1)) :
    diffVarSection d n ξ k.succ μ =
      diffVarSection d n ξ k.castSucc μ + ξ k μ := by
  dsimp [diffVarSection]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

omit [NeZero d] in
private theorem diffVarSection_injective (n : ℕ) :
    Function.Injective (diffVarSection d n) := by
  intro ξ₁ ξ₂ h
  ext k μ
  have h_succ := congr_fun₂ h k.succ μ
  have h_cast := congr_fun₂ h k.castSucc μ
  simp only [diffVarSection_succ] at h_succ
  linarith

/-- Reduction to difference variables: precomposes a Schwartz function on (n+1)
    spacetime points with the zero-basepoint section map, producing a Schwartz
    function of n difference variables `ξⱼ = xⱼ₊₁ - xⱼ`. -/
noncomputable def diffVarReduction (n : ℕ) :
    SchwartzNPointSpace d (n + 1) →L[ℂ] SchwartzNPointSpace d n :=
  let hanti := (diffVarSection d n).toLinearMap.injective_iff_antilipschitz.mp
    (diffVarSection_injective d n)
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (diffVarSection d n).hasTemperateGrowth hanti.choose_spec.2

/-- **Spectral condition (distribution-level / Streater-Wightman form).**

    For each n, there exists a tempered distribution `w` on n copies of spacetime
    (the reduced Wightman function in difference variables ξⱼ = xⱼ - xⱼ₊₁) such that:
    1. `w` determines `W_{n+1}` via `diffVarReduction`.
    2. The Fourier transform of `w` has support in V̄₊ⁿ.

    Ref: Streater-Wightman, "PCT, Spin and Statistics, and All That", §3-1. -/
def SpectralConditionDistribution
    (W : (n : ℕ) → SchwartzNPointSpace d n → ℂ) : Prop :=
  ∀ (n : ℕ),
    ∃ (w : SchwartzNPointSpace d n → ℂ),
      Continuous w ∧ IsLinearMap ℂ w ∧
      (∀ f : SchwartzNPointSpace d (n + 1),
        W (n + 1) f = w (diffVarReduction d n f)) ∧
      (∀ φ : SchwartzNPointSpace d n,
        (∀ q : NPointSpacetime d n, φ q ≠ 0 →
          ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
        w (φ.fourierTransform) = 0)

/-- **Forward tube analyticity condition.**

    For each n, `W_n` extends to a holomorphic function on the forward tube `T_n`,
    with distributional boundary values recovering `W_n`. -/
def ForwardTubeAnalyticity
    (W : (n : ℕ) → SchwartzNPointSpace d n → ℂ) : Prop :=
  ∀ (n : ℕ),
    ∃ (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d n) ∧
      (∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W n f)))

end SpectralConditionDefinitions

/-! ### Product Forward Tube and Paley-Wiener-Schwartz Axioms -/

variable {d : ℕ} [NeZero d]

/-- The product forward tube in difference coordinates. -/
def ProductForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { ζ | ∀ k : Fin n, InOpenForwardCone d (fun μ => (ζ k μ).im) }

/-- The product forward tube is open. -/
theorem isOpen_productForwardTube (n : ℕ) :
    IsOpen (ProductForwardTube d n) := by
  sorry

/-- **Fourier-Laplace extension** (Vladimirov §25 Thm 25.1 / SW Thm 2-6). -/
axiom cone_fourierLaplace_extension (d n : ℕ) [NeZero d]
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hw_supp : ∀ φ : SchwartzNPointSpace d n,
      (∀ q : NPointSpacetime d n, φ q ≠ 0 →
        ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
      w (φ.fourierTransform) = 0) :
    ∃ (F : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F (ProductForwardTube d n) ∧
      (∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k : Fin n, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (w φ)))

/-- **Converse Paley-Wiener-Schwartz** (Vladimirov §26 Thm 26.1 / RS II §IX.3). -/
axiom converse_paleyWiener_tube (d n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ProductForwardTube d n))
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hF_bv : ∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k : Fin n, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (w φ))) :
    ∀ φ : SchwartzNPointSpace d n,
      (∀ q : NPointSpacetime d n, φ q ≠ 0 →
        ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
      w (φ.fourierTransform) = 0

/-! ### Complex Difference Coordinates -/

/-- Complex difference-coordinate map. -/
noncomputable def complexDiffCoord (d : ℕ) (n : ℕ) :
    (Fin (n + 1) → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toFun z k μ := z k.succ μ - z k.castSucc μ
  map_add' u v := by ext k μ; simp [Pi.add_apply, add_sub_add_comm]
  map_smul' c u := by ext k μ; simp [Pi.smul_apply, smul_sub, mul_sub]

/-- Complex partial-sum section. -/
noncomputable def complexDiffVarSection (d : ℕ) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → Fin (d + 1) → ℂ) where
  toFun ζ k μ := ∑ j : Fin k.val, ζ ⟨j.val, by omega⟩ μ
  map_add' u v := by ext k μ; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext k μ; simp [Finset.mul_sum]

@[simp] lemma complexDiffVarSection_zero (n : ℕ) (ζ : Fin n → Fin (d + 1) → ℂ)
    (μ : Fin (d + 1)) : complexDiffVarSection d n ζ 0 μ = 0 := by
  simp [complexDiffVarSection]

lemma complexDiffVarSection_succ (n : ℕ) (ζ : Fin n → Fin (d + 1) → ℂ)
    (k : Fin n) (μ : Fin (d + 1)) :
    complexDiffVarSection d n ζ k.succ μ =
      complexDiffVarSection d n ζ k.castSucc μ + ζ k μ := by
  dsimp [complexDiffVarSection]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

/-- `complexDiffCoord ∘ complexDiffVarSection = id`. -/
lemma complexDiffCoord_comp_section (n : ℕ) (ζ : Fin n → Fin (d + 1) → ℂ) :
    complexDiffCoord d n (complexDiffVarSection d n ζ) = ζ := by
  ext k μ
  simp only [complexDiffCoord, LinearMap.coe_mk, AddHom.coe_mk]
  rw [complexDiffVarSection_succ]
  ring

/-! ### Geometric Glue -/

/-- Difference coordinates map ForwardTube into ProductForwardTube. -/
lemma diffCoord_maps_forwardTube_to_productTube (n : ℕ)
    (z : Fin (n + 1) → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d (n + 1)) :
    complexDiffCoord d n z ∈ ProductForwardTube d n := by
  intro k
  exact hz k.succ

/-- Shifted partial-sum section maps ProductForwardTube into ForwardTube. -/
lemma shifted_section_maps_productTube_to_forwardTube (n : ℕ)
    (z₀ : Fin (d + 1) → ℂ) (hz₀ : InOpenForwardCone d (fun μ => (z₀ μ).im))
    (ζ : Fin n → Fin (d + 1) → ℂ) (hζ : ζ ∈ ProductForwardTube d n) :
    (fun k μ => z₀ μ + complexDiffVarSection d n ζ k μ) ∈ ForwardTube d (n + 1) := by
  sorry

/-- `InForwardCone` successive differences lie in open forward cone. -/
lemma inForwardCone_succ_implies_diffs_inOpenForwardCone (n : ℕ)
    (η : Fin (n + 1) → Fin (d + 1) → ℝ) (hη : InForwardCone d (n + 1) η) :
    ∀ k : Fin n, InOpenForwardCone d (fun μ => η k.succ μ - η k.castSucc μ) := by
  intro k
  exact hη k.succ

/-! ### Proof of the Main Equivalence -/

variable (d) in
/-- The reduced distribution in difference variables exists from translation invariance. -/
lemma exists_diffVar_distribution
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n))
    (hW_transl : ∀ (n : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d n),
      (∀ x : NPointSpacetime d n, g.toFun x = f.toFun (fun i => x i + a)) →
      W n f = W n g)
    (n : ℕ) :
    ∃ (w : SchwartzNPointSpace d n → ℂ),
      Continuous w ∧ IsLinearMap ℂ w ∧
      (∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f)) := by
  sorry

variable (d) in
/-- Forward direction helper: lift F from ProductForwardTube to ForwardTube. -/
lemma forwardTube_extension_of_productTube {n : ℕ}
    {W : (m : ℕ) → SchwartzNPointSpace d m → ℂ}
    (hW_tempered : ∀ m, Continuous (W m))
    (hW_linear : ∀ m, IsLinearMap ℂ (W m))
    (hW_transl : ∀ (m : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d m),
      (∀ x : NPointSpacetime d m, g.toFun x = f.toFun (fun i => x i + a)) →
      W m f = W m g)
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_det : ∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f))
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ProductForwardTube d n))
    (hF_bv : ∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k : Fin n, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (w φ))) :
    ∃ (W_analytic : (Fin (n + 1) → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d (n + 1)) ∧
      (∀ (f : SchwartzNPointSpace d (n + 1)) (η : Fin (n + 1) → Fin (d + 1) → ℝ),
        InForwardCone d (n + 1) η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d (n + 1),
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W (n + 1) f))) := by
  -- Define W_analytic := F ∘ complexDiffCoord
  refine ⟨F ∘ (complexDiffCoord d n), ?_, ?_⟩
  · -- Holomorphicity
    intro z hz
    have hmaps := diffCoord_maps_forwardTube_to_productTube n z hz
    have hF_at := hF_holo.differentiableAt
      (IsOpen.mem_nhds (isOpen_productForwardTube n) hmaps)
    have hL_diff : DifferentiableAt ℂ (complexDiffCoord d n) z :=
      (complexDiffCoord d n).toContinuousLinearMap.differentiableAt
    exact (hF_at.comp z hL_diff).differentiableWithinAt
  · -- Boundary values
    sorry

variable (d) in
/-- Backward direction helper: construct F on ProductForwardTube from W_analytic. -/
lemma productTube_function_of_forwardTube {n : ℕ}
    {W : (m : ℕ) → SchwartzNPointSpace d m → ℂ}
    (hW_tempered : ∀ m, Continuous (W m))
    (hW_linear : ∀ m, IsLinearMap ℂ (W m))
    (hW_transl : ∀ (m : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d m),
      (∀ x : NPointSpacetime d m, g.toFun x = f.toFun (fun i => x i + a)) →
      W m f = W m g)
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hw_det : ∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f))
    (W_analytic : (Fin (n + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hWa_holo : DifferentiableOn ℂ W_analytic (ForwardTube d (n + 1)))
    (hWa_bv : ∀ (f : SchwartzNPointSpace d (n + 1)) (η : Fin (n + 1) → Fin (d + 1) → ℝ),
      InForwardCone d (n + 1) η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d (n + 1),
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W (n + 1) f))) :
    ∃ (F : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F (ProductForwardTube d n) ∧
      (∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k : Fin n, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (w φ))) := by
  sorry

variable (d) in
/-- The zero-point case of ForwardTubeAnalyticity is trivial. -/
lemma forwardTubeAnalyticity_zero
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n)) :
    ∃ (W_analytic : (Fin 0 → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d 0) ∧
      (∀ (f : SchwartzNPointSpace d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
        InForwardCone d 0 η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d 0,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W 0 f))) := by
  sorry

/-! ### Main Theorem -/

variable (d) in
/-- **Equivalence of the two spectral condition formulations.**
    Ref: Streater-Wightman, Theorem 3-5; Reed-Simon Vol. II, §IX.3. -/
theorem spectralConditionDistribution_iff_forwardTubeAnalyticity
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n))
    (hW_transl : ∀ (n : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d n),
      (∀ x : NPointSpacetime d n, g.toFun x = f.toFun (fun i => x i + a)) →
      W n f = W n g) :
    SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W := by
  constructor
  · intro hSpec n
    match n with
    | 0 => exact forwardTubeAnalyticity_zero d hW_tempered hW_linear
    | n + 1 =>
      obtain ⟨w, hw_cont, hw_lin, hw_det, hw_supp⟩ := hSpec n
      obtain ⟨F, hF_holo, hF_bv⟩ :=
        cone_fourierLaplace_extension d n w hw_cont hw_lin hw_supp
      exact forwardTube_extension_of_productTube d
        hW_tempered hW_linear hW_transl w hw_det F hF_holo hF_bv
  · intro hAnal n
    obtain ⟨W_analytic, hWa_holo, hWa_bv⟩ := hAnal (n + 1)
    obtain ⟨w, hw_cont, hw_lin, hw_det⟩ :=
      exists_diffVar_distribution d hW_tempered hW_linear hW_transl n
    refine ⟨w, hw_cont, hw_lin, hw_det, ?_⟩
    obtain ⟨F, hF_holo, hF_bv⟩ :=
      productTube_function_of_forwardTube d
        hW_tempered hW_linear hW_transl w hw_cont hw_lin hw_det
        W_analytic hWa_holo hWa_bv
    exact @converse_paleyWiener_tube d ‹_› d n ‹_› F hF_holo w hw_cont hw_lin hF_bv
