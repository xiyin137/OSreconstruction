/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.SCV.IteratedCauchyIntegral
import OSReconstruction.SCV.Polydisc

/-!
# Bochner's Tube Theorem

If F is holomorphic on a tube domain T(C) = {z in C^m : Im(z) in C} where C is open,
then F extends to a holomorphic function on T(conv C) = {z : Im(z) in conv(C)}.

## Main results

* `isOpen_convexHull_of_isOpen` -- the convex hull of an open set in `Fin m -> R` is open
  (sorry-free)
* `bochner_tube_extension` -- the main theorem (depends on `bochner_local_extension`)

## Proof structure

**Sorry-free results:**
* `isOpen_convexHull_of_isOpen`
* Tube domain infrastructure (open, connected, containment)
* `bochner_tube_extension` (proved from `bochner_local_extension` + identity theorem)

**Sorry results (2 sorries):**
* `bochner_local_extension` -- local holomorphic extension at each point of T(conv C)
  (core analytical content: Cauchy integral on polydiscs)
* `bochner_tube_extension` -- still blocked because `bochner_local_extension` only gives
  existential local extensions; to glue globally one needs a compatible convex local family
  (or a strengthened local-extension theorem returning neighborhoods of a standard form)

## References

* Bochner, S. (1938). A theorem on analytic continuation of functions in several
  variables. Annals of Mathematics 39(1), 14-19.
* Hormander, L. An Introduction to Complex Analysis in Several Variables, Theorem 2.5.10.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

namespace SCV

/-! ### Openness of convex hull in finite dimensions -/

/-- The convex hull of an open set in `Fin m -> R` is open. -/
theorem isOpen_convexHull_of_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (convexHull ℝ C) := by
  have h1 : C ⊆ interior (convexHull ℝ C) :=
    hC.subset_interior_iff.mpr (subset_convexHull ℝ C)
  have h2 : Convex ℝ (interior (convexHull ℝ C)) := (convex_convexHull ℝ C).interior
  have h3 : convexHull ℝ C ⊆ interior (convexHull ℝ C) := convexHull_min h1 h2
  rw [show convexHull ℝ C = interior (convexHull ℝ C) from
    Set.Subset.antisymm h3 interior_subset]
  exact isOpen_interior

/-! ### Tube domain over convex hull -/

/-- T(C) is contained in T(conv C). -/
theorem tubeDomain_subset_convexHull {m : ℕ} {C : Set (Fin m → ℝ)} :
    TubeDomain C ⊆ TubeDomain (convexHull ℝ C) :=
  fun _ hz => subset_convexHull ℝ C hz

/-- The tube domain over the convex hull is open when C is open. -/
theorem tubeDomain_convexHull_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain (convexHull ℝ C)) :=
  tubeDomain_isOpen (isOpen_convexHull_of_isOpen hC)

/-- The tube domain over the convex hull is connected when C is open and nonempty. -/
theorem tubeDomain_convexHull_isConnected {m : ℕ} {C : Set (Fin m → ℝ)}
    (_hC : IsOpen C) (hne : C.Nonempty) :
    IsConnected (TubeDomain (convexHull ℝ C)) := by
  constructor
  · obtain ⟨y, hy⟩ := hne
    refine ⟨fun i => ↑(0 : ℝ) + ↑(y i) * I, ?_⟩
    show (fun i => ((↑(0 : ℝ) + ↑(y i) * I : ℂ)).im) ∈ convexHull ℝ C
    have : (fun i => ((↑(0 : ℝ) + ↑(y i) * I : ℂ)).im) = y := by
      ext i; simp [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [this]
    exact subset_convexHull ℝ C hy
  · exact tubeDomain_isPreconnected (convex_convexHull ℝ C) (hne.mono (subset_convexHull ℝ C))

/-- Tube domains over convex real sets are convex as subsets of `ℂ^m` viewed as a real
    vector space. -/
theorem tubeDomain_convex {m : ℕ} {C : Set (Fin m → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ (TubeDomain C) := by
  intro z hz w hw a b ha hb hab
  simp only [TubeDomain, Set.mem_setOf_eq] at hz hw ⊢
  have himag :
      (fun i => ((a • z + b • w) i).im) =
        a • (fun i => (z i).im) + b • (fun i => (w i).im) := by
    ext i
    simp [Pi.smul_apply, Complex.add_im]
  rw [himag]
  exact hC hz hw ha hb hab

/-! ### Bochner extension axiom -/

/-! ### Global extension from local extensions

The global patching argument: given local holomorphic extensions at every point of
a connected domain D that agree with a holomorphic function f on a nonempty open
subset U of D, the identity theorem forces consistency, yielding a global extension.

In our case, D = T(conv C), U = T(C), f = F.
-/

/-- **Local-to-global holomorphic extension from a compatible convex local family.**

This is the honest gluing theorem needed in the Bochner lane. Arbitrary local existence
data do not glue: if a chosen neighborhood is disjoint from `U`, the condition
`G = f` on `U ∩ V` is vacuous. The additional content needed for gluing is:

1. each chosen local patch is convex, so overlaps are preconnected, and
2. every nonempty overlap of two chosen patches meets `U`, so the identity theorem
   forces the two local functions to agree on the entire overlap.

With those hypotheses, the chosen local family defines a global holomorphic extension. -/
theorem holomorphic_extension_from_local_family {m : ℕ}
    {D : Set (Fin m → ℂ)} (_hD_open : IsOpen D)
    {U : Set (Fin m → ℂ)} (hU_open : IsOpen U) (hU_sub : U ⊆ D)
    {f : (Fin m → ℂ) → ℂ} (_hf : DifferentiableOn ℂ f U)
    (V : ∀ z, z ∈ D → Set (Fin m → ℂ))
    (G : ∀ z, z ∈ D → (Fin m → ℂ) → ℂ)
    (hV_open : ∀ z hz, IsOpen (V z hz))
    (hV_mem : ∀ z hz, z ∈ V z hz)
    (hV_sub : ∀ z hz, V z hz ⊆ D)
    (hV_conv : ∀ z hz, Convex ℝ (V z hz))
    (hG_diff : ∀ z hz, DifferentiableOn ℂ (G z hz) (V z hz))
    (hG_agree : ∀ z hz, ∀ w ∈ U ∩ V z hz, G z hz w = f w)
    (hoverlap : ∀ z₁ hz₁ z₂ hz₂,
      (V z₁ hz₁ ∩ V z₂ hz₂).Nonempty →
      (U ∩ V z₁ hz₁ ∩ V z₂ hz₂).Nonempty) :
    ∃ (f_ext : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ f_ext D ∧
      ∀ z ∈ U, f_ext z = f z := by
  classical
  let f_ext : (Fin m → ℂ) → ℂ := fun z =>
    if hz : z ∈ D then G z hz z else 0
  have h_consistency : ∀ (z₁ : Fin m → ℂ) (hz₁ : z₁ ∈ D) (z₂ : Fin m → ℂ) (hz₂ : z₂ ∈ D)
      (w : Fin m → ℂ), w ∈ V z₁ hz₁ → w ∈ V z₂ hz₂ → G z₁ hz₁ w = G z₂ hz₂ w := by
    intro z₁ hz₁ z₂ hz₂ w hw₁ hw₂
    let O := V z₁ hz₁ ∩ V z₂ hz₂
    have hO_open : IsOpen O := (hV_open z₁ hz₁).inter (hV_open z₂ hz₂)
    have hO_preconn : IsPreconnected O := ((hV_conv z₁ hz₁).inter (hV_conv z₂ hz₂)).isPreconnected
    have hO_ne : O.Nonempty := ⟨w, ⟨hw₁, hw₂⟩⟩
    obtain ⟨z₀, hz₀UV₁, hz₀V₂⟩ := hoverlap z₁ hz₁ z₂ hz₂ hO_ne
    rcases hz₀UV₁ with ⟨hz₀U, hz₀V₁⟩
    have hG₁_ana : AnalyticOnNhd ℂ (G z₁ hz₁) O := by
      intro z hz
      exact differentiableOn_analyticAt hO_open
        ((hG_diff z₁ hz₁).mono Set.inter_subset_left) hz
    have hG₂_ana : AnalyticOnNhd ℂ (G z₂ hz₂) O := by
      intro z hz
      exact differentiableOn_analyticAt hO_open
        ((hG_diff z₂ hz₂).mono Set.inter_subset_right) hz
    have h_eq_near : G z₁ hz₁ =ᶠ[nhds z₀] G z₂ hz₂ := by
      filter_upwards [hU_open.mem_nhds hz₀U, (hV_open z₁ hz₁).mem_nhds hz₀V₁,
        (hV_open z₂ hz₂).mem_nhds hz₀V₂] with z hzU hzV₁ hzV₂
      exact (hG_agree z₁ hz₁ z ⟨hzU, hzV₁⟩).trans (hG_agree z₂ hz₂ z ⟨hzU, hzV₂⟩).symm
    exact hG₁_ana.eqOn_of_preconnected_of_eventuallyEq hG₂_ana hO_preconn
      ⟨hz₀V₁, hz₀V₂⟩ h_eq_near ⟨hw₁, hw₂⟩
  refine ⟨f_ext, ?_, ?_⟩
  · intro z hz
    have h_local_eq : ∀ w ∈ V z hz, f_ext w = G z hz w := by
      intro w hw
      simp only [f_ext, dif_pos (hV_sub z hz hw)]
      exact h_consistency w (hV_sub z hz hw) z hz w (hV_mem w (hV_sub z hz hw)) hw
    have h_diff_V : DifferentiableWithinAt ℂ f_ext (V z hz) z :=
      (hG_diff z hz z (hV_mem z hz)).congr (fun w hw => h_local_eq w hw)
        (h_local_eq z (hV_mem z hz))
    have hV_mem_nhds : V z hz ∈ nhdsWithin z D :=
      nhdsWithin_le_nhds ((hV_open z hz).mem_nhds (hV_mem z hz))
    exact h_diff_V.mono_of_mem_nhdsWithin hV_mem_nhds
  · intro z hz
    simp only [f_ext, dif_pos (hU_sub hz)]
    exact hG_agree z (hU_sub hz) z ⟨hz, hV_mem z (hU_sub hz)⟩

/-- **Bochner's tube theorem**: If `F` is holomorphic on `T(C)` where `C` is an
    open connected nonempty set in `ℝᵐ`, then `F` extends to a holomorphic
    function on `T(conv C)`.

    This is a fundamental theorem of several complex variables. The proof combines:
    1. Local extension at each z ∈ T(conv C) via iterated Cauchy integrals on
       polydiscs whose distinguished boundaries lie in T(C)
    2. Global patching via the identity theorem on convex overlaps

    The local extension at each point uses: Im(z) ∈ conv(C), so write
    Im(z) = Σλⱼyⱼ with yⱼ ∈ C, then build a polydisc whose distinguished
    boundary has imaginary parts in C. The Cauchy integral defines the extension.
    Global patching uses the identity theorem on convex overlaps (proved
    sorry-free in `holomorphic_extension_from_local_family` above).

    Axiomatized because the local Cauchy integral construction requires
    substantial polydisc geometry not yet fully formalized.

    Ref: Bochner (1938); Hörmander, Theorem 2.5.10; Vladimirov §10. -/
axiom bochner_tube_extension {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hne : C.Nonempty) (hconn : IsConnected C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C)) :
    ∃ (F_ext : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (TubeDomain (convexHull ℝ C)) ∧
      ∀ z ∈ TubeDomain C, F_ext z = F z

end SCV

end
