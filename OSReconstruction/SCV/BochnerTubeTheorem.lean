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
* `holomorphic_extension_from_local` -- DifferentiableOn part only; the agreement
  part (f_ext = f on U) is sorry-free. Needs the identity theorem consistency argument.

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

/-! ### Local extension at each point -/

/-- **Local Bochner extension**: For each z in T(conv C), there is an open
    neighborhood U of z in T(conv C) and a holomorphic function G on U that
    agrees with F on T(C) intersect U.

    The construction uses the Cauchy integral formula on polydiscs centered at z
    with contours in T(C). Im(z) is in the open set conv(C), so there is a
    polydisc around z whose distinguished boundary has imaginary parts in C (by
    the convex hull characterization + openness of C). The Cauchy integral
    on this polydisc defines G, which is holomorphic by differentiation under
    the integral sign.

    Ref: Hormander, Theorem 2.5.10 proof -/
theorem bochner_local_extension {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (_hF : DifferentiableOn ℂ F (TubeDomain C))
    {z : Fin m → ℂ} (_hz : z ∈ TubeDomain (convexHull ℝ C)) :
    ∃ (G : (Fin m → ℂ) → ℂ) (U : Set (Fin m → ℂ)),
      IsOpen U ∧ z ∈ U ∧ U ⊆ TubeDomain (convexHull ℝ C) ∧
      DifferentiableOn ℂ G U ∧
      ∀ w ∈ TubeDomain C ∩ U, G w = F w := by
  sorry

/-! ### Global extension from local extensions

The global patching argument: given local holomorphic extensions at every point of
a connected domain D that agree with a holomorphic function f on a nonempty open
subset U of D, the identity theorem forces consistency, yielding a global extension.

In our case, D = T(conv C), U = T(C), f = F.
-/

/-- **Local-to-global holomorphic extension on connected domains.**

If D is a connected open set in C^m, U is a nonempty open subset of D,
f is holomorphic on U, and at every point z of D there is a local holomorphic
extension of f (agreeing with f on U), then f extends to a holomorphic function
on D.

The construction defines F_ext(z) = G_z(z) where G_z is any local extension at z.
Well-definedness follows from the identity theorem: any two local extensions
G_z, G_w that agree with f on U must agree on U_z cap U_w (since U is nonempty
open and connected to both U_z and U_w through D). -/
theorem holomorphic_extension_from_local {m : ℕ}
    {D : Set (Fin m → ℂ)} (hD_open : IsOpen D) (hD_conn : IsConnected D)
    {U : Set (Fin m → ℂ)} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_sub : U ⊆ D)
    {f : (Fin m → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U)
    (hlocal : ∀ z ∈ D, ∃ (G : (Fin m → ℂ) → ℂ) (V : Set (Fin m → ℂ)),
      IsOpen V ∧ z ∈ V ∧ V ⊆ D ∧ DifferentiableOn ℂ G V ∧ ∀ w ∈ U ∩ V, G w = f w) :
    ∃ (f_ext : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ f_ext D ∧
      ∀ z ∈ U, f_ext z = f z := by
  -- The proof uses the open-closed argument on the connected set D.
  --
  -- Define S = {z in D : there exists an open V containing z and a function g
  -- holomorphic on V with g = f on U cap V}. Then S is open by definition.
  -- D \ S is also open: if z is in D \ S, then the local extension G_z at z
  -- is holomorphic on V_z and agrees with f on U cap V_z; this contradicts
  -- z not in S unless the local extension at z is not the "global" one,
  -- which can't happen because the local extension exists for every z in D.
  --
  -- Actually, S = D by hypothesis (every z in D has a local extension).
  -- The subtlety is CONSISTENCY: the local extensions must glue coherently.
  --
  -- Standard approach: define f_ext via the identity theorem.
  -- Since D is connected and U is a nonempty open subset, any holomorphic function
  -- on D is uniquely determined by its values on U.
  --
  -- Construction:
  -- 1. Choose local extensions G_z at each z in D
  -- 2. Define f_ext(z) = G_z(z)
  -- 3. Show f_ext is well-defined (consistency via identity theorem)
  -- 4. Show f_ext is holomorphic (local agreement with holomorphic G_z)
  -- 5. Show f_ext = f on U
  --
  -- Steps 3 and 4 require showing G_z(w) = G_w(w) for overlapping domains.
  -- This uses the identity theorem: G_z and G_w agree on U (nonempty open),
  -- so they agree on any connected component of V_z cap V_w meeting U.
  -- Since D is connected, every point is reachable from U, so by induction
  -- along chains of overlapping neighborhoods, consistency propagates.
  --
  -- This is the standard monodromy theorem / sheaf gluing for connected domains.
  -- Step 1: Choose local extensions at every point using Classical.choice
  have hchoice : ∀ z ∈ D, ∃ (G : (Fin m → ℂ) → ℂ) (V : Set (Fin m → ℂ)),
      IsOpen V ∧ z ∈ V ∧ V ⊆ D ∧ DifferentiableOn ℂ G V ∧ ∀ w ∈ U ∩ V, G w = f w :=
    hlocal
  -- Pick a specific local extension at each point of D
  choose G V hV_open hV_mem hV_sub hG_diff hG_agree using hchoice
  -- Step 2: Define f_ext(z) = G_z(z) for z ∈ D, 0 otherwise
  classical
  let f_ext : (Fin m → ℂ) → ℂ := fun z =>
    if hz : z ∈ D then G z hz z else 0
  -- Key consistency lemma: for z₁, z₂ ∈ D with w ∈ V z₁ ∩ V z₂,
  -- G z₁ w = G z₂ w (by identity theorem: both agree with f on U)
  --
  -- Proof sketch (monodromy theorem): Since D is connected and open, any two
  -- points z₁, z₂ ∈ D can be connected by a path in D. The path passes through
  -- a chain of overlapping neighborhoods V_{p₁}, V_{p₂}, ..., V_{p_k} where
  -- p₁ near z₁, p_k near z₂. At each overlap V_{pᵢ} ∩ V_{p_{i+1}}:
  -- - G_{pᵢ} and G_{p_{i+1}} both agree with f on U ∩ V_{pᵢ} ∩ V_{p_{i+1}}
  -- - If this triple intersection meets U, the identity theorem gives G_{pᵢ} = G_{p_{i+1}}
  --   on the connected component of V_{pᵢ} ∩ V_{p_{i+1}} meeting U.
  -- - The chain starting from U (where all G agree with f) propagates consistency
  --   to every point of D.
  --
  -- The formal proof requires: path-connectedness of D (from connectedness + openness
  -- in a locally path-connected space), compactness of the path image, finite subcover
  -- by the V's, and iterated application of the identity theorem.
  have h_consistency : ∀ (z₁ : Fin m → ℂ) (hz₁ : z₁ ∈ D) (z₂ : Fin m → ℂ) (hz₂ : z₂ ∈ D)
      (w : Fin m → ℂ), w ∈ V z₁ hz₁ → w ∈ V z₂ hz₂ → G z₁ hz₁ w = G z₂ hz₂ w := by
    -- The monodromy argument: chain consistency along paths in D.
    -- Both G z₁ and G z₂ agree with f on U. Since D is connected and open,
    -- path-connect z₁ to a point u ∈ U through D. Cover the path by finitely many V's.
    -- At each step, two overlapping G's agree on U ∩ overlap (nonempty by path from U),
    -- so the identity theorem forces agreement on each overlap.
    sorry
  refine ⟨f_ext, ?_, ?_⟩
  · -- DifferentiableOn ℂ f_ext D
    intro z hz
    -- f_ext agrees with G z hz on V z hz (an open neighborhood of z)
    have h_local_eq : ∀ w ∈ V z hz, f_ext w = G z hz w := by
      intro w hw
      simp only [f_ext, dif_pos (hV_sub z hz hw)]
      exact h_consistency w (hV_sub z hz hw) z hz w (hV_mem w (hV_sub z hz hw)) hw
    -- G z hz is differentiable on V z hz, and f_ext = G z hz on V z hz
    -- So f_ext is differentiable on V z hz
    have h_diff_V : DifferentiableWithinAt ℂ f_ext (V z hz) z :=
      (hG_diff z hz z (hV_mem z hz)).congr (fun w hw => h_local_eq w hw)
        (h_local_eq z (hV_mem z hz))
    -- V z hz is open and z ∈ V z hz, so V z hz ∈ nhdsWithin z D
    have hV_mem_nhds : V z hz ∈ nhdsWithin z D :=
      nhdsWithin_le_nhds ((hV_open z hz).mem_nhds (hV_mem z hz))
    exact h_diff_V.mono_of_mem_nhdsWithin hV_mem_nhds
  · -- f_ext = f on U
    intro z hz
    simp only [f_ext, dif_pos (hU_sub hz)]
    exact hG_agree z (hU_sub hz) z ⟨hz, hV_mem z (hU_sub hz)⟩

/-- **Bochner's tube theorem**: If F is holomorphic on T(C) where C is an open
    nonempty set in R^m, then F extends to a holomorphic function on T(conv C). -/
theorem bochner_tube_extension {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C)) :
    ∃ (F_ext : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (TubeDomain (convexHull ℝ C)) ∧
      ∀ z ∈ TubeDomain C, F_ext z = F z := by
  -- Infrastructure
  have hconv_open : IsOpen (convexHull ℝ C) := isOpen_convexHull_of_isOpen hC
  have hT_open : IsOpen (TubeDomain (convexHull ℝ C)) := tubeDomain_isOpen hconv_open
  have hT_conn : IsConnected (TubeDomain (convexHull ℝ C)) :=
    tubeDomain_convexHull_isConnected hC hne
  have hTC_sub : TubeDomain C ⊆ TubeDomain (convexHull ℝ C) := tubeDomain_subset_convexHull
  have hTC_open : IsOpen (TubeDomain C) := tubeDomain_isOpen hC
  have hTC_ne : (TubeDomain C).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    refine ⟨fun i => ↑(0 : ℝ) + ↑(y i) * I, ?_⟩
    show (fun i => ((↑(0 : ℝ) + ↑(y i) * I : ℂ)).im) ∈ C
    have : (fun i => ((↑(0 : ℝ) + ↑(y i) * I : ℂ)).im) = y := by
      ext i; simp [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [this]; exact hy
  -- Apply the local-to-global extension principle
  exact holomorphic_extension_from_local hT_open hT_conn hTC_open hTC_ne hTC_sub hF
    (fun z hz => bochner_local_extension hC hne hF hz)

end SCV

end
