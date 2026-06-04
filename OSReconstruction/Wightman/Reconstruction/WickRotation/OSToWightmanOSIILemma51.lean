/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.TotallyRealIdentity

/-!
# OS II Lemma 5.1: Local Gluing Substrate

This file contains the checked gluing half of the OS II Chapter V.1
Malgrange-Zerner step.  The hard paper step is still to construct the local
directional semigroup representatives.  Once those representatives and their
real-edge compatibilities are available, the theorems here glue them to the
flat positive-time witness and to the ACR(1) holomorphic surface used by the
E-to-R payload.
-/

noncomputable section

open Complex Topology
open scoped Classical NNReal

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Local-domain guard for OS II Lemma 5.1 at the `ACR(1)` level.

The full Lemma 5.1 proof refines this qualitative radius to the paper's
dual-cone/Malgrange-Zerner quantitative radius. -/
theorem osii_lemma51_acrOne_local_ball
    {k : ℕ} {z : Fin k → Fin (d + 1) → ℂ}
    (hz : z ∈ AnalyticContinuationRegion d k 1) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        Metric.ball z ρ ⊆ AnalyticContinuationRegion d k 1 := by
  exact (Metric.isOpen_iff.mp
    (isOpen_analyticContinuationRegion_succ (d := d) (k := k) (r := 0))) z hz

/-- Flattened local-domain guard for the positive time-difference tube. -/
theorem osii_lemma51_flatPositiveTimeDiff_local_ball
    {k : ℕ} {u : Fin (k * (d + 1)) → ℝ}
    (hu : u ∈ FlatPositiveTimeDiffReal k d) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        Metric.ball u ρ ⊆ FlatPositiveTimeDiffReal k d := by
  exact (Metric.isOpen_iff.mp (isOpen_flatPositiveTimeDiffReal k d)) u hu

/-- Identity-theorem overlap closure for two local Malgrange-Zerner
representatives.

In OS II V.1 the local functions produced from different directional
continuations all continue the same real distribution.  Once an overlap contains
a real open seed, the several-variable totally-real identity theorem forces the
two holomorphic representatives to agree on the whole connected overlap. -/
theorem osii_mz_overlap_eqOn_of_real_slice_agreement
    {m : ℕ} {U : Set (Fin m → ℂ)}
    (hU_open : IsOpen U) (hU_conn : IsConnected U)
    (D₁ D₂ : (Fin m → ℂ) → ℂ)
    (hD₁ : DifferentiableOn ℂ D₁ U)
    (hD₂ : DifferentiableOn ℂ D₂ U)
    {x₀ : Fin m → ℝ} (hx₀ : SCV.realToComplex x₀ ∈ U)
    (hreal :
      ∀ x : Fin m → ℝ, SCV.realToComplex x ∈ U →
        D₁ (SCV.realToComplex x) = D₂ (SCV.realToComplex x)) :
    Set.EqOn D₁ D₂ U := by
  intro z hz
  exact SCV.holomorphic_eq_of_eq_on_real_of_connected
    hU_open hU_conn hD₁ hD₂ hx₀ hreal z hz

/-- Pairwise overlap equality for a family of local MZ representatives from real
edge agreement on every nonempty overlap.

This theorem turns the paper's statement that all local continuations continue
the same distribution into the `Set.EqOn` family required for gluing. -/
theorem osii_mz_patch_pairwise_eqOn_of_real_slice_agreement
    {m : ℕ} {ι : Type*}
    (N : ι → Set (Fin m → ℂ))
    (D : ι → (Fin m → ℂ) → ℂ)
    (hN_open : ∀ i, IsOpen (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hN_inter_conn :
      ∀ i j, (N i ∩ N j).Nonempty → IsConnected (N i ∩ N j))
    (hreal :
      ∀ i j, (N i ∩ N j).Nonempty →
        ∃ x₀ : Fin m → ℝ,
          SCV.realToComplex x₀ ∈ N i ∩ N j ∧
            ∀ x : Fin m → ℝ, SCV.realToComplex x ∈ N i ∩ N j →
              D i (SCV.realToComplex x) = D j (SCV.realToComplex x)) :
    ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j) := by
  intro i j z hz
  have hne : (N i ∩ N j).Nonempty := ⟨z, hz⟩
  rcases hreal i j hne with ⟨x₀, hx₀, hreal_ij⟩
  have hEq :
      Set.EqOn (D i) (D j) (N i ∩ N j) :=
    osii_mz_overlap_eqOn_of_real_slice_agreement
      ((hN_open i).inter (hN_open j))
      (hN_inter_conn i j hne)
      (D i) (D j)
      ((hD i).mono Set.inter_subset_left)
      ((hD j).mono Set.inter_subset_right)
      hx₀ hreal_ij
  exact hEq hz

/-- Local Malgrange-Zerner representatives on the flattened `C_k^(1)` tube glue
to the time-holomorphic flat witness surface.

The remaining OS II input is to produce the open carriers `N i`,
representatives `D i`, the cover, and the pairwise overlap equality from the
directional semigroup continuations. -/
theorem osii_flat_positive_time_witness_from_local_mz_patches
    {k : ℕ} {ι : Type*}
    (N : ι → Set (Fin (k * (d + 1)) → ℂ))
    (D : ι → (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hcover :
      SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (SCV.glued_iUnion N D) := by
  have hGdiff :
      DifferentiableOn ℂ (SCV.glued_iUnion N D)
        (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) :=
    SCV.differentiableOn_glued_iUnion hcover hN_open hD hEq
  refine ⟨hGdiff.continuousOn, ?_⟩
  intro z hz i
  let idx : Fin (k * (d + 1)) := finProdFinEquiv (i, (0 : Fin (d + 1)))
  have hupdate_diff :
      Differentiable ℂ (fun w : ℂ => Function.update z idx w) := by
    rw [differentiable_pi]
    intro p
    by_cases hp : p = idx
    · subst hp
      simpa using differentiable_id
    · simpa [Function.update, hp] using differentiable_const (z p)
  have hline_maps :
      Set.MapsTo (fun w : ℂ => Function.update z idx w)
        {w : ℂ | 0 < w.im}
        (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) := by
    intro w hw
    rw [mem_tubeDomain_flatPositiveTimeDiffReal_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [idx]
    · have hzj :
          0 < (z (finProdFinEquiv (j, (0 : Fin (d + 1))))).im := by
        exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (z := z)).mp hz j
      simpa [idx, Function.update, hji] using hzj
  simpa [idx] using
    hGdiff.comp hupdate_diff.differentiableOn hline_maps

/-- The same glued flat Malgrange-Zerner patch family gives a holomorphic scalar
on `AnalyticContinuationRegion d k 1` after the difference-coordinate pullback.

This is the ACR(1)-side form consumed by the E-to-R witness producer.  The
reproduction, symmetry, and growth fields still come from the OS I/II semigroup
and Chapter VI arguments. -/
theorem osii_acrOne_holomorphic_from_local_mz_patches
    {k : ℕ} {ι : Type*}
    (N : ι → Set (Fin (k * (d + 1)) → ℂ))
    (D : ι → (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hcover :
      SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) :
    DifferentiableOn ℂ
      (fun z : Fin k → Fin (d + 1) → ℂ =>
        SCV.glued_iUnion N D (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  have hGdiff :
      DifferentiableOn ℂ (SCV.glued_iUnion N D)
        (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) :=
    SCV.differentiableOn_glued_iUnion hcover hN_open hD hEq
  exact hGdiff.comp (differentiable_toDiffFlat_local k d).differentiableOn
      (fun z hz => (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff z).mp hz)

/-- MZ gluing with the overlap equalities supplied by real-edge identity
theorem. -/
theorem osii_flat_positive_time_witness_from_local_mz_patches_real_slice_agreement
    {k : ℕ} {ι : Type*}
    (N : ι → Set (Fin (k * (d + 1)) → ℂ))
    (D : ι → (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hcover :
      SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hN_inter_conn :
      ∀ i j, (N i ∩ N j).Nonempty → IsConnected (N i ∩ N j))
    (hreal :
      ∀ i j, (N i ∩ N j).Nonempty →
        ∃ x₀ : Fin (k * (d + 1)) → ℝ,
          SCV.realToComplex x₀ ∈ N i ∩ N j ∧
            ∀ x : Fin (k * (d + 1)) → ℝ,
              SCV.realToComplex x ∈ N i ∩ N j →
                D i (SCV.realToComplex x) = D j (SCV.realToComplex x)) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (SCV.glued_iUnion N D) := by
  exact osii_flat_positive_time_witness_from_local_mz_patches
    N D hcover hN_open hD
    (osii_mz_patch_pairwise_eqOn_of_real_slice_agreement N D hN_open hD
      hN_inter_conn hreal)

/-- ACR(1)-side MZ gluing with overlap equalities supplied by real-edge identity
theorem. -/
theorem osii_acrOne_holomorphic_from_local_mz_patches_real_slice_agreement
    {k : ℕ} {ι : Type*}
    (N : ι → Set (Fin (k * (d + 1)) → ℂ))
    (D : ι → (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hcover :
      SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hN_inter_conn :
      ∀ i j, (N i ∩ N j).Nonempty → IsConnected (N i ∩ N j))
    (hreal :
      ∀ i j, (N i ∩ N j).Nonempty →
        ∃ x₀ : Fin (k * (d + 1)) → ℝ,
          SCV.realToComplex x₀ ∈ N i ∩ N j ∧
            ∀ x : Fin (k * (d + 1)) → ℝ,
              SCV.realToComplex x ∈ N i ∩ N j →
                D i (SCV.realToComplex x) = D j (SCV.realToComplex x)) :
    DifferentiableOn ℂ
      (fun z : Fin k → Fin (d + 1) → ℂ =>
        SCV.glued_iUnion N D (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  exact osii_acrOne_holomorphic_from_local_mz_patches
    N D hcover hN_open hD
    (osii_mz_patch_pairwise_eqOn_of_real_slice_agreement N D hN_open hD
      hN_inter_conn hreal)

/-- Convex-carrier form of the MZ real-slice gluing theorem.

The OS II/Malgrange-Zerner carriers are convex local sector/tube domains.  For
convex carriers, every nonempty overlap is connected, so the remaining overlap
datum is only the common real-edge agreement. -/
theorem osii_flat_positive_time_witness_from_convex_mz_patches_real_slice_agreement
    {k : ℕ} {ι : Type*}
    (N : ι → Set (Fin (k * (d + 1)) → ℂ))
    (D : ι → (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hcover :
      SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hN_conv : ∀ i, Convex ℝ (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hreal :
      ∀ i j, (N i ∩ N j).Nonempty →
        ∃ x₀ : Fin (k * (d + 1)) → ℝ,
          SCV.realToComplex x₀ ∈ N i ∩ N j ∧
            ∀ x : Fin (k * (d + 1)) → ℝ,
              SCV.realToComplex x ∈ N i ∩ N j →
                D i (SCV.realToComplex x) = D j (SCV.realToComplex x)) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (SCV.glued_iUnion N D) := by
  exact osii_flat_positive_time_witness_from_local_mz_patches_real_slice_agreement
    N D hcover hN_open hD
    (fun i j hne => ⟨hne, ((hN_conv i).inter (hN_conv j)).isPreconnected⟩)
    hreal

/-- Convex-carrier ACR(1) form of the MZ real-slice gluing theorem. -/
theorem osii_acrOne_holomorphic_from_convex_mz_patches_real_slice_agreement
    {k : ℕ} {ι : Type*}
    (N : ι → Set (Fin (k * (d + 1)) → ℂ))
    (D : ι → (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hcover :
      SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hN_conv : ∀ i, Convex ℝ (N i))
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hreal :
      ∀ i j, (N i ∩ N j).Nonempty →
        ∃ x₀ : Fin (k * (d + 1)) → ℝ,
          SCV.realToComplex x₀ ∈ N i ∩ N j ∧
            ∀ x : Fin (k * (d + 1)) → ℝ,
              SCV.realToComplex x ∈ N i ∩ N j →
                D i (SCV.realToComplex x) = D j (SCV.realToComplex x)) :
    DifferentiableOn ℂ
      (fun z : Fin k → Fin (d + 1) → ℂ =>
        SCV.glued_iUnion N D (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  exact osii_acrOne_holomorphic_from_local_mz_patches_real_slice_agreement
    N D hcover hN_open hD
    (fun i j hne => ⟨hne, ((hN_conv i).inter (hN_conv j)).isPreconnected⟩)
    hreal

end OSReconstruction
