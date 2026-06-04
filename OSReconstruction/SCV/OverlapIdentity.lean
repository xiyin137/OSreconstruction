import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.IdentityTheorem

/-!
# Identity propagation on metric-ball overlaps

Neutral SCV helpers for local analytic-continuation galleries.
-/

noncomputable section

open Topology

namespace SCV

/-- If two local representatives both agree with the same model on open
carriers, then a nonempty carrier overlap is already an open equality seed.

This is the neutral seed used for continuation-gallery sectors where the
branch provenance is literally equality with one fixed model branch. -/
theorem local_overlap_seed_of_common_model
    {E F : Type*} [TopologicalSpace E]
    {N₁ N₂ : Set E} {f₁ f₂ model : E → F}
    (hN₁_open : IsOpen N₁) (hN₂_open : IsOpen N₂)
    (hne : (N₁ ∩ N₂).Nonempty)
    (h₁ : Set.EqOn f₁ model N₁)
    (h₂ : Set.EqOn f₂ model N₂) :
    ∃ W : Set E,
      IsOpen W ∧ W.Nonempty ∧ W ⊆ N₁ ∩ N₂ ∧ Set.EqOn f₁ f₂ W := by
  refine ⟨N₁ ∩ N₂, hN₁_open.inter hN₂_open, hne, subset_rfl, ?_⟩
  intro z hz
  exact (h₁ hz.1).trans (h₂ hz.2).symm

/-- Pointed form of `local_overlap_seed_of_common_model`.

This is useful when a continuation-gallery overlap proof has already selected
the overlap point that must belong to the seed fed to a later identity-theorem
shrink. -/
theorem local_overlap_seed_at_of_common_model
    {E F : Type*} [TopologicalSpace E]
    {N₁ N₂ : Set E} {f₁ f₂ model : E → F}
    (hN₁_open : IsOpen N₁) (hN₂_open : IsOpen N₂)
    {z₀ : E} (hz₀ : z₀ ∈ N₁ ∩ N₂)
    (h₁ : Set.EqOn f₁ model N₁)
    (h₂ : Set.EqOn f₂ model N₂) :
    ∃ W : Set E,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ N₁ ∩ N₂ ∧ Set.EqOn f₁ f₂ W := by
  refine ⟨N₁ ∩ N₂, hN₁_open.inter hN₂_open, hz₀, subset_rfl, ?_⟩
  intro z hz
  exact (h₁ hz.1).trans (h₂ hz.2).symm

/-- If two product-holomorphic functions agree on a nonempty complex-open seed
inside the intersection of two metric balls, then they agree on the whole
two-ball overlap.

This is the identity-theorem step used by local continuation galleries after
the hard branch-law construction has produced the open seed. -/
theorem identity_theorem_product_inter_metric_ball_of_eqOn_open {n m : ℕ}
    {c₁ c₂ : Fin n → Fin m → ℂ} {r₁ r₂ : ℝ}
    {W : Set (Fin n → Fin m → ℂ)}
    (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂)
    {f g : (Fin n → Fin m → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c₁ r₁))
    (hg : DifferentiableOn ℂ g (Metric.ball c₂ r₂))
    (hfg : Set.EqOn f g W) :
    Set.EqOn f g (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) := by
  have hD_open : IsOpen (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hD_ne : (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂).Nonempty := by
    rcases hW_ne with ⟨z₀, hz₀W⟩
    exact ⟨z₀, hW_sub hz₀W⟩
  have hD_conn : IsConnected (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) :=
    SCV.isConnected_inter_metric_ball hD_ne
  have hfD : DifferentiableOn ℂ f (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) :=
    hf.mono (fun _ hz => hz.1)
  have hgD : DifferentiableOn ℂ g (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) :=
    hg.mono (fun _ hz => hz.2)
  exact
    identity_theorem_product_of_eqOn_open
      hD_open hD_conn hW_open hW_ne hW_sub hfD hgD hfg

/-- Difference form of
`identity_theorem_product_inter_metric_ball_of_eqOn_open`.

Once the two numerator branches and the two denominator branches agree on the
same nonempty complex-open seed, the corresponding branch differences agree on
the full two-ball overlap. -/
theorem identity_theorem_product_inter_metric_ball_sub_of_eqOn_open {n m : ℕ}
    {c₁ c₂ : Fin n → Fin m → ℂ} {r₁ r₂ : ℝ}
    {W : Set (Fin n → Fin m → ℂ)}
    (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂)
    {f₁ g₁ f₂ g₂ : (Fin n → Fin m → ℂ) → ℂ}
    (hf₁ : DifferentiableOn ℂ f₁ (Metric.ball c₁ r₁))
    (hg₁ : DifferentiableOn ℂ g₁ (Metric.ball c₁ r₁))
    (hf₂ : DifferentiableOn ℂ f₂ (Metric.ball c₂ r₂))
    (hg₂ : DifferentiableOn ℂ g₂ (Metric.ball c₂ r₂))
    (hf_eq : Set.EqOn f₁ f₂ W)
    (hg_eq : Set.EqOn g₁ g₂ W) :
    Set.EqOn
      (fun z => f₁ z - g₁ z)
      (fun z => f₂ z - g₂ z)
      (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) := by
  refine
    SCV.identity_theorem_product_inter_metric_ball_of_eqOn_open
      hW_open hW_ne hW_sub (hf₁.sub hg₁) (hf₂.sub hg₂) ?_
  intro z hz
  simp [hf_eq hz, hg_eq hz]

/-- Two-seed difference form for local continuation overlaps.

If the numerator branches agree on one complex-open seed and the denominator
branches agree on another, and both seeds contain the same point in a two-ball
overlap, then the branch differences agree on the whole two-ball overlap. -/
theorem identity_theorem_product_inter_metric_ball_sub_of_two_eqOn_open {n m : ℕ}
    {c₁ c₂ : Fin n → Fin m → ℂ} {r₁ r₂ : ℝ}
    {Wf Wg : Set (Fin n → Fin m → ℂ)} {z₀ : Fin n → Fin m → ℂ}
    (hWf_open : IsOpen Wf) (hz₀Wf : z₀ ∈ Wf)
    (hWf_sub : Wf ⊆ Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂)
    (hWg_open : IsOpen Wg) (hz₀Wg : z₀ ∈ Wg)
    (hWg_sub : Wg ⊆ Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂)
    {f₁ g₁ f₂ g₂ : (Fin n → Fin m → ℂ) → ℂ}
    (hf₁ : DifferentiableOn ℂ f₁ (Metric.ball c₁ r₁))
    (hg₁ : DifferentiableOn ℂ g₁ (Metric.ball c₁ r₁))
    (hf₂ : DifferentiableOn ℂ f₂ (Metric.ball c₂ r₂))
    (hg₂ : DifferentiableOn ℂ g₂ (Metric.ball c₂ r₂))
    (hf_eq : Set.EqOn f₁ f₂ Wf)
    (hg_eq : Set.EqOn g₁ g₂ Wg) :
    Set.EqOn
      (fun z => f₁ z - g₁ z)
      (fun z => f₂ z - g₂ z)
      (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) := by
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    SCV.exists_metric_ball_subset_inter_of_mem_open
      hWf_open hz₀Wf hWg_open hz₀Wg
  let W : Set (Fin n → Fin m → ℂ) := Metric.ball z₀ ρ
  have hW_open : IsOpen W := Metric.isOpen_ball
  have hW_ne : W.Nonempty := ⟨z₀, Metric.mem_ball_self hρ_pos⟩
  have hW_sub : W ⊆ Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂ := by
    intro z hz
    exact ⟨(hWf_sub (hρ_sub hz).1).1, (hWg_sub (hρ_sub hz).2).2⟩
  have hfW : Set.EqOn f₁ f₂ W := by
    intro z hz
    exact hf_eq (hρ_sub hz).1
  have hgW : Set.EqOn g₁ g₂ W := by
    intro z hz
    exact hg_eq (hρ_sub hz).2
  exact
    SCV.identity_theorem_product_inter_metric_ball_sub_of_eqOn_open
      hW_open hW_ne hW_sub hf₁ hg₁ hf₂ hg₂ hfW hgW

/-- All-overlap propagation for metric-ball local analytic galleries.

If each carrier is a metric ball, the representatives are holomorphic on their
carriers, and every nonempty overlap contains a complex-open seed where the two
representatives agree, then the representatives agree on every full overlap.
This is the neutral SCV step used after the branch-law construction has
produced the local seeds. -/
theorem pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds {n m : ℕ}
    {ι : Type*}
    {N : ι → Set (Fin n → Fin m → ℂ)}
    {center : ι → Fin n → Fin m → ℂ} {radius : ι → ℝ}
    (hN_ball : ∀ i, N i = Metric.ball (center i) (radius i))
    {D : ι → (Fin n → Fin m → ℂ) → ℂ}
    (hD : ∀ i, DifferentiableOn ℂ (D i) (N i))
    (hseed :
      ∀ i j, (N i ∩ N j).Nonempty →
        ∃ W : Set (Fin n → Fin m → ℂ),
          IsOpen W ∧
          W.Nonempty ∧
          W ⊆ N i ∩ N j ∧
          Set.EqOn (D i) (D j) W) :
    ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j) := by
  intro i j z hz
  by_cases hne : (N i ∩ N j).Nonempty
  · rcases hseed i j hne with
      ⟨W, hW_open, hW_ne, hW_sub, hW_eq⟩
    have hDi :
        DifferentiableOn ℂ (D i)
          (Metric.ball (center i) (radius i)) := by
      simpa [hN_ball i] using hD i
    have hDj :
        DifferentiableOn ℂ (D j)
          (Metric.ball (center j) (radius j)) := by
      simpa [hN_ball j] using hD j
    have hW_sub_ball :
        W ⊆
          Metric.ball (center i) (radius i) ∩
            Metric.ball (center j) (radius j) := by
      simpa [hN_ball i, hN_ball j] using hW_sub
    have hfull :
        Set.EqOn (D i) (D j)
          (Metric.ball (center i) (radius i) ∩
            Metric.ball (center j) (radius j)) :=
      SCV.identity_theorem_product_inter_metric_ball_of_eqOn_open
        hW_open hW_ne hW_sub_ball hDi hDj hW_eq
    exact hfull (by simpa [hN_ball i, hN_ball j] using hz)
  · exact False.elim (hne ⟨z, hz⟩)

end SCV
