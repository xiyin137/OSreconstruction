import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceBranchLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairTimeShellCarrier

/-!
# OS-II Axis-Pair Cutoff Boundary Integrals

Book step: OS II V.1 `(5.7)`--`(5.8)`, after the Lemma 5.1 local
Malgrange-Zerner branch has been selected.  The source-side cutoff CLM
convergence is already checked; this file proves the nontrivial last
transport needed by local EOW: if the cutoff is one on the real test support,
the CLM convergence is exactly convergence of the uncut moving side-branch
integrals.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Positive side: source-side cutoff CLM convergence gives the uncut moving
branch-integral boundary value on every test selected by the product cutoff
and supported where the branch cutoff is one. -/
theorem osiiAxisPair_positiveSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
                F τ)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    exists_axisPair_positiveSide_cutoffBranchCLMs_timeSchwartz_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
    F hχ_one hF_window
  rcases
    hpacket hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
      F hχ_one with
    ⟨T, Tseq, htend, hT_formula, hTseq_formula⟩
  let K0 : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have htarget :
      T F =
        ∫ τ : Fin (d + 1) → ℝ, K0 τ * F τ := by
    calc
      T F =
          ∫ τ : Fin (d + 1) → ℝ,
            (χbranch τ * K0 τ) * F τ := by
          simpa [K0] using hT_formula F
      _ =
          ∫ τ : Fin (d + 1) → ℝ, K0 τ * F τ := by
          refine
            integral_mul_eq_of_eqOn_tsupport
              (fun τ : Fin (d + 1) → ℝ => χbranch τ * K0 τ)
              K0
              (F : (Fin (d + 1) → ℝ) → ℂ)
              ?_
          intro τ hτ
          simp [hχ_one_window τ (hF_window hτ)]
  have hseq :
      (fun y : Fin (d + 1) → ℝ => Tseq y F)
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
            F τ) := by
    filter_upwards [hTseq_formula] with y hy
    let Ky : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T0 ξ
        (fun ν : Fin (d + 1) =>
          ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))
    calc
      Tseq y F =
          ∫ τ : Fin (d + 1) → ℝ,
            (χbranch τ * Ky τ) * F τ := by
          simpa [Ky] using hy F
      _ =
          ∫ τ : Fin (d + 1) → ℝ, Ky τ * F τ := by
          refine
            integral_mul_eq_of_eqOn_tsupport
              (fun τ : Fin (d + 1) → ℝ => χbranch τ * Ky τ)
              Ky
              (F : (Fin (d + 1) → ℝ) → ℂ)
              ?_
          intro τ hτ
          simp [hχ_one_window τ (hF_window hτ)]
  simpa [K0, htarget] using (tendsto_congr' hseq).1 htend

/-- Positive side uncut moving branch-integral boundary value for compact
tests supported in the smaller axis-pair window. -/
theorem osiiAxisPair_positiveSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto_of_compact_support_in_halfWindow
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        HasCompactSupport (F : (Fin (d + 1) → ℝ) → ℂ) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion (d + 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
                F τ)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    osiiAxisPair_positiveSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hboundary⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window F hF_compact hF_pos hF_window_half
  rcases exists_axisPairWindow_productCutoffs_on_compact
      (d := d) ξ hρ hF_compact.isCompact hF_pos hF_window_half with
    ⟨χs, hχ_pos, hχ_compact, hχ_head, hχ_tail, hχ_one⟩
  have hF_window :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρ := by
    intro τ hτ ν
    exact lt_trans (hF_window_half hτ ν) (by linarith)
  exact
    hboundary hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head
      hχ_tail F hχ_one hF_window

/-- Positive side local-EOW boundary value from an eventual, support-local
side-kernel identity.

This is the collar form actually needed for the side transport: the branch
identity only has to hold for sufficiently small side height and only on the
real test support. -/
theorem osiiAxisPair_positiveSide_localEOW_boundaryIntegral_tendsto_of_eventually_side_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ))
    (Fplus : (Fin (d + 1) → ℂ) → ℂ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
          ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
            Fplus (fun ν : Fin (d + 1) =>
                (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              Fplus (fun ν : Fin (d + 1) =>
                  (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) *
                F τ)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    osiiAxisPair_positiveSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
    F hχ_one hF_window hside_eq
  have hbranch_tend :=
    hpacket hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head
      hχ_tail F hχ_one hF_window
  have heq :
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          Fplus (fun ν : Fin (d + 1) =>
              (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) *
            F τ)
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
            F τ) := by
    filter_upwards [hside_eq] with y hy
    exact
      integral_mul_eq_of_eqOn_tsupport
        (fun τ : Fin (d + 1) → ℝ =>
          Fplus (fun ν : Fin (d + 1) =>
            (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I))
        (fun τ : Fin (d + 1) → ℝ =>
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T0 ξ
            (fun ν : Fin (d + 1) =>
              ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)))
        (F : (Fin (d + 1) → ℝ) → ℂ)
        (fun τ hτ => hy τ hτ)
  exact (tendsto_congr' heq).2 hbranch_tend

/-- Positive side local-EOW boundary value from the concrete semigroup-side
kernel identity.

This is the OS II `(5.7)` transport in the form used by the local
Malgrange-Zerner branch: a support-local equality with the finite-height
semigroup scalar, together with the time-shell carrier collar, gives the
moving local-EOW side integral boundary value.  The cutoff radius and the
branch-carrier radius are kept separate because they come from different
parts of the proof. -/
theorem osiiAxisPair_positiveSide_localEOW_boundaryIntegral_tendsto_of_semigroup_side_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ))
    (Fplus : (Fin (d + 1) → ℂ) → ℂ) :
    ∃ ρcut ρtest C : ℝ, 0 < ρcut ∧ 0 < ρtest ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρcut →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρcut,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρcut) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρcut) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρtest →
        (∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
          ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
            Fplus (fun ν : Fin (d + 1) =>
                (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single r g hg_ord)
                (((τ 0 + y 0 : ℝ) : ℂ))) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              Fplus (fun ν : Fin (d + 1) =>
                  (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) *
                F τ)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    osiiAxisPair_positiveSide_localEOW_boundaryIntegral_tendsto_of_eventually_side_eq
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos χbranch hχbranch_compact Fplus with
    ⟨ρcut, C, hρcut, hC, hboundary⟩
  rcases
    osiiAxisPair_realWindow_shiftedTimeShellBranch_eq_semigroup_time
      (d := d) OS lgc f hf_ord g hg_ord T0 hT0 ξ hξ0 with
    ⟨ρbranch, hρbranch, hbranch⟩
  let ρtest : ℝ := min ρcut (ρbranch / 2)
  refine ⟨ρcut, ρtest, C, hρcut, ?_, hC, ?_⟩
  · exact lt_min hρcut (half_pos hρbranch)
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
    F hχ_one hF_window hsem
  have hF_window_cut :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρcut := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hF_window hτ ν)
      (min_le_left ρcut (ρbranch / 2))
  have hF_window_half :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ (ρbranch / 2) := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hF_window hτ ν)
      (min_le_right ρcut (ρbranch / 2))
  have hwin :=
    osiiAxisPair_eventually_positive_shifted_tsupport_mem_timeShellWindow
      (d := d) ξ hρbranch F hF_window_half hCside_pos
  have hside_eq :
      ∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
        ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          Fplus (fun ν : Fin (d + 1) =>
              (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) := by
    filter_upwards [hsem, hwin] with y hysem hywin τ hτ
    calc
      Fplus (fun ν : Fin (d + 1) =>
          (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I)
          =
        OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)
          (((τ 0 + y 0 : ℝ) : ℂ)) := hysem τ hτ
      _ =
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T0 ξ
          (fun ν : Fin (d + 1) =>
            ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) :=
          (hbranch τ (y 0) (hywin τ hτ)).symm
  exact
    hboundary hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head
      hχ_tail F hχ_one hF_window_cut hside_eq

/-- Lower side: the same cutoff-CLM handoff with the negative side height
written as the positive semigroup displacement `-y 0`. -/
theorem osiiAxisPair_lowerSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
                F τ)
          (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    exists_axisPair_lowerSide_cutoffBranchCLMs_timeSchwartz_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
    F hχ_one hF_window
  rcases
    hpacket hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
      F hχ_one with
    ⟨T, Tseq, htend, hT_formula, hTseq_formula⟩
  let K0 : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have htarget :
      T F =
        ∫ τ : Fin (d + 1) → ℝ, K0 τ * F τ := by
    calc
      T F =
          ∫ τ : Fin (d + 1) → ℝ,
            (χbranch τ * K0 τ) * F τ := by
          simpa [K0] using hT_formula F
      _ =
          ∫ τ : Fin (d + 1) → ℝ, K0 τ * F τ := by
          refine
            integral_mul_eq_of_eqOn_tsupport
              (fun τ : Fin (d + 1) → ℝ => χbranch τ * K0 τ)
              K0
              (F : (Fin (d + 1) → ℝ) → ℂ)
              ?_
          intro τ hτ
          simp [hχ_one_window τ (hF_window hτ)]
  have hseq :
      (fun y : Fin (d + 1) → ℝ => Tseq y F)
        =ᶠ[𝓝[Cminus] (0 : Fin (d + 1) → ℝ)]
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
            F τ) := by
    filter_upwards [hTseq_formula] with y hy
    let Ky : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T0 ξ
        (fun ν : Fin (d + 1) =>
          ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))
    calc
      Tseq y F =
          ∫ τ : Fin (d + 1) → ℝ,
            (χbranch τ * Ky τ) * F τ := by
          simpa [Ky] using hy F
      _ =
          ∫ τ : Fin (d + 1) → ℝ, Ky τ * F τ := by
          refine
            integral_mul_eq_of_eqOn_tsupport
              (fun τ : Fin (d + 1) → ℝ => χbranch τ * Ky τ)
              Ky
              (F : (Fin (d + 1) → ℝ) → ℂ)
              ?_
          intro τ hτ
          simp [hχ_one_window τ (hF_window hτ)]
  simpa [K0, htarget] using (tendsto_congr' hseq).1 htend

/-- Lower side uncut moving branch-integral boundary value for compact tests
supported in the smaller axis-pair window. -/
theorem osiiAxisPair_lowerSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto_of_compact_support_in_halfWindow
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        HasCompactSupport (F : (Fin (d + 1) → ℝ) → ℂ) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion (d + 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
                F τ)
          (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    osiiAxisPair_lowerSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hboundary⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window F hF_compact hF_pos hF_window_half
  rcases exists_axisPairWindow_productCutoffs_on_compact
      (d := d) ξ hρ hF_compact.isCompact hF_pos hF_window_half with
    ⟨χs, hχ_pos, hχ_compact, hχ_head, hχ_tail, hχ_one⟩
  have hF_window :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρ := by
    intro τ hτ ν
    exact lt_trans (hF_window_half hτ ν) (by linarith)
  exact
    hboundary hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head
      hχ_tail F hχ_one hF_window

/-- Lower side local-EOW boundary value from an eventual, support-local
side-kernel identity. -/
theorem osiiAxisPair_lowerSide_localEOW_boundaryIntegral_tendsto_of_eventually_side_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ))
    (Fminus : (Fin (d + 1) → ℂ) → ℂ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
          ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
            Fminus (fun ν : Fin (d + 1) =>
                (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              Fminus (fun ν : Fin (d + 1) =>
                  (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) *
                F τ)
          (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    osiiAxisPair_lowerSide_cutoffCLM_to_uncut_boundaryIntegral_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
    F hχ_one hF_window hside_eq
  have hbranch_tend :=
    hpacket hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head
      hχ_tail F hχ_one hF_window
  have heq :
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          Fminus (fun ν : Fin (d + 1) =>
              (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) *
            F τ)
        =ᶠ[𝓝[Cminus] (0 : Fin (d + 1) → ℝ)]
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
            F τ) := by
    filter_upwards [hside_eq] with y hy
    exact
      integral_mul_eq_of_eqOn_tsupport
        (fun τ : Fin (d + 1) → ℝ =>
          Fminus (fun ν : Fin (d + 1) =>
            (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I))
        (fun τ : Fin (d + 1) → ℝ =>
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T0 ξ
            (fun ν : Fin (d + 1) =>
              ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)))
        (F : (Fin (d + 1) → ℝ) → ℂ)
        (fun τ hτ => hy τ hτ)
  exact (tendsto_congr' heq).2 hbranch_tend

/-- Lower side local-EOW boundary value from the concrete semigroup-side
kernel identity.  This is the OS II `(5.8)` companion to
`osiiAxisPair_positiveSide_localEOW_boundaryIntegral_tendsto_of_semigroup_side_eq`;
the positive semigroup displacement is `-y 0`. -/
theorem osiiAxisPair_lowerSide_localEOW_boundaryIntegral_tendsto_of_semigroup_side_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ))
    (Fminus : (Fin (d + 1) → ℂ) → ℂ) :
    ∃ ρcut ρtest C : ℝ, 0 < ρcut ∧ 0 < ρtest ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρcut →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρcut,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρcut) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρcut) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρtest →
        (∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
          ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
            Fminus (fun ν : Fin (d + 1) =>
                (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single r g hg_ord)
                (((τ 0 + (-y 0) : ℝ) : ℂ))) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              Fminus (fun ν : Fin (d + 1) =>
                  (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) *
                F τ)
          (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                F τ))) := by
  classical
  rcases
    osiiAxisPair_lowerSide_localEOW_boundaryIntegral_tendsto_of_eventually_side_eq
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg χbranch hχbranch_compact Fminus with
    ⟨ρcut, C, hρcut, hC, hboundary⟩
  rcases
    osiiAxisPair_realWindow_shiftedTimeShellBranch_eq_semigroup_time
      (d := d) OS lgc f hf_ord g hg_ord T0 hT0 ξ hξ0 with
    ⟨ρbranch, hρbranch, hbranch⟩
  let ρtest : ℝ := min ρcut (ρbranch / 2)
  refine ⟨ρcut, ρtest, C, hρcut, ?_, hC, ?_⟩
  · exact lt_min hρcut (half_pos hρbranch)
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail
    F hχ_one hF_window hsem
  have hF_window_cut :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρcut := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hF_window hτ ν)
      (min_le_left ρcut (ρbranch / 2))
  have hF_window_half :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ (ρbranch / 2) := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hF_window hτ ν)
      (min_le_right ρcut (ρbranch / 2))
  have hwin :=
    osiiAxisPair_eventually_lower_shifted_tsupport_mem_timeShellWindow
      (d := d) ξ hρbranch F hF_window_half hCminus_neg
  have hside_eq :
      ∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
        ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          Fminus (fun ν : Fin (d + 1) =>
              (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) := by
    filter_upwards [hsem, hwin] with y hysem hywin τ hτ
    calc
      Fminus (fun ν : Fin (d + 1) =>
          (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I)
          =
        OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)
          (((τ 0 + (-y 0) : ℝ) : ℂ)) := hysem τ hτ
      _ =
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T0 ξ
          (fun ν : Fin (d + 1) =>
            ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) :=
          (hbranch τ (-y 0) (hywin τ hτ)).symm
  exact
    hboundary hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head
      hχ_tail F hχ_one hF_window_cut hside_eq

end OSReconstruction
