import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPairTotalBranch

/-!
# OS-II Axis-Pair A0 Bridge

This companion records the handoff from the compact axis-pair
Malgrange-Zerner real representative to the Section 4.3 product-source
pairings used by the local `(A0)->(P0)` bridge.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Product-source pairing form of the compact axis-pair real representative.

The compact representative theorem is stated for an arbitrary compact carrier
`K`.  Here `K` is the actual compact support of a Section 4.3 finite time
product source, so positivity, compactness, the open carrier, continuity, and
the pairing identity are in the shape used by the local `(A0)->(P0)` bridge. -/
theorem osiiAxisPair_timeShell_realRepresentative_productSource_pairing
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
    (T : ℝ) (hT : 0 < T)
    (gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ τ ∈ tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ),
          S_real τ =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∫ τ : Fin (d + 1) → ℝ,
            S_real τ * (section43TimeProductSource gs).f τ) =
          ∫ τ : Fin (d + 1) → ℝ,
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
              (section43TimeProductSource gs).f τ := by
  classical
  let K : Set (Fin (d + 1) → ℝ) :=
    tsupport ((section43TimeProductSource gs).f :
      (Fin (d + 1) → ℝ) → ℂ)
  have hK : IsCompact K := by
    simpa [K] using (section43TimeProductSource gs).compact.isCompact
  have hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0} := by
    intro τ hτ
    exact (section43TimeProductSource gs).positive hτ 0
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative_pairing
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos with
    ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hedge, hpair⟩
  refine ⟨Ureal, S_real, hUreal_open, ?_, hS_cont, ?_, ?_⟩
  · simpa [K] using hK_sub
  · simpa [K] using hedge
  · simpa [K] using
      hpair (section43TimeProductSource gs).f (by
        intro τ hτ
        exact hτ)

end OSReconstruction
