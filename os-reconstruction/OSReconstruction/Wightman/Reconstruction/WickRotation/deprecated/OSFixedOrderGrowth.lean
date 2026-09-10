import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketGrowth

/-!
# Deprecated fixed-order Euclidean growth

This is the exact former public growth condition, retained only for results
that genuinely used its fixed Schwartz order. It is not the OS-II input:
normalization forces its order to be zero. The only conversion goes from
this legacy condition to the corrected arity-linear public condition.
-/

noncomputable section

open scoped BigOperators Classical

structure OSFixedOrderGrowthCondition
    (d : Nat) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  sobolev_index : Nat
  alpha : Real
  beta : Real
  gamma : Real
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  growth_estimate : ∀ (n : Nat) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : Real) ^ gamma *
      SchwartzMap.seminorm Real sobolev_index sobolev_index f.1

theorem OSFixedOrderGrowthCondition.sobolev_index_eq_zero
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSFixedOrderGrowthCondition d OS) :
    lgc.sobolev_index = 0 := by
  by_contra horder
  let factors : Fin 0 → SchwartzSpacetime d := fun i => Fin.elim0 i
  let test : SchwartzNPoint d 0 := SchwartzMap.productTensor factors
  have hvanish : VanishesToInfiniteOrderOnCoincidence test := by
    intro k x hx
    obtain ⟨i, j, hij, heq⟩ := hx
    exact Fin.elim0 i
  have hseminorm :
      SchwartzMap.seminorm Real lgc.sobolev_index lgc.sobolev_index test = 0 := by
    apply le_antisymm _ (apply_nonneg _ _)
    apply SchwartzMap.seminorm_le_bound Real _ _ test (le_refl 0)
    intro x
    have hx : ‖x‖ = 0 := by
      rw [show x = 0 from Subsingleton.elim x 0, norm_zero]
    simp [hx, zero_pow horder]
  have hnormalized : OS.S 0 ⟨test, hvanish⟩ = 1 := by
    rw [lgc.normalized_zero]
    simp [test, factors, SchwartzMap.productTensor_apply]
  have hgrowth := lgc.growth_estimate 0 ⟨test, hvanish⟩
  rw [hnormalized, hseminorm] at hgrowth
  norm_num at hgrowth

theorem OSFixedOrderGrowthCondition.growth_estimate_zero_order
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSFixedOrderGrowthCondition d OS)
    (n : Nat) (f : ZeroDiagonalSchwartz d n) :
    ‖OS.S n f‖ ≤ lgc.alpha * lgc.beta ^ n * (n.factorial : Real) ^ lgc.gamma *
      SchwartzMap.seminorm Real 0 0 f.1 := by
  simpa [lgc.sobolev_index_eq_zero] using lgc.growth_estimate n f

abbrev OSFixedOrderGrowthCondition.toArityLinearGrowthCondition
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSFixedOrderGrowthCondition d OS) :
    OSReconstruction.OSArityLinearGrowthCondition d OS where
  normalized_zero := lgc.normalized_zero
  sobolev_index := lgc.sobolev_index
  alpha := lgc.alpha
  beta := lgc.beta
  gamma := lgc.gamma
  alpha_pos := lgc.alpha_pos
  beta_pos := lgc.beta_pos
  growth_estimate := by
    intro n f
    have hindices : Finset.Iic ((0, 0) : Nat × Nat) = {(0, 0)} := by
      ext ⟨p, q⟩
      simp
    simpa [OSReconstruction.osArityLinearSchwartzSeminorm,
      lgc.sobolev_index_eq_zero, hindices] using
      lgc.growth_estimate_zero_order n f

@[simp] theorem OSFixedOrderGrowthCondition.toArityLinearGrowthCondition_sobolev_index
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSFixedOrderGrowthCondition d OS) :
    lgc.toArityLinearGrowthCondition.sobolev_index = lgc.sobolev_index := rfl

instance {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d} :
    Coe (OSFixedOrderGrowthCondition d OS) (OSLinearGrowthCondition d OS) :=
  ⟨OSFixedOrderGrowthCondition.toArityLinearGrowthCondition⟩

namespace OSReconstruction

/-- The former fixed-order Hilbert estimate is valid only for the former
fixed-order input. The general theorem is the arity-linear estimate. -/
theorem osiiPositiveTimeSingleVectorCLM_norm_sq_le_finsetSup
    {d m : Nat} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (g : SchwartzNPoint d m)
    (hg : tsupport (g : NPointDomain d m → Complex) ⊆
      OrderedPositiveTimeRegion d m) :
    let s := lgc.sobolev_index
    let t : Finset (Nat × Nat) :=
      ({0, s} : Finset Nat).product (Finset.range (s + 1))
    let Q := t.sup (schwartzSeminormFamily Real (NPointDomain d m) Complex) g
    ‖osiiPositiveTimeSingleVectorCLM OS m ⟨g, hg⟩‖ ^ 2 ≤
      (lgc.alpha * lgc.beta ^ (m + m) *
          ((m + m).factorial : Real) ^ lgc.gamma) *
        (2 ^ s * ∑ i ∈ Finset.range (s + 1),
          (s.choose i : Real) * (Q * Q + Q * Q)) := by
  have hs : lgc.sobolev_index = 0 := lgc.sobolev_index_eq_zero
  have hindices : Finset.Iic ((0, 0) : Nat × Nat) = {(0, 0)} := by
    ext ⟨p, q⟩
    simp
  have hcorrect :=
    osiiPositiveTimeSingleVectorCLM_norm_sq_le_arityLinearFinsetSup
      OS lgc.toArityLinearGrowthCondition g hg
  simpa [OSFixedOrderGrowthCondition.toArityLinearGrowthCondition,
    hs, hindices, pow_two, two_mul] using hcorrect

end OSReconstruction
