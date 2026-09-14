import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapGrowthMZ

/-!
# Real translations of multi-gap logarithmic coordinates

The physical narrow-time logarithmic chart differs from its intrinsic chart
by a level-dependent real constant.  Since the multi-gap MZ domain constrains
only imaginary parts, real coordinate translations preserve that domain.

This file packages the corresponding translation of a flat cross and proves
that the selected MZ continuation of the translated cross is the pullback of
the original continuation.  It is the neutral reparametrization needed to
state centered packet-growth estimates without changing their real edge.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d] [NeZero k]

/-- Subtract a real multi-gap logarithmic shift from complex coordinates. -/
def osiiAxisPairMultiGapSubReal
    (s : Fin k → osiiAxisPairIndex d → ℝ)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    Fin k → osiiAxisPairIndex d → ℂ :=
  fun i a => z i a - (s i a : ℂ)

/-- Subtract a real multi-gap logarithmic shift from real coordinates. -/
def osiiAxisPairMultiGapSub
    (s x : Fin k → osiiAxisPairIndex d → ℝ) :
    Fin k → osiiAxisPairIndex d → ℝ :=
  fun i a => x i a - s i a

omit [NeZero d] [NeZero k] in
@[simp] theorem osiiAxisPairMultiGapSubReal_im
    (s : Fin k → osiiAxisPairIndex d → ℝ)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    (osiiAxisPairMultiGapSubReal s z i a).im = (z i a).im := by
  simp [osiiAxisPairMultiGapSubReal]

omit [NeZero d] [NeZero k] in
@[simp] theorem osiiAxisPairMultiGapSubReal_realEmbed
    (s x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairMultiGapSubReal s
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiAxisPairMultiGapSub s x) := by
  funext i a
  simp [osiiAxisPairMultiGapSubReal, osiiAxisPairMultiGapSub,
    osiiAxisPairSimultaneousLogRealEmbed, osiiAxisPairLogRealEmbed]

omit [NeZero d] [NeZero k] in
theorem osiiAxisPairMultiGapSubReal_mem_logDomain_iff
    (s : Fin k → osiiAxisPairIndex d → ℝ)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    osiiAxisPairMultiGapSubReal s z ∈
        osiiAxisPairMultiGapLogDomain d k ↔
      z ∈ osiiAxisPairMultiGapLogDomain d k := by
  simp only [osiiAxisPairMultiGapLogDomain, Set.mem_setOf_eq,
    osiiAxisPairMultiGapSubReal_im]

omit [NeZero d] [NeZero k] in
theorem differentiable_osiiAxisPairMultiGapSubReal
    (s : Fin k → osiiAxisPairIndex d → ℝ) :
    Differentiable ℂ (osiiAxisPairMultiGapSubReal (d := d) s) := by
  rw [differentiable_pi]
  intro i
  rw [differentiable_pi]
  intro a
  change Differentiable ℂ
    (fun z : Fin k → osiiAxisPairIndex d → ℂ =>
      z i a - (s i a : ℂ))
  fun_prop

omit [NeZero d] [NeZero k] in
@[simp] theorem osiiAxisPairMultiGapSubReal_update
    (s x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : ℂ) :
    osiiAxisPairMultiGapSubReal s
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w) =
      osiiAxisPairMultiGapUpdate
        (osiiAxisPairSimultaneousLogRealEmbed
          (osiiAxisPairMultiGapSub s x))
        q (w - (s q.1 q.2 : ℂ)) := by
  funext i a
  by_cases hi : i = q.1
  · subst i
    by_cases ha : a = q.2
    · subst a
      simp [osiiAxisPairMultiGapSubReal, osiiAxisPairMultiGapSub,
        osiiAxisPairMultiGapUpdate,
        osiiAxisPairSimultaneousLogRealEmbed, osiiAxisPairLogRealEmbed]
    · simp [osiiAxisPairMultiGapSubReal, osiiAxisPairMultiGapSub,
        osiiAxisPairMultiGapUpdate,
        osiiAxisPairSimultaneousLogRealEmbed, osiiAxisPairLogRealEmbed, ha]
  · simp [osiiAxisPairMultiGapSubReal, osiiAxisPairMultiGapSub,
      osiiAxisPairMultiGapUpdate,
      osiiAxisPairSimultaneousLogRealEmbed, osiiAxisPairLogRealEmbed, hi]

namespace OSIIAxisPairMultiGapFlatCrossData

/-- Recenter a multi-gap flat cross by subtracting one real logarithmic
coordinate vector from every complex argument. -/
def realShift
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (s : Fin k → osiiAxisPairIndex d → ℝ) :
    OSIIAxisPairMultiGapFlatCrossData d k where
  branch := fun x q z =>
    P.branch (osiiAxisPairMultiGapSub s x) q
      (osiiAxisPairMultiGapSubReal s z)
  realEdge := fun x => P.realEdge (osiiAxisPairMultiGapSub s x)
  branch_differentiableOn := by
    intro x q
    apply
      (P.branch_differentiableOn
        (osiiAxisPairMultiGapSub s x) q).comp
        (differentiable_osiiAxisPairMultiGapSubReal s).differentiableOn
    intro z hz
    simpa [osiiAxisPairMultiGapCoordinateLogStrip] using hz
  branch_congr_of_eq_off_selected := by
    intro x y q hxy
    have hbranch :
        P.branch (osiiAxisPairMultiGapSub s x) q =
          P.branch (osiiAxisPairMultiGapSub s y) q := by
      apply P.branch_congr_of_eq_off_selected
      intro p hp
      simp only [osiiAxisPairMultiGapSub]
      rw [hxy p hp]
    funext z
    exact congrFun hbranch (osiiAxisPairMultiGapSubReal s z)
  branch_real_edge := by
    intro x q
    rw [osiiAxisPairMultiGapSubReal_realEmbed]
    exact P.branch_real_edge (osiiAxisPairMultiGapSub s x) q
  chart_continuous := by
    intro q
    let pull :
        ((Fin k → osiiAxisPairIndex d → ℝ) × ℂ) →
          ((Fin k → osiiAxisPairIndex d → ℝ) × ℂ) :=
      fun p =>
        (osiiAxisPairMultiGapSub s p.1,
          p.2 - (s q.1 q.2 : ℂ))
    have hpull : Continuous pull := by
      apply Continuous.prodMk
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro a
        exact
          ((continuous_apply a).comp
            ((continuous_apply i).comp continuous_fst)).sub
              continuous_const
      · exact continuous_snd.sub continuous_const
    have hmaps :
        Set.MapsTo pull
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
      intro p hp
      refine ⟨Set.mem_univ _, ?_⟩
      change |(p.2 - (s q.1 q.2 : ℂ)).im| < Real.pi / 2
      simpa using hp.2
    refine ((P.chart_continuous q).comp hpull.continuousOn hmaps).congr ?_
    intro p hp
    dsimp only [Function.comp_apply, pull]
    rw [osiiAxisPairMultiGapSubReal_update]

@[simp] theorem realShift_branch
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (s x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    (P.realShift s).branch x q z =
      P.branch (osiiAxisPairMultiGapSub s x) q
        (osiiAxisPairMultiGapSubReal s z) :=
  rfl

@[simp] theorem realShift_realEdge
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (s x : Fin k → osiiAxisPairIndex d → ℝ) :
    (P.realShift s).realEdge x =
      P.realEdge (osiiAxisPairMultiGapSub s x) :=
  rfl

end OSIIAxisPairMultiGapFlatCrossData

namespace OSIIAxisPairMultiGapSourcewiseCoshGrowthData

/-- Recenter the flat cross and real edge of a sourcewise growth family.  A
growth proof for the shifted cross is supplied separately. -/
def realShiftFlatCross
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (s : Fin k → osiiAxisPairIndex d → ℝ) :
    (Fin n → SchwartzSpacetime d) →
      OSIIAxisPairMultiGapFlatCrossData d k :=
  fun fs => (P.flatCross fs).realShift s

/-- The original selected continuation pulled back by a real logarithmic
translation is holomorphic on the unchanged multi-gap domain. -/
theorem differentiableOn_toMZFamily_comp_subReal
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (s : Fin k → osiiAxisPairIndex d → ℝ)
    (fs : Fin n → SchwartzSpacetime d) :
    DifferentiableOn ℂ
      (fun z => P.toMZFamily.toFun fs
        (osiiAxisPairMultiGapSubReal s z))
      (osiiAxisPairMultiGapLogDomain d k) := by
  exact
    (P.toMZFamily.holomorphic fs).comp
      (differentiable_osiiAxisPairMultiGapSubReal s).differentiableOn
      (fun z hz =>
        (osiiAxisPairMultiGapSubReal_mem_logDomain_iff s z).2 hz)

/-- Any selected MZ continuation for the shifted flat cross agrees with the
pullback of the original continuation. -/
theorem toMZFamily_realShift_eq
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (s : Fin k → osiiAxisPairIndex d → ℝ)
    (Q : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (_hflat : Q.flatCross = P.realShiftFlatCross s)
    (hreal :
      ∀ x, Q.realEdge x =
        P.realEdge (osiiAxisPairMultiGapSub s x))
    (fs : Fin n → SchwartzSpacetime d)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    Q.toMZFamily.toFun fs z =
      P.toMZFamily.toFun fs
        (osiiAxisPairMultiGapSubReal s z) := by
  let F := Q.toMZFamily.toFun fs
  let G := fun w =>
    P.toMZFamily.toFun fs (osiiAxisPairMultiGapSubReal s w)
  have hF :
      DifferentiableOn ℂ F
        (osiiAxisPairMultiGapLogDomain d k) :=
    Q.toMZFamily.holomorphic fs
  have hG :
      DifferentiableOn ℂ G
        (osiiAxisPairMultiGapLogDomain d k) :=
    P.differentiableOn_toMZFamily_comp_subReal s fs
  apply
    SCV.holomorphic_eq_of_eq_on_real_of_connected_finite_product
      isOpen_osiiAxisPairMultiGapLogDomain
      isConnected_osiiAxisPairMultiGapLogDomain
      hF hG
      (x₀ := fun _ _ => 0)
      (osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap
        (fun _ _ => 0))
      ?_ z hz
  intro x _hx
  dsimp [F, G]
  change
    Q.toMZFamily.toFun fs
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      P.toMZFamily.toFun fs
        (osiiAxisPairMultiGapSubReal s
          (osiiAxisPairSimultaneousLogRealEmbed x))
  rw [Q.toMZFamily.realEdge_eq, osiiAxisPairMultiGapSubReal_realEmbed,
    P.toMZFamily.realEdge_eq]
  change Q.realEdge x fs =
    P.realEdge (osiiAxisPairMultiGapSub s x) fs
  exact DFunLike.congr_fun (hreal x) fs

end OSIIAxisPairMultiGapSourcewiseCoshGrowthData

end OSReconstruction
