/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapSourcewiseMZ
















noncomputable section

open Complex Filter Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d] [NeZero k]

/-- One interleaved Chapter V.1 coordinate: a chronological gap and an
axis-pair direction. -/
abbrev osiiAxisPairMultiGapIndex (d k : ℕ) :=
  Fin k × osiiAxisPairIndex d

/-- Flatten the gap and spatial-axis coordinates, leaving the sign coordinate
explicit. -/
def osiiAxisPairMultiGapFlatten
    {α : Type*}
    (z : Fin k → osiiAxisPairIndex d → α) :
    osiiAxisPairIndex (k * d) → α :=
  fun q =>
    let p := finProdFinEquiv.symm q.1
    z p.1 (p.2, q.2)

/-- Undo `osiiAxisPairMultiGapFlatten`. -/
def osiiAxisPairMultiGapUnflatten
    {α : Type*}
    (z : osiiAxisPairIndex (k * d) → α) :
    Fin k → osiiAxisPairIndex d → α :=
  fun i a => z (finProdFinEquiv (i, a.1), a.2)

/-- Flatten one selected multi-gap coordinate. -/
def osiiAxisPairMultiGapFlattenIndex
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiAxisPairIndex (k * d) :=
  (finProdFinEquiv (q.1, q.2.1), q.2.2)

/-- Undo `osiiAxisPairMultiGapFlattenIndex`. -/
def osiiAxisPairMultiGapUnflattenIndex
    (q : osiiAxisPairIndex (k * d)) :
    osiiAxisPairMultiGapIndex d k :=
  let p := finProdFinEquiv.symm q.1
  (p.1, (p.2, q.2))

@[simp] theorem osiiAxisPairMultiGapUnflatten_flatten
    {α : Type*} (z : Fin k → osiiAxisPairIndex d → α) :
    osiiAxisPairMultiGapUnflatten
        (osiiAxisPairMultiGapFlatten z) = z := by
  funext i a
  simp [osiiAxisPairMultiGapUnflatten, osiiAxisPairMultiGapFlatten]

@[simp] theorem osiiAxisPairMultiGapFlatten_unflatten
    {α : Type*} (z : osiiAxisPairIndex (k * d) → α) :
    osiiAxisPairMultiGapFlatten
        (osiiAxisPairMultiGapUnflatten z) = z := by
  funext q
  rcases q with ⟨q, b⟩
  change
    z (finProdFinEquiv (finProdFinEquiv.symm q), b) = z (q, b)
  rw [finProdFinEquiv.apply_symm_apply]

@[simp] theorem osiiAxisPairMultiGapUnflattenIndex_flattenIndex
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiAxisPairMultiGapUnflattenIndex
        (osiiAxisPairMultiGapFlattenIndex q) = q := by
  rcases q with ⟨i, a, b⟩
  simp [osiiAxisPairMultiGapUnflattenIndex,
    osiiAxisPairMultiGapFlattenIndex]

@[simp] theorem osiiAxisPairMultiGapFlattenIndex_unflattenIndex
    (q : osiiAxisPairIndex (k * d)) :
    osiiAxisPairMultiGapFlattenIndex
        (osiiAxisPairMultiGapUnflattenIndex q) = q := by
  rcases q with ⟨q, b⟩
  change
    (finProdFinEquiv (finProdFinEquiv.symm q), b) = (q, b)
  rw [finProdFinEquiv.apply_symm_apply]

/-- Update one selected nested `(gap, direction)` coordinate. -/
def osiiAxisPairMultiGapUpdate
    {α : Type*}
    [DecidableEq α]
    (z : Fin k → osiiAxisPairIndex d → α)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : α) :
    Fin k → osiiAxisPairIndex d → α :=
  Function.update z q.1 (Function.update (z q.1) q.2 w)

omit [NeZero d] [NeZero k] in
@[simp] theorem osiiAxisPairMultiGapUnflatten_update_flatten
    {α : Type*} [DecidableEq α]
    (z : Fin k → osiiAxisPairIndex d → α)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : α) :
    osiiAxisPairMultiGapUnflatten
        (Function.update
          (osiiAxisPairMultiGapFlatten z)
          (osiiAxisPairMultiGapFlattenIndex q) w) =
      osiiAxisPairMultiGapUpdate z q w := by
  funext i a
  by_cases hi : i = q.1
  · subst i
    by_cases ha : a = q.2
    · subst a
      simp [osiiAxisPairMultiGapUnflatten,
        osiiAxisPairMultiGapFlatten,
        osiiAxisPairMultiGapFlattenIndex,
        osiiAxisPairMultiGapUpdate]
    · have hidx :
          (finProdFinEquiv (q.1, a.1), a.2) ≠
            (finProdFinEquiv (q.1, q.2.1), q.2.2) := by
        intro h
        have hpair :
            (q.1, a.1) = (q.1, q.2.1) :=
          finProdFinEquiv.injective (congrArg Prod.fst h)
        have hfst : a.1 = q.2.1 := congrArg Prod.snd hpair
        have hsnd : a.2 = q.2.2 :=
          congrArg
            (fun t : osiiAxisPairIndex (k * d) => t.2) h
        exact ha (Prod.ext hfst hsnd)
      simp [osiiAxisPairMultiGapUnflatten,
        osiiAxisPairMultiGapFlatten,
        osiiAxisPairMultiGapFlattenIndex,
        osiiAxisPairMultiGapUpdate, ha, hidx]
  · have hidx :
        (finProdFinEquiv (i, a.1), a.2) ≠
          (finProdFinEquiv (q.1, q.2.1), q.2.2) := by
      intro h
      have hpair :
          (i, a.1) = (q.1, q.2.1) :=
        finProdFinEquiv.injective (congrArg Prod.fst h)
      exact hi (congrArg Prod.fst hpair)
    simp [osiiAxisPairMultiGapUnflatten,
      osiiAxisPairMultiGapFlatten,
      osiiAxisPairMultiGapFlattenIndex,
      osiiAxisPairMultiGapUpdate, hi, hidx]

/-- Complex-linear coordinate reindexing used to transport holomorphy. -/
def osiiAxisPairMultiGapFlattenCLE :
    (Fin k → osiiAxisPairIndex d → ℂ) ≃L[ℂ]
      (osiiAxisPairIndex (k * d) → ℂ) := by
  apply LinearEquiv.toContinuousLinearEquiv
  exact
    { toFun := osiiAxisPairMultiGapFlatten
      invFun := osiiAxisPairMultiGapUnflatten
      left_inv := osiiAxisPairMultiGapUnflatten_flatten
      right_inv := osiiAxisPairMultiGapFlatten_unflatten
      map_add' := by
        intro x y
        funext q
        simp [osiiAxisPairMultiGapFlatten]
      map_smul' := by
        intro c x
        funext q
        simp [osiiAxisPairMultiGapFlatten] }

/-- Real-linear coordinate reindexing used to transport chart continuity. -/
def osiiAxisPairMultiGapFlattenCLER :
    (Fin k → osiiAxisPairIndex d → ℝ) ≃L[ℝ]
      (osiiAxisPairIndex (k * d) → ℝ) := by
  apply LinearEquiv.toContinuousLinearEquiv
  exact
    { toFun := osiiAxisPairMultiGapFlatten
      invFun := osiiAxisPairMultiGapUnflatten
      left_inv := osiiAxisPairMultiGapUnflatten_flatten
      right_inv := osiiAxisPairMultiGapFlatten_unflatten
      map_add' := by
        intro x y
        funext q
        simp [osiiAxisPairMultiGapFlatten]
      map_smul' := by
        intro c x
        funext q
        simp [osiiAxisPairMultiGapFlatten] }

@[simp] theorem osiiAxisPairMultiGapFlattenCLE_apply
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    osiiAxisPairMultiGapFlattenCLE z =
      osiiAxisPairMultiGapFlatten z :=
  rfl

@[simp] theorem osiiAxisPairMultiGapFlattenCLE_symm_apply
    (z : osiiAxisPairIndex (k * d) → ℂ) :
    (osiiAxisPairMultiGapFlattenCLE (d := d) (k := k)).symm z =
      osiiAxisPairMultiGapUnflatten z :=
  rfl

@[simp] theorem osiiAxisPairMultiGapFlattenCLER_symm_apply
    (z : osiiAxisPairIndex (k * d) → ℝ) :
    (osiiAxisPairMultiGapFlattenCLER (d := d) (k := k)).symm z =
      osiiAxisPairMultiGapUnflatten z :=
  rfl

omit [NeZero d] [NeZero k] in
theorem osiiAxisPairMultiGapFlatten_realEmbed
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairMultiGapFlatten
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      osiiAxisPairLogRealEmbed
        (osiiAxisPairMultiGapFlatten x) := by
  funext q
  simp [osiiAxisPairMultiGapFlatten,
    osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed]

omit [NeZero d] [NeZero k] in
theorem osiiAxisPairMultiGapUnflatten_realEmbed
    (x : osiiAxisPairIndex (k * d) → ℝ) :
    osiiAxisPairMultiGapUnflatten
        (osiiAxisPairLogRealEmbed x) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiAxisPairMultiGapUnflatten x) := by
  funext i a
  simp [osiiAxisPairMultiGapUnflatten,
    osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed]

omit [NeZero d] [NeZero k] in
theorem osiiAxisPairMultiGap_sum_abs_im_flatten
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    (∑ q : osiiAxisPairIndex (k * d),
        |(osiiAxisPairMultiGapFlatten z q).im|) =
      ∑ i : Fin k, ∑ a : osiiAxisPairIndex d, |(z i a).im| := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ q : Fin (k * d), ∑ b : Bool,
        |(osiiAxisPairMultiGapFlatten z (q, b)).im|) =
      ∑ p : Fin k × Fin d, ∑ b : Bool, |(z p.1 (p.2, b)).im| := by
        symm
        refine Fintype.sum_equiv finProdFinEquiv
          (fun p : Fin k × Fin d =>
            ∑ b : Bool, |(z p.1 (p.2, b)).im|)
          (fun q : Fin (k * d) =>
            ∑ b : Bool,
              |(osiiAxisPairMultiGapFlatten z (q, b)).im|)
          ?_
        intro p
        simp [osiiAxisPairMultiGapFlatten]
    _ = ∑ i : Fin k, ∑ a : osiiAxisPairIndex d, |(z i a).im| := by
      rw [Fintype.sum_prod_type]
      simp only [Prod.fst, Prod.snd]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Fintype.sum_prod_type]

/-- Flattening identifies the Chapter V.1 global `l1` carrier with the
already-proved finite axis-pair MZ carrier. -/
theorem osiiAxisPairMultiGapFlatten_mem_logDomain_iff
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    osiiAxisPairMultiGapFlatten z ∈
        osiiAxisPairLogDomain (d := k * d) ↔
      z ∈ osiiAxisPairMultiGapLogDomain d k := by
  simp only [osiiAxisPairLogDomain, osiiAxisPairMultiGapLogDomain,
    Set.mem_setOf_eq]
  rw [osiiAxisPairMultiGap_sum_abs_im_flatten]

/-- One selected multi-gap logarithmic strip. -/
def osiiAxisPairMultiGapCoordinateLogStrip
    (q : osiiAxisPairMultiGapIndex d k) :
    Set (Fin k → osiiAxisPairIndex d → ℂ) :=
  {z | |(z q.1 q.2).im| < Real.pi / 2}

/-- The exact interleaved directional data consumed by Chapter V.1.

The fields are the multi-gap analogues of
`OSIIAxisPairDirectionalBranchFamily` plus the chart continuity needed by the
Gaussian MZ promotion. -/
structure OSIIAxisPairMultiGapFlatCrossData
    (d k : ℕ) [NeZero d] [NeZero k] where
  branch :
    (Fin k → osiiAxisPairIndex d → ℝ) →
      osiiAxisPairMultiGapIndex d k →
        (Fin k → osiiAxisPairIndex d → ℂ) → ℂ
  realEdge :
    (Fin k → osiiAxisPairIndex d → ℝ) → ℂ
  branch_differentiableOn :
    ∀ x q, DifferentiableOn ℂ (branch x q)
      (osiiAxisPairMultiGapCoordinateLogStrip q)
  branch_congr_of_eq_off_selected :
    ∀ {x y} q,
      (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
        branch x q = branch y q
  branch_real_edge :
    ∀ x q,
      branch x q (osiiAxisPairSimultaneousLogRealEmbed x) =
        realEdge x
  chart_continuous :
    ∀ q,
      ContinuousOn
        (fun p :
            (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
          branch p.1 q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed p.1) q p.2))
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})

namespace OSIIAxisPairMultiGapFlatCrossData

private theorem ne_flattenIndex_of_ne
    {p q : osiiAxisPairMultiGapIndex d k}
    (hpq : p ≠ q) :
    osiiAxisPairMultiGapFlattenIndex p ≠
      osiiAxisPairMultiGapFlattenIndex q := by
  intro h
  apply hpq
  rw [← osiiAxisPairMultiGapUnflattenIndex_flattenIndex p,
    ← osiiAxisPairMultiGapUnflattenIndex_flattenIndex q, h]

/-- Reindex an interleaved multi-gap cross as the finite axis-pair cross
already handled by the Gaussian MZ theorem. -/
def toFlattenedFlatCrossData
    (P : OSIIAxisPairMultiGapFlatCrossData d k) :
    OSIIAxisPairFlatCrossData (k * d) := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let F : OSIIAxisPairDirectionalBranchFamily (k * d) :=
    { branch := fun x q z =>
        P.branch
          (osiiAxisPairMultiGapUnflatten x)
          (osiiAxisPairMultiGapUnflattenIndex q)
          (osiiAxisPairMultiGapUnflatten z)
      realEdge := fun x =>
        P.realEdge (osiiAxisPairMultiGapUnflatten x)
      branch_differentiableOn := by
        intro x q
        apply
          (P.branch_differentiableOn
            (osiiAxisPairMultiGapUnflatten x)
            (osiiAxisPairMultiGapUnflattenIndex q)).comp
            (osiiAxisPairMultiGapFlattenCLE (d := d) (k := k)).symm.differentiable.differentiableOn
        intro z hz
        change
          |(z (osiiAxisPairMultiGapFlattenIndex
            (osiiAxisPairMultiGapUnflattenIndex q))).im| <
            Real.pi / 2
        rw [osiiAxisPairMultiGapFlattenIndex_unflattenIndex]
        exact hz
      branch_congr_of_eq_off_selected := by
        intro x y q hxy
        have hbranch :
            P.branch
                (osiiAxisPairMultiGapUnflatten x)
                (osiiAxisPairMultiGapUnflattenIndex q) =
              P.branch
                (osiiAxisPairMultiGapUnflatten y)
                (osiiAxisPairMultiGapUnflattenIndex q) := by
          apply P.branch_congr_of_eq_off_selected
          intro p hp
          apply hxy
          have hne :
              osiiAxisPairMultiGapFlattenIndex p ≠ q := by
            rw [← osiiAxisPairMultiGapFlattenIndex_unflattenIndex q]
            exact ne_flattenIndex_of_ne hp
          exact hne
        exact congrArg
          (fun f =>
            fun z => f (osiiAxisPairMultiGapUnflatten z))
          hbranch
      branch_real_edge := by
        intro x q
        simpa [osiiAxisPairMultiGapUnflatten_realEmbed] using
          P.branch_real_edge
            (osiiAxisPairMultiGapUnflatten x)
            (osiiAxisPairMultiGapUnflattenIndex q) }
  refine
    { family := F
      chart_continuous := ?_ }
  intro q
  let uq := osiiAxisPairMultiGapUnflattenIndex q
  let pull :
      ((osiiAxisPairIndex (k * d) → ℝ) × ℂ) →
        ((Fin k → osiiAxisPairIndex d → ℝ) × ℂ) :=
    fun p => (osiiAxisPairMultiGapUnflatten p.1, p.2)
  have hpull : Continuous pull := by
    exact Continuous.prodMk
      ((osiiAxisPairMultiGapFlattenCLER
        (d := d) (k := k)).symm.continuous.comp continuous_fst)
      continuous_snd
  have hmaps :
      Set.MapsTo pull
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  have hcont :=
    (P.chart_continuous uq).comp hpull.continuousOn hmaps
  refine hcont.congr ?_
  intro p hp
  have hflat :=
    F.flatTubeBranch_coordinate_line_eq_branch p.1 q hp.2
  dsimp only [Function.comp_apply]
  change
    F.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed p.1) q p.2) =
      P.branch
        (osiiAxisPairMultiGapUnflatten p.1) uq
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiAxisPairMultiGapUnflatten p.1)) uq p.2)
  rw [hflat]
  change
    P.branch
        (osiiAxisPairMultiGapUnflatten p.1) uq
        (osiiAxisPairMultiGapUnflatten
          (Function.update (osiiAxisPairLogRealEmbed p.1) q p.2)) =
      P.branch
        (osiiAxisPairMultiGapUnflatten p.1) uq
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiAxisPairMultiGapUnflatten p.1)) uq p.2)
  rw [show q = osiiAxisPairMultiGapFlattenIndex uq by
    simp [uq]]
  have hbase :
      osiiAxisPairLogRealEmbed p.1 =
        osiiAxisPairMultiGapFlatten
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiAxisPairMultiGapUnflatten p.1)) := by
    rw [osiiAxisPairMultiGapFlatten_realEmbed]
    rw [osiiAxisPairMultiGapFlatten_unflatten]
  rw [hbase]
  rw [osiiAxisPairMultiGapUnflatten_update_flatten]

/-- A holomorphic multi-gap continuation with the prescribed common real
edge agrees with the supplied semigroup branch along every selected
coordinate line. -/
theorem coordinateLine_eq_of_holomorphic_realEdge
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (Gamma : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma
        (osiiAxisPairMultiGapLogDomain d k))
    (hreal :
      ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
          P.realEdge x)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    Set.EqOn
      (fun w : ℂ =>
        Gamma
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w))
      (fun w : ℂ =>
        P.branch x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w))
      {w : ℂ | |w.im| < Real.pi / 2} := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := P.toFlattenedFlatCrossData
  let GammaFlat : (osiiAxisPairIndex (k * d) → ℂ) → ℂ :=
    fun z => Gamma (osiiAxisPairMultiGapUnflatten z)
  have hGammaFlat :
      DifferentiableOn ℂ GammaFlat
        (osiiAxisPairLogDomain (d := k * d)) := by
    apply hGamma.comp
      (osiiAxisPairMultiGapFlattenCLE
        (d := d) (k := k)).symm.differentiable.differentiableOn
    intro z hz
    apply
      (osiiAxisPairMultiGapFlatten_mem_logDomain_iff
        (osiiAxisPairMultiGapUnflatten z)).1
    simpa using hz
  have hrealFlat :
      ∀ y : osiiAxisPairIndex (k * d) → ℝ,
        GammaFlat (osiiAxisPairLogRealEmbed y) =
          X.family.realEdge y := by
    intro y
    change
      Gamma
          (osiiAxisPairMultiGapUnflatten
            (osiiAxisPairLogRealEmbed y)) =
        X.family.realEdge y
    rw [osiiAxisPairMultiGapUnflatten_realEmbed]
    simpa [X, toFlattenedFlatCrossData] using
      hreal (osiiAxisPairMultiGapUnflatten y)
  intro w hw
  have hlineSet :=
    X.family.coordinateLine_eq_of_holomorphic_realEdge
      GammaFlat hGammaFlat hrealFlat
      (osiiAxisPairMultiGapFlatten x)
      (osiiAxisPairMultiGapFlattenIndex q)
  have hline :
      GammaFlat
          (Function.update
            (osiiAxisPairLogRealEmbed
              (osiiAxisPairMultiGapFlatten x))
            (osiiAxisPairMultiGapFlattenIndex q) w) =
        X.family.flatTubeBranch
          (Function.update
            (osiiAxisPairLogRealEmbed
              (osiiAxisPairMultiGapFlatten x))
            (osiiAxisPairMultiGapFlattenIndex q) w) := by
    apply hlineSet
    change |w.im| < Real.pi / 2
    exact hw
  have hbase :
      osiiAxisPairLogRealEmbed
          (osiiAxisPairMultiGapFlatten x) =
        osiiAxisPairMultiGapFlatten
          (osiiAxisPairSimultaneousLogRealEmbed x) := by
    exact (osiiAxisPairMultiGapFlatten_realEmbed x).symm
  have hlineUnflatten :
      osiiAxisPairMultiGapUnflatten
          (Function.update
            (osiiAxisPairLogRealEmbed
              (osiiAxisPairMultiGapFlatten x))
            (osiiAxisPairMultiGapFlattenIndex q) w) =
        osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w := by
    rw [hbase]
    exact osiiAxisPairMultiGapUnflatten_update_flatten
      (osiiAxisPairSimultaneousLogRealEmbed x) q w
  calc
    Gamma
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w) =
      GammaFlat
        (Function.update
          (osiiAxisPairLogRealEmbed
            (osiiAxisPairMultiGapFlatten x))
          (osiiAxisPairMultiGapFlattenIndex q) w) := by
            change
              Gamma
                  (osiiAxisPairMultiGapUpdate
                    (osiiAxisPairSimultaneousLogRealEmbed x) q w) =
                Gamma
                  (osiiAxisPairMultiGapUnflatten
                    (Function.update
                      (osiiAxisPairLogRealEmbed
                        (osiiAxisPairMultiGapFlatten x))
                      (osiiAxisPairMultiGapFlattenIndex q) w))
            rw [hlineUnflatten]
    _ = X.family.flatTubeBranch
        (Function.update
          (osiiAxisPairLogRealEmbed
            (osiiAxisPairMultiGapFlatten x))
          (osiiAxisPairMultiGapFlattenIndex q) w) := hline
    _ = X.family.branch
        (osiiAxisPairMultiGapFlatten x)
        (osiiAxisPairMultiGapFlattenIndex q)
        (Function.update
          (osiiAxisPairLogRealEmbed
            (osiiAxisPairMultiGapFlatten x))
          (osiiAxisPairMultiGapFlattenIndex q) w) :=
      X.family.flatTubeBranch_coordinate_line_eq_branch
        (osiiAxisPairMultiGapFlatten x)
        (osiiAxisPairMultiGapFlattenIndex q) hw
    _ = P.branch x q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w) := by
            simp only [X, toFlattenedFlatCrossData]
            rw [hlineUnflatten]
            simp

/-- A multi-gap flat cross has a holomorphic continuation on the global
Chapter V.1 `l1` carrier once its real edge and all coordinate charts have
uniform bounds. -/
theorem exists_holomorphic_realEdge_extension_of_bounds
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (B : ℝ)
    (hB : ∀ x, ‖P.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 < C)
    (hchart :
      ∀ q : osiiAxisPairMultiGapIndex d k,
        ∀ (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖P.branch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤ C) :
    ∃ Gamma : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ,
      DifferentiableOn ℂ Gamma
        (osiiAxisPairMultiGapLogDomain d k) ∧
      ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
          P.realEdge x := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := P.toFlattenedFlatCrossData
  have hBflat :
      ∀ x : osiiAxisPairIndex (k * d) → ℝ,
        ‖X.family.realEdge x‖ ≤ B := by
    intro x
    simpa [X, toFlattenedFlatCrossData] using
      hB (osiiAxisPairMultiGapUnflatten x)
  have hchartFlat :
      ∀ q : osiiAxisPairIndex (k * d),
        ∀ (x : osiiAxisPairIndex (k * d) → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) q w)‖ ≤ C := by
    intro q x w hw
    rw [X.family.flatTubeBranch_coordinate_line_eq_branch x q hw]
    simp only [X, toFlattenedFlatCrossData]
    let uq := osiiAxisPairMultiGapUnflattenIndex q
    rw [show q = osiiAxisPairMultiGapFlattenIndex uq by simp [uq]]
    have hbase :
        osiiAxisPairLogRealEmbed x =
          osiiAxisPairMultiGapFlatten
            (osiiAxisPairSimultaneousLogRealEmbed
              (osiiAxisPairMultiGapUnflatten x)) := by
      rw [osiiAxisPairMultiGapFlatten_realEmbed]
      rw [osiiAxisPairMultiGapFlatten_unflatten]
    rw [hbase]
    rw [osiiAxisPairMultiGapUnflatten_update_flatten]
    simpa using
      hchart uq (osiiAxisPairMultiGapUnflatten x) w hw
  obtain ⟨G, hG, hGreal⟩ :=
    X.exists_holomorphic_realEdge_extension_of_bounds
      B hBflat C hC hchartFlat
  refine
    ⟨fun z => G (osiiAxisPairMultiGapFlatten z), ?_, ?_⟩
  · apply hG.comp
      (osiiAxisPairMultiGapFlattenCLE
        (d := d) (k := k)).differentiable.differentiableOn
    intro z hz
    exact
      (osiiAxisPairMultiGapFlatten_mem_logDomain_iff z).2 hz
  · intro x
    change
      G (osiiAxisPairMultiGapFlatten
        (osiiAxisPairSimultaneousLogRealEmbed x)) =
        P.realEdge x
    rw [osiiAxisPairMultiGapFlatten_realEmbed]
    simpa [X, toFlattenedFlatCrossData] using
      hGreal (osiiAxisPairMultiGapFlatten x)

/-- The common coordinate-chart bound also controls any multi-gap
holomorphic continuation with the prescribed real edge. -/
theorem norm_holomorphic_realEdge_extension_le
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (B : ℝ)
    (hB : ∀ x, ‖P.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 < C)
    (hchart :
      ∀ q : osiiAxisPairMultiGapIndex d k,
        ∀ (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖P.branch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤ C)
    (Gamma : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma
        (osiiAxisPairMultiGapLogDomain d k))
    (hreal :
      ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
          P.realEdge x)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    ‖Gamma z‖ ≤ C := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := P.toFlattenedFlatCrossData
  have hbound :=
    X.norm_holomorphic_realEdge_extension_le
      B
      (fun x => by
        simpa [X, toFlattenedFlatCrossData] using
          hB (osiiAxisPairMultiGapUnflatten x))
      C hC
      (by
        intro q x w hw
        rw [X.family.flatTubeBranch_coordinate_line_eq_branch x q hw]
        simp only [X, toFlattenedFlatCrossData]
        let uq := osiiAxisPairMultiGapUnflattenIndex q
        rw [show q = osiiAxisPairMultiGapFlattenIndex uq by simp [uq]]
        have hbase :
            osiiAxisPairLogRealEmbed x =
              osiiAxisPairMultiGapFlatten
                (osiiAxisPairSimultaneousLogRealEmbed
                  (osiiAxisPairMultiGapUnflatten x)) := by
          rw [osiiAxisPairMultiGapFlatten_realEmbed]
          rw [osiiAxisPairMultiGapFlatten_unflatten]
        rw [hbase]
        rw [osiiAxisPairMultiGapUnflatten_update_flatten]
        simpa using
          hchart uq (osiiAxisPairMultiGapUnflatten x) w hw)
      (fun w => Gamma (osiiAxisPairMultiGapUnflatten w))
      (by
        apply hGamma.comp
          (osiiAxisPairMultiGapFlattenCLE
            (d := d) (k := k)).symm.differentiable.differentiableOn
        intro w hw
        apply
          (osiiAxisPairMultiGapFlatten_mem_logDomain_iff
            (osiiAxisPairMultiGapUnflatten w)).1
        simpa using hw)
      (by
        intro x
        change
          Gamma
              (osiiAxisPairMultiGapUnflatten
                (osiiAxisPairLogRealEmbed x)) =
            X.family.realEdge x
        rw [osiiAxisPairMultiGapUnflatten_realEmbed]
        simpa [X, toFlattenedFlatCrossData] using
          hreal (osiiAxisPairMultiGapUnflatten x))
      (osiiAxisPairMultiGapFlatten z)
      ((osiiAxisPairMultiGapFlatten_mem_logDomain_iff z).2 hz)
  simpa using hbound

end OSIIAxisPairMultiGapFlatCrossData

namespace OSIIAxisPairMultiGapSourcewiseFlatCrossData

end OSIIAxisPairMultiGapSourcewiseFlatCrossData

end OSReconstruction
