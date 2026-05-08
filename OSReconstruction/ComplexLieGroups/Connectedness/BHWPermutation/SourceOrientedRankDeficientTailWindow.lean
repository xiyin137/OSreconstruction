import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailRadius
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTailSmallRealization
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

/-!
# Tail windows for rank-deficient source Schur charts

The rank-deficient local-image proof uses a target-shaped tail window, not a
same-radius compatible invariant/coordinate polydisc.  The window stores a
coordinate radius for the realizing shifted-tail tuple and a residual-data
radius from the checked one-way shifted-tail realization theorem.  The
parameter set itself includes the residual-data inequalities, making forward
containment a membership condition.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Tail-window data for the source-oriented rank-deficient normal
parameters.  The `tailRealize` field is exactly the checked one-way shifted
tail realization theorem at the chosen coordinate radius. -/
structure SourceOrientedRankDeficientTailWindowChoice
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) where
  tailCoordRadius : ℝ
  tailCoordRadius_pos : 0 < tailCoordRadius
  tailEta : ℝ
  tailEta_pos : 0 < tailEta
  tailRealize :
    ∀ T : SourceShiftedTailOrientedData d r hrD (n - r),
      T ∈ sourceShiftedTailOrientedVariety d r hrD (n - r) →
      (∀ u v, ‖T.gram u v‖ < tailEta) →
      (∀ ι, ‖T.det ι‖ < tailEta) →
      ∃ q : Fin (n - r) → Fin (d + 1 - r) → ℂ,
        (∀ u μ, ‖q u μ‖ < tailCoordRadius) ∧
        sourceShiftedTailOrientedInvariant d r hrD (n - r) q = T

/-- The target-shaped tail window on normal parameters.  It combines the raw
tail-coordinate bound needed for ambient shrink estimates with the shifted
tail invariant bounds needed for forward Schur containment. -/
def sourceOrientedRankDeficientTailWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :=
  {p |
    (∀ u μ, ‖p.tail u μ‖ < Tail.tailCoordRadius) ∧
    (∀ u v,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).gram u v‖ <
        Tail.tailEta) ∧
    (∀ ι,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).det ι‖ <
        Tail.tailEta)}

/-- A finite coordinate polydisc in a two-index complex coordinate model. -/
def sourceMatrixCoordinateWindow {ι κ : Type*}
    (center : ι → κ → ℂ) (ρ : ℝ) :
    Set (ι → κ → ℂ) :=
  {x | ∀ i j, ‖x i j - center i j‖ < ρ}

theorem sourceMatrixCoordinateWindow_real_affine_sub_eq
    (a b : ℝ)
    (z w c : ℂ)
    (hab : a + b = 1) :
    a • z + b • w - c = a • (z - c) + b • (w - c) := by
  have h : (a + b : ℝ) • c = c := by
    rw [hab]
    simp
  calc
    a • z + b • w - c = a • z + b • w - (a + b : ℝ) • c := by
      rw [h]
    _ = a • z + b • w - (a • c + b • c) := by
      rw [show (a + b : ℝ) • c = a • c + b • c from add_smul a b c]
    _ = a • (z - c) + b • (w - c) := by
      rw [show a • (z - c) = a • z - a • c from smul_sub a z c]
      rw [show b • (w - c) = b • w - b • c from smul_sub b w c]
      abel

/-- Coordinate polydiscs are convex in the real affine structure. -/
theorem convex_sourceMatrixCoordinateWindow {ι κ : Type*}
    (center : ι → κ → ℂ)
    (ρ : ℝ) :
    Convex ℝ (sourceMatrixCoordinateWindow center ρ) := by
  intro x hx
  rw [starConvex_iff_segment_subset]
  intro y hy
  rw [segment_subset_iff]
  intro a b ha hb hab i j
  have hdecomp :
      (a • x + b • y) i j - center i j =
        a • (x i j - center i j) + b • (y i j - center i j) := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    exact
      sourceMatrixCoordinateWindow_real_affine_sub_eq
        a b (x i j) (y i j) (center i j) hab
  have hnorm_le :
      ‖(a • x + b • y) i j - center i j‖ ≤
        a * ‖x i j - center i j‖ +
          b * ‖y i j - center i j‖ := by
    calc
      ‖(a • x + b • y) i j - center i j‖ =
          ‖a • (x i j - center i j) +
            b • (y i j - center i j)‖ := by
            rw [hdecomp]
      _ ≤
          ‖a • (x i j - center i j)‖ +
            ‖b • (y i j - center i j)‖ :=
            norm_add_le _ _
      _ =
          |a| * ‖x i j - center i j‖ +
            |b| * ‖y i j - center i j‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs]
      _ =
          a * ‖x i j - center i j‖ +
            b * ‖y i j - center i j‖ := by
            rw [abs_of_nonneg ha, abs_of_nonneg hb]
  have hweighted :
      a * ‖x i j - center i j‖ +
          b * ‖y i j - center i j‖ < ρ := by
    have hxle :
        a * ‖x i j - center i j‖ ≤ a * ρ :=
      mul_le_mul_of_nonneg_left (le_of_lt (hx i j)) ha
    have hyle :
        b * ‖y i j - center i j‖ ≤ b * ρ :=
      mul_le_mul_of_nonneg_left (le_of_lt (hy i j)) hb
    have hsum_eq : a * ρ + b * ρ = ρ := by
      rw [← add_mul, hab, one_mul]
    by_cases ha_eq : a = 0
    · have hb_pos : 0 < b := by
        linarith
      have hylt :
          b * ‖y i j - center i j‖ < b * ρ :=
        mul_lt_mul_of_pos_left (hy i j) hb_pos
      calc
        a * ‖x i j - center i j‖ +
            b * ‖y i j - center i j‖
            < a * ρ + b * ρ :=
              add_lt_add_of_le_of_lt hxle hylt
        _ = ρ := hsum_eq
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_eq)
      have hxlt :
          a * ‖x i j - center i j‖ < a * ρ :=
        mul_lt_mul_of_pos_left (hx i j) ha_pos
      calc
        a * ‖x i j - center i j‖ +
            b * ‖y i j - center i j‖
            < a * ρ + b * ρ :=
              add_lt_add_of_lt_of_le hxlt hyle
        _ = ρ := hsum_eq
  exact lt_of_le_of_lt hnorm_le hweighted

theorem isOpen_sourceMatrixCoordinateWindow {ι κ : Type*}
    [Finite ι] [Finite κ]
    (center : ι → κ → ℂ)
    (ρ : ℝ) :
    IsOpen (sourceMatrixCoordinateWindow center ρ) := by
  simp only [sourceMatrixCoordinateWindow, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i : ι =>
    isOpen_iInter_of_finite fun j : κ =>
      isOpen_lt (by fun_prop) continuous_const

/-- Coordinate windows form a neighborhood basis at any finite two-index
coordinate point. -/
theorem exists_sourceMatrixCoordinateWindow_subset_of_mem_nhds
    {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (center : ι → κ → ℂ)
    {V : Set (ι → κ → ℂ)}
    (hV : V ∈ 𝓝 center) :
    ∃ ρ : ℝ, 0 < ρ ∧ sourceMatrixCoordinateWindow center ρ ⊆ V := by
  rcases Metric.mem_nhds_iff.mp hV with ⟨ρ, hρ, hρsub⟩
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  apply hρsub
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hρ]
  intro i
  rw [pi_norm_lt_iff hρ]
  intro j
  simpa [Pi.sub_apply] using hx i j

/-- The head-factor coordinate window around the identity matrix. -/
def sourceOrientedHeadCoordinateWindow
    (r : ℕ)
    (ρ : ℝ) :
    Set (Matrix (Fin r) (Fin r) ℂ) :=
  sourceMatrixCoordinateWindow (1 : Matrix (Fin r) (Fin r) ℂ) ρ

/-- The mixed-coordinate window around zero. -/
def sourceOrientedMixedCoordinateWindow
    (n r : ℕ)
    (ρ : ℝ) :
    Set (Matrix (Fin (n - r)) (Fin r) ℂ) :=
  sourceMatrixCoordinateWindow (0 : Matrix (Fin (n - r)) (Fin r) ℂ) ρ

theorem isOpen_sourceOrientedHeadCoordinateWindow
    (r : ℕ)
    (ρ : ℝ) :
    IsOpen (sourceOrientedHeadCoordinateWindow r ρ) := by
  simpa [sourceOrientedHeadCoordinateWindow] using
    isOpen_sourceMatrixCoordinateWindow
      (1 : Matrix (Fin r) (Fin r) ℂ) ρ

theorem isOpen_sourceOrientedMixedCoordinateWindow
    (n r : ℕ)
    (ρ : ℝ) :
    IsOpen (sourceOrientedMixedCoordinateWindow n r ρ) := by
  simpa [sourceOrientedMixedCoordinateWindow] using
    isOpen_sourceMatrixCoordinateWindow
      (0 : Matrix (Fin (n - r)) (Fin r) ℂ) ρ

theorem isConnected_sourceOrientedHeadCoordinateWindow
    (r : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsConnected (sourceOrientedHeadCoordinateWindow r ρ) := by
  exact
    (convex_sourceMatrixCoordinateWindow
      (1 : Matrix (Fin r) (Fin r) ℂ) ρ).isConnected
      ⟨(1 : Matrix (Fin r) (Fin r) ℂ), by
        intro i j
        simp [hρ]⟩

theorem isConnected_sourceOrientedMixedCoordinateWindow
    (n r : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsConnected (sourceOrientedMixedCoordinateWindow n r ρ) := by
  exact
    (convex_sourceMatrixCoordinateWindow
      (0 : Matrix (Fin (n - r)) (Fin r) ℂ) ρ).isConnected
      ⟨(0 : Matrix (Fin (n - r)) (Fin r) ℂ), by
        intro i j
        simpa using hρ⟩

@[simp]
theorem sourceTailEmbed_smul
    (d r : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin (d + 1 - r) → ℂ) :
    sourceTailEmbed d r hrD (fun μ => a * q μ) =
      fun μ => a * sourceTailEmbed d r hrD q μ := by
  ext μ
  by_cases h : r ≤ μ.val
  · simp [sourceTailEmbed, h]
  · simp [sourceTailEmbed, h]

@[simp]
theorem sourceShiftedTailGram_smul
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (u v : Fin m) :
    sourceShiftedTailGram d r hrD m (fun u μ => a * q u μ) u v =
      a * a * sourceShiftedTailGram d r hrD m q u v := by
  rw [sourceShiftedTailGram_apply, sourceShiftedTailGram_apply]
  rw [sourceTailEmbed_smul, sourceTailEmbed_smul]
  rw [sourceVectorMinkowskiInner_smul_left, sourceVectorMinkowskiInner_smul_right]
  ring

@[simp]
theorem sourceShiftedTailOrientedInvariant_smul_gram
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (u v : Fin m) :
    (sourceShiftedTailOrientedInvariant d r hrD m
        (fun u μ => a * q u μ)).gram u v =
      a * a * (sourceShiftedTailOrientedInvariant d r hrD m q).gram u v := by
  exact sourceShiftedTailGram_smul d r m hrD a q u v

@[simp]
theorem sourceShiftedTailOrientedInvariant_smul_det
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1 - r) ↪ Fin m) :
    (sourceShiftedTailOrientedInvariant d r hrD m
        (fun u μ => a * q u μ)).det ι =
      a ^ (d + 1 - r) *
        (sourceShiftedTailOrientedInvariant d r hrD m q).det ι := by
  let M : Matrix (Fin (d + 1 - r)) (Fin (d + 1 - r)) ℂ :=
    fun u μ => q (ι u) μ
  change (a • M).det = a ^ (d + 1 - r) * M.det
  rw [Matrix.det_smul]
  simp

/-- Scaling a tail tuple toward zero preserves membership in the target-shaped
tail window inequalities. -/
theorem sourceShiftedTailWindow_scaled
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    {q : Fin (n - r) → Fin (d + 1 - r) → ℂ}
    (hq_coord : ∀ u μ, ‖q u μ‖ < Tail.tailCoordRadius)
    (hq_gram :
      ∀ u v,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ <
          Tail.tailEta)
    (hq_det :
      ∀ ι,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ <
          Tail.tailEta)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 1) :
    (∀ u μ, ‖(t : ℂ) * q u μ‖ < Tail.tailCoordRadius) ∧
      (∀ u v,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).gram u v‖ < Tail.tailEta) ∧
      (∀ ι,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).det ι‖ < Tail.tailEta) := by
  have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    exact ht_le
  constructor
  · intro u μ
    calc
      ‖(t : ℂ) * q u μ‖ = ‖(t : ℂ)‖ * ‖q u μ‖ := norm_mul _ _
      _ ≤ 1 * ‖q u μ‖ := mul_le_mul_of_nonneg_right ht_norm (norm_nonneg _)
      _ = ‖q u μ‖ := one_mul _
      _ < Tail.tailCoordRadius := hq_coord u μ
  constructor
  · intro u v
    calc
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).gram u v‖ =
          ‖(t : ℂ) * (t : ℂ) *
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            rw [sourceShiftedTailOrientedInvariant_smul_gram]
      _ = ‖(t : ℂ)‖ * ‖(t : ℂ)‖ *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            rw [norm_mul, norm_mul, mul_assoc]
      _ ≤ 1 * 1 *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            gcongr
      _ = ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            ring
      _ < Tail.tailEta := hq_gram u v
  · intro ι
    have hpow_norm : ‖(t : ℂ) ^ (d + 1 - r)‖ ≤ 1 := by
      calc
        ‖(t : ℂ) ^ (d + 1 - r)‖ = ‖(t : ℂ)‖ ^ (d + 1 - r) := norm_pow _ _
        _ ≤ 1 ^ (d + 1 - r) := pow_le_pow_left₀ (norm_nonneg _) ht_norm _
        _ = 1 := one_pow _
    calc
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).det ι‖ =
          ‖(t : ℂ) ^ (d + 1 - r) *
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ := by
            rw [sourceShiftedTailOrientedInvariant_smul_det]
      _ = ‖(t : ℂ) ^ (d + 1 - r)‖ *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ :=
            norm_mul _ _
      _ ≤ 1 *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ := by
            exact mul_le_mul_of_nonneg_right hpow_norm (norm_nonneg _)
      _ = ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ :=
            one_mul _
      _ < Tail.tailEta := hq_det ι

/-- The target-shaped window on shifted-tail tuples alone. -/
def sourceShiftedTailTupleWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (Fin (n - r) → Fin (d + 1 - r) → ℂ) :=
  {q |
    (∀ u μ, ‖q u μ‖ < Tail.tailCoordRadius) ∧
    (∀ u v,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ <
        Tail.tailEta) ∧
    (∀ ι,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ <
        Tail.tailEta)}

/-- The shifted-tail tuple window is connected: it is star-shaped from zero. -/
theorem isConnected_sourceShiftedTailTupleWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsConnected (sourceShiftedTailTupleWindow d n r hrD hrn Tail) := by
  have hzero : (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ) ∈
      sourceShiftedTailTupleWindow d n r hrD hrn Tail := by
    constructor
    · intro u μ
      simp [Tail.tailCoordRadius_pos]
    constructor
    · intro u v
      simp [sourceShiftedTailOrientedInvariant, sourceShiftedTailGram,
        sourceVectorMinkowskiInner, Tail.tailEta_pos]
    · intro ι
      have hDtail : 0 < d + 1 - r := by omega
      have hnonempty : Nonempty (Fin (d + 1 - r)) :=
        Fin.pos_iff_nonempty.mp hDtail
      have hdet0 :
          (sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)).det ι = 0 := by
        simpa [sourceShiftedTailOrientedInvariant] using
          (Matrix.det_zero (n := Fin (d + 1 - r)) (R := ℂ) hnonempty)
      rw [hdet0, norm_zero]
      exact Tail.tailEta_pos
  have hstar : StarConvex ℝ
      (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)
      (sourceShiftedTailTupleWindow d n r hrD hrn Tail) := by
    rw [starConvex_iff_segment_subset]
    intro q hq
    rw [segment_subset_iff]
    intro a b ha0 hb0 hab
    have hb1 : b ≤ 1 := by linarith
    dsimp [sourceShiftedTailTupleWindow] at hq ⊢
    have hscaled :=
      sourceShiftedTailWindow_scaled d n r hrD hrn Tail
        hq.1 hq.2.1 hq.2.2 hb0 hb1
    have hseg :
        a • (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ) + b • q =
          fun u μ => (b : ℂ) * q u μ := by
      ext u μ
      simp
    simpa [hseg] using hscaled
  exact (hstar.isPathConnected hzero).isConnected

/-- The shifted-tail tuple window is open in finite coordinates. -/
theorem isOpen_sourceShiftedTailTupleWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen (sourceShiftedTailTupleWindow d n r hrD hrn Tail) := by
  have hcoord_open :
      IsOpen {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        ∀ u μ, ‖q u μ‖ < Tail.tailCoordRadius} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun u : Fin (n - r) =>
      isOpen_iInter_of_finite fun μ : Fin (d + 1 - r) =>
        isOpen_lt
          (continuous_norm.comp
            ((continuous_apply μ).comp (continuous_apply u)))
          continuous_const
  have hgram_open :
      IsOpen {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        ∀ u v,
          ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ <
            Tail.tailEta} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun u : Fin (n - r) =>
      isOpen_iInter_of_finite fun v : Fin (n - r) => by
        have hgram_q :
            Continuous (fun q : Fin (n - r) → Fin (d + 1 - r) → ℂ =>
              (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v) := by
          simpa [sourceShiftedTailOrientedInvariant] using
            (continuous_apply v).comp
              ((continuous_apply u).comp
                (continuous_sourceShiftedTailGram d r (n - r) hrD))
        exact isOpen_lt (continuous_norm.comp hgram_q) continuous_const
  have hdet_open :
      IsOpen {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        ∀ ι,
          ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ <
            Tail.tailEta} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun ι : Fin (d + 1 - r) ↪ Fin (n - r) => by
      have hdet_q :
          Continuous (fun q : Fin (n - r) → Fin (d + 1 - r) → ℂ =>
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι) := by
        fun_prop
      exact isOpen_lt (continuous_norm.comp hdet_q) continuous_const
  simpa [sourceShiftedTailTupleWindow, Set.setOf_and] using
    hcoord_open.inter (hgram_open.inter hdet_open)

/-- The tail window is open in the finite normal-parameter topology. -/
theorem isOpen_sourceOrientedRankDeficientTailWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen (sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail) := by
  let P := SourceOrientedRankDeficientNormalParameter d n r hrD hrn
  have htail_cont : Continuous (fun p : P => p.tail) :=
    continuous_sourceOrientedNormalParameter_tail
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have hcoord_open :
      IsOpen {p : P | ∀ u μ, ‖p.tail u μ‖ < Tail.tailCoordRadius} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun u : Fin (n - r) =>
      isOpen_iInter_of_finite fun μ : Fin (d + 1 - r) =>
        isOpen_lt
          ((continuous_norm.comp
            ((continuous_apply μ).comp ((continuous_apply u).comp htail_cont))))
          continuous_const
  have hgram_open :
      IsOpen {p : P |
        ∀ u v,
          ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).gram u v‖ <
            Tail.tailEta} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun u : Fin (n - r) =>
      isOpen_iInter_of_finite fun v : Fin (n - r) => by
        have hgram_q :
            Continuous (fun q : Fin (n - r) → Fin (d + 1 - r) → ℂ =>
              (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v) := by
          simpa [sourceShiftedTailOrientedInvariant] using
            (continuous_apply v).comp
              ((continuous_apply u).comp
                (continuous_sourceShiftedTailGram d r (n - r) hrD))
        exact
          isOpen_lt (continuous_norm.comp (hgram_q.comp htail_cont))
            continuous_const
  have hdet_open :
      IsOpen {p : P |
        ∀ ι,
          ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).det ι‖ <
            Tail.tailEta} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun ι : Fin (d + 1 - r) ↪ Fin (n - r) => by
      have hdet_q :
          Continuous (fun q : Fin (n - r) → Fin (d + 1 - r) → ℂ =>
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι) := by
        fun_prop
      exact
        isOpen_lt (continuous_norm.comp (hdet_q.comp htail_cont))
          continuous_const
  simpa [sourceOrientedRankDeficientTailWindow, Set.setOf_and] using
    hcoord_open.inter (hgram_open.inter hdet_open)

/-- The normal center lies in every positive tail window. -/
theorem sourceOrientedNormalCenterParameter_mem_tailWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    sourceOrientedNormalCenterParameter d n r hrD hrn ∈
      sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail := by
  constructor
  · intro u μ
    simp [sourceOrientedNormalCenterParameter, Tail.tailCoordRadius_pos]
  constructor
  · intro u v
    simp [sourceOrientedNormalCenterParameter, sourceShiftedTailOrientedInvariant,
      sourceShiftedTailGram, sourceVectorMinkowskiInner, Tail.tailEta_pos]
  · intro ι
    have hDtail : 0 < d + 1 - r := by omega
    have hnonempty : Nonempty (Fin (d + 1 - r)) :=
      Fin.pos_iff_nonempty.mp hDtail
    have hdet0 :
        (sourceShiftedTailOrientedInvariant d r hrD (n - r)
          (sourceOrientedNormalCenterParameter d n r hrD hrn).tail).det ι = 0 := by
      simpa [sourceOrientedNormalCenterParameter, sourceShiftedTailOrientedInvariant] using
        (Matrix.det_zero (n := Fin (d + 1 - r)) (R := ℂ) hnonempty)
    rw [hdet0, norm_zero]
    exact Tail.tailEta_pos

/-- The full rank-deficient Schur parameter window on normal parameters:
head near identity, mixed near zero, and tail in the target-shaped shifted
tail window. -/
def sourceOrientedRankDeficientSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :=
  {p |
    p.head ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
    p.mixed ∈ sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
    p ∈ sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail}

theorem isOpen_sourceOrientedRankDeficientSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen
      (sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) := by
  let P := SourceOrientedRankDeficientNormalParameter d n r hrD hrn
  have hhead_cont : Continuous (fun p : P => p.head) :=
    continuous_sourceOrientedNormalParameter_head
  have hmixed_cont : Continuous (fun p : P => p.mixed) :=
    continuous_sourceOrientedNormalParameter_mixed
  have hhead_open :
      IsOpen {p : P |
        p.head ∈ sourceOrientedHeadCoordinateWindow r headRadius} := by
    exact
      IsOpen.preimage hhead_cont
        (isOpen_sourceOrientedHeadCoordinateWindow r headRadius)
  have hmixed_open :
      IsOpen {p : P |
        p.mixed ∈ sourceOrientedMixedCoordinateWindow n r mixedRadius} := by
    exact
      IsOpen.preimage hmixed_cont
        (isOpen_sourceOrientedMixedCoordinateWindow n r mixedRadius)
  have htail_open :
      IsOpen {p : P |
        p ∈ sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail} :=
    isOpen_sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail
  simpa [sourceOrientedRankDeficientSchurParameterWindow, Set.setOf_and] using
    hhead_open.inter (hmixed_open.inter htail_open)

theorem isConnected_sourceOrientedRankDeficientSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsConnected
      (sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) := by
  let S : Set (Matrix (Fin r) (Fin r) ℂ ×
      Matrix (Fin (n - r)) (Fin r) ℂ ×
        (Fin (n - r) → Fin (d + 1 - r) → ℂ)) :=
    sourceOrientedHeadCoordinateWindow r headRadius ×ˢ
      (sourceOrientedMixedCoordinateWindow n r mixedRadius ×ˢ
        sourceShiftedTailTupleWindow d n r hrD hrn Tail)
  have hhead_conn :
      IsConnected (sourceOrientedHeadCoordinateWindow r headRadius) :=
    isConnected_sourceOrientedHeadCoordinateWindow r hheadRadius
  have hmixed_conn :
      IsConnected (sourceOrientedMixedCoordinateWindow n r mixedRadius) :=
    isConnected_sourceOrientedMixedCoordinateWindow n r hmixedRadius
  have htail_conn :
      IsConnected (sourceShiftedTailTupleWindow d n r hrD hrn Tail) :=
    isConnected_sourceShiftedTailTupleWindow d n r hrD hrn Tail
  have hS : IsConnected S := by
    dsimp [S]
    exact hhead_conn.prod (hmixed_conn.prod htail_conn)
  let e :=
    sourceOrientedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have himage : e.symm '' S = e ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨e p, hp, by simp [e]⟩
  have hpre : IsConnected (e ⁻¹' S) := by
    rw [← himage]
    exact hS.image e.symm e.symm.continuous.continuousOn
  have heq :
      sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail =
        e ⁻¹' S := by
    ext p
    simp [sourceOrientedRankDeficientSchurParameterWindow, S, e,
      sourceOrientedRankDeficientTailWindow, sourceShiftedTailTupleWindow,
      sourceOrientedNormalParameterCoordHomeomorph,
      sourceOrientedNormalParameterCoordEquiv, sourceOrientedNormalParameterCoord]
  rw [heq]
  exact hpre

/-- Connectedness of the full Schur-parameter window restricted to the
residual-tail exact-rank slice reduces to the corresponding tail-coordinate
connectedness theorem. -/
theorem isConnected_sourceOrientedRankDeficientSchurParameterWindow_tailRank
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    (htailRank_conn :
      IsConnected (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})) :
    IsConnected
      (sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail ∩
        {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
          (sourceOrientedNormalParameterSchurTail d n r hrD hrn p).rank =
            d + 1 - r}) := by
  let H : Set (Matrix (Fin r) (Fin r) ℂ) :=
    sourceOrientedHeadCoordinateWindow r headRadius
  let M : Set (Matrix (Fin (n - r)) (Fin r) ℂ) :=
    sourceOrientedMixedCoordinateWindow n r mixedRadius
  let T : Set (Fin (n - r) → Fin (d + 1 - r) → ℂ) :=
    sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
      {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}
  let S :
      Set (Matrix (Fin r) (Fin r) ℂ ×
        Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ)) :=
    H ×ˢ (M ×ˢ T)
  have hhead_conn : IsConnected H :=
    isConnected_sourceOrientedHeadCoordinateWindow r hheadRadius
  have hmixed_conn : IsConnected M :=
    isConnected_sourceOrientedMixedCoordinateWindow n r hmixedRadius
  have htail_conn : IsConnected T := by
    dsimp [T]
    exact htailRank_conn
  have hS : IsConnected S := by
    dsimp [S]
    exact hhead_conn.prod (hmixed_conn.prod htail_conn)
  let e :=
    sourceOrientedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have himage : e.symm '' S = e ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨e p, hp, by simp [e]⟩
  have hpre : IsConnected (e ⁻¹' S) := by
    rw [← himage]
    exact hS.image e.symm e.symm.continuous.continuousOn
  have heq :
      sourceOrientedRankDeficientSchurParameterWindow
            d n r hrD hrn headRadius mixedRadius Tail ∩
          {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
            (sourceOrientedNormalParameterSchurTail d n r hrD hrn p).rank =
              d + 1 - r} =
        e ⁻¹' S := by
    ext p
    simp [sourceOrientedRankDeficientSchurParameterWindow, S, H, M, T, e,
      sourceOrientedRankDeficientTailWindow, sourceShiftedTailTupleWindow,
      sourceOrientedNormalParameterSchurTail,
      sourceOrientedNormalParameterCoordHomeomorph,
      sourceOrientedNormalParameterCoordEquiv, sourceOrientedNormalParameterCoord]
    tauto
  rw [heq]
  exact hpre

theorem sourceOrientedNormalCenterParameter_mem_schurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    sourceOrientedNormalCenterParameter d n r hrD hrn ∈
      sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail := by
  constructor
  · intro a b
    simp [sourceOrientedNormalCenterParameter, hheadRadius]
  constructor
  · intro u a
    simpa [sourceOrientedNormalCenterParameter] using hmixedRadius
  · exact sourceOrientedNormalCenterParameter_mem_tailWindow d n r hrD hrn Tail

/-- The full Schur parameter window is an open connected neighborhood of the
normal center. -/
theorem sourceOrientedRankDeficientSchurParameterWindow_open_connected
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen
        (sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail) ∧
      IsConnected
        (sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail) ∧
      sourceOrientedNormalCenterParameter d n r hrD hrn ∈
        sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail := by
  exact
    ⟨isOpen_sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail,
      isConnected_sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn hheadRadius hmixedRadius Tail,
      sourceOrientedNormalCenterParameter_mem_schurParameterWindow
        d n r hrD hrn hheadRadius hmixedRadius Tail⟩

/-- Build a tail-window choice from the checked one-way shifted-tail small
realization theorem. -/
def sourceOriented_rankDeficient_tailWindowChoice
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {tailCoordRadius : ℝ}
    (htailCoordRadius : 0 < tailCoordRadius) :
    SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn := by
  classical
  let hrealization :=
    sourceShiftedTailSmallRealization d r (n - r) hrD htailCoordRadius
  let tailEta := Classical.choose hrealization
  have htailEta_spec := Classical.choose_spec hrealization
  exact
    { tailCoordRadius := tailCoordRadius
      tailCoordRadius_pos := htailCoordRadius
      tailEta := tailEta
      tailEta_pos := htailEta_spec.1
      tailRealize := htailEta_spec.2 }

namespace SourceOrientedRankDeficientTailWindowChoice

/-- Window membership supplies Schur residual-tail smallness for normal
parameters with invertible head. -/
theorem normalParam_tail_small
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det)
    (hp : p ∈ sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail) :
    SourceOrientedSchurTailSmallFor d n r hrD hrn Tail.tailEta
      (sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p))
      p.head := by
  have htail_eq :
      sourceOrientedSchurResidualTailData d n r hrD hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p))
          p.head =
        sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail :=
    sourceOrientedSchurResidualTailData_normalParameter
      d n r hrD hrn p hH
  exact
    { gram_bound := by
        intro u v
        have h := hp.2.1 u v
        simpa [htail_eq] using h
      det_bound := by
        intro ι
        have h := hp.2.2 ι
        simpa [htail_eq] using h }

end SourceOrientedRankDeficientTailWindowChoice

end BHW
