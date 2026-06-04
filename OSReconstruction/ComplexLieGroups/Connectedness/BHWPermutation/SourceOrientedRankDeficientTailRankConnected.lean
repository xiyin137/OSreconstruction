import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailWindow

/-!
# Exact-rank residual tail connectedness support

This file starts the final residual-tail connectedness bridge for the
rank-deficient source Schur chart.  The exact-rank condition on the shifted
tail Gram is transported to the already checked full-rank source configuration
space after diagonal normalization, and radial shrinking is proved to stay
inside the target-shaped tail window.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The ordinary dot-Gram has full symmetric rank exactly when the underlying
source configuration has full column rank. -/
theorem sourceComplexDotGram_rank_eq_iff_fullRank
    {m D : ℕ}
    (A : Fin m → Fin D → ℂ) :
    (Matrix.of fun i j : Fin m => sourceComplexDotGram D m A i j).rank = D ↔
      A ∈ sourceFullRankConfigurations m D := by
  constructor
  · intro hgram
    let P : Matrix (Fin m) (Fin D) ℂ := Matrix.of fun i a => A i a
    let M : Matrix (Fin m) (Fin m) ℂ :=
      Matrix.of fun i j : Fin m => sourceComplexDotGram D m A i j
    have hM_eq : M = P * Pᵀ := by
      ext i j
      simp [M, P, sourceComplexDotGram, Matrix.mul_apply]
    have hM_rank : M.rank = D := by
      simpa [M] using hgram
    have hle : P.rank ≤ D := by
      simpa using Matrix.rank_le_width P
    have hge : D ≤ P.rank := by
      have hmul_le : (P * Pᵀ).rank ≤ P.rank :=
        Matrix.rank_mul_le_left P Pᵀ
      have hmul_rank : (P * Pᵀ).rank = D := by
        rw [← hM_eq]
        exact hM_rank
      exact hmul_rank.symm.le.trans hmul_le
    simpa [sourceFullRankConfigurations, P] using le_antisymm hle hge
  · intro hA
    exact (sourceComplexDotGram_mem_rankExact_of_fullRank hA).2

/-- Full column rank of a source configuration is preserved by nonzero scalar
multiplication. -/
theorem sourceFullRankConfigurations_smul_mem
    {m D : ℕ}
    {A : Fin m → Fin D → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m D)
    {c : ℂ} (hc : c ≠ 0) :
    (fun i a => c * A i a) ∈ sourceFullRankConfigurations m D := by
  let P : Matrix (Fin m) (Fin D) ℂ := Matrix.of fun i a => A i a
  have hmat :
      (Matrix.of fun (i : Fin m) (a : Fin D) => c * A i a) = c • P := by
    ext i a
    simp [P]
  change (Matrix.of fun (i : Fin m) (a : Fin D) => c * A i a).rank = D
  rw [hmat]
  simpa [sourceFullRankConfigurations, P] using
    (matrix_rank_smul_of_ne_zero (m := Fin m) (n := Fin D) c hc P).trans hA

/-- A positive real scalar at most one dominates all of its positive powers. -/
theorem real_pow_le_self_of_pos_of_le_one
    {ρ : ℝ} {k : ℕ}
    (hρ : 0 < ρ) (hρle : ρ ≤ 1) (hk : 0 < k) :
    ρ ^ k ≤ ρ := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  rw [pow_succ']
  exact mul_le_of_le_one_right hρ.le (pow_le_one₀ hρ.le hρle)

/-- After the shifted-tail metric normalization, exact rank of the shifted
tail Gram is the checked full-rank condition on the normalized tuple. -/
theorem sourceShiftedTailGram_rank_eq_iff_normalized_fullRank
    (d r m : ℕ)
    (hrD : r < d + 1)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    (sourceShiftedTailGram d r hrD m q).rank = d + 1 - r ↔
      (fun u μ =>
          (sourceShiftedTailMetricNormalization d r hrD).scale μ * q u μ) ∈
        sourceFullRankConfigurations m (d + 1 - r) := by
  let N := sourceShiftedTailMetricNormalization d r hrD
  have hgram :
      (Matrix.of fun u v : Fin m =>
        sourceComplexDotGram (d + 1 - r) m
          (fun u μ => N.scale μ * q u μ) u v) =
        sourceShiftedTailGram d r hrD m q := by
    have h :=
      congrArg SourceTailOrientedData.gram
        (sourceShiftedTailInvariant_toEuclidean d r m hrD N q)
    ext u v
    exact congr_fun (congr_fun (by
      simpa [sourceComplexDotGram, sourceTailOrientedInvariant,
        sourceShiftedTailDataToEuclidean, N] using h) u) v
  rw [← hgram]
  exact sourceComplexDotGram_rank_eq_iff_fullRank
    (fun u μ => N.scale μ * q u μ)

/-- Radial shrinking by a positive real scalar preserves membership in the
target-shaped shifted-tail window and preserves the residual exact-rank
condition. -/
theorem sourceShiftedTailTupleWindow_tailRank_joined_radial_smul
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    {q : Fin (n - r) → Fin (d + 1 - r) → ℂ}
    (hq :
      q ∈ sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
    {ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1) :
    JoinedIn
      (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
      q (fun u μ => (ρ : ℂ) * q u μ) := by
  let S :=
    sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
      {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}
  let f : ℝ → Fin (n - r) → Fin (d + 1 - r) → ℂ :=
    fun t u μ => (((1 - t) + t * ρ : ℝ) : ℂ) * q u μ
  refine JoinedIn.ofLine (f := f) ?_ ?_ ?_ ?_
  · fun_prop
  · ext u μ
    simp [f]
  · ext u μ
    simp [f]
  · rintro x ⟨t, ht, rfl⟩
    change t ∈ Set.Icc (0 : ℝ) 1 at ht
    have hcoeff_pos : 0 < (1 - t) + t * ρ := by
      rcases eq_or_lt_of_le ht.1 with ht0 | htpos
      · subst ht0
        simp
      · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos htpos hρ)
    have hcoeff_nonneg : 0 ≤ (1 - t) + t * ρ := hcoeff_pos.le
    have hcoeff_le_one : (1 - t) + t * ρ ≤ 1 := by
      have hmul : t * ρ ≤ t * 1 := mul_le_mul_of_nonneg_left hρle ht.1
      linarith
    constructor
    · exact
        sourceShiftedTailWindow_scaled d n r hrD hrn Tail
          hq.1.1 hq.1.2.1 hq.1.2.2 hcoeff_nonneg hcoeff_le_one
    · have hgram_smul :
          sourceShiftedTailGram d r hrD (n - r)
              (fun u μ => (((1 - t) + t * ρ : ℝ) : ℂ) * q u μ) =
            ((((1 - t) + t * ρ : ℝ) : ℂ) *
              (((1 - t) + t * ρ : ℝ) : ℂ)) •
              sourceShiftedTailGram d r hrD (n - r) q := by
        ext u v
        rw [Matrix.smul_apply]
        exact
          sourceShiftedTailGram_smul d r (n - r) hrD
            (((1 - t) + t * ρ : ℝ) : ℂ) q u v
      change
        (sourceShiftedTailGram d r hrD (n - r)
            (fun u μ => (((1 - t) + t * ρ : ℝ) : ℂ) * q u μ)).rank =
          d + 1 - r
      rw [hgram_smul]
      have hcoeff_ne :
          (((1 - t) + t * ρ : ℝ) : ℂ) *
              (((1 - t) + t * ρ : ℝ) : ℂ) ≠ 0 := by
        exact mul_ne_zero (by exact_mod_cast hcoeff_pos.ne')
          (by exact_mod_cast hcoeff_pos.ne')
      simpa using
        (matrix_rank_smul_of_ne_zero
          (m := Fin (n - r)) (n := Fin (n - r))
          ((((1 - t) + t * ρ : ℝ) : ℂ) *
            (((1 - t) + t * ρ : ℝ) : ℂ))
          hcoeff_ne (sourceShiftedTailGram d r hrD (n - r) q)).trans hq.2

/-- Any two points of the residual-tail exact-rank slice are joined inside the
target-shaped tail window.  The proof uses the checked full-rank configuration
path after shifted-tail metric normalization, then scales the middle path small
enough to satisfy the target coordinate, Gram, and determinant bounds. -/
theorem sourceShiftedTailTupleWindow_tailRank_joined
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (hn : d + 1 ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    {q₀ q₁ : Fin (n - r) → Fin (d + 1 - r) → ℂ}
    (hq₀ :
      q₀ ∈ sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
    (hq₁ :
      q₁ ∈ sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}) :
    JoinedIn
      (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
      q₀ q₁ := by
  let D := d + 1 - r
  let m := n - r
  have hDpos : 0 < D := by
    dsimp [D]
    omega
  have hDle : D ≤ m := by
    dsimp [D, m]
    omega
  let N := sourceShiftedTailMetricNormalization d r hrD
  let A₀ : Fin m → Fin D → ℂ := fun u μ => N.scale μ * q₀ u μ
  let A₁ : Fin m → Fin D → ℂ := fun u μ => N.scale μ * q₁ u μ
  have hA₀ : A₀ ∈ sourceFullRankConfigurations m D := by
    dsimp [A₀, D, m, N]
    exact
      (sourceShiftedTailGram_rank_eq_iff_normalized_fullRank
        d r (n - r) hrD q₀).1 hq₀.2
  have hA₁ : A₁ ∈ sourceFullRankConfigurations m D := by
    dsimp [A₁, D, m, N]
    exact
      (sourceShiftedTailGram_rank_eq_iff_normalized_fullRank
        d r (n - r) hrD q₁).1 hq₁.2
  have hjoinA :
      JoinedIn (sourceFullRankConfigurations m D) A₀ A₁ :=
    (sourceFullRankConfigurations_isPathConnected m D hDle).joinedIn
      A₀ hA₀ A₁ hA₁
  let γ : Path A₀ A₁ := hjoinA.somePath
  have hγ_mem : ∀ t : unitInterval, γ t ∈ sourceFullRankConfigurations m D :=
    hjoinA.somePath_mem
  let unnorm : (Fin m → Fin D → ℂ) → Fin m → Fin D → ℂ :=
    fun A u μ => (N.scale μ)⁻¹ * A u μ
  have hunnorm_cont : Continuous unnorm := by
    dsimp [unnorm]
    fun_prop
  let γq : Path (unnorm A₀) (unnorm A₁) := γ.map hunnorm_cont
  rcases exists_pos_norm_bound_of_path γq with
    ⟨Mq, hMq_pos, hMq_bound⟩
  let gramMap : (Fin m → Fin D → ℂ) → Fin m → Fin m → ℂ :=
    fun q u v => sourceShiftedTailGram d r hrD m q u v
  have hgramMap_cont : Continuous gramMap := by
    dsimp [gramMap]
    exact continuous_pi fun u => continuous_pi fun v =>
      (continuous_apply v).comp
        ((continuous_apply u).comp (continuous_sourceShiftedTailGram d r m hrD))
  let γgram : Path (gramMap (unnorm A₀)) (gramMap (unnorm A₁)) :=
    γq.map hgramMap_cont
  rcases exists_pos_norm_bound_of_path γgram with
    ⟨Mg, hMg_pos, hMg_bound⟩
  let detMap : (Fin m → Fin D → ℂ) → ((Fin D ↪ Fin m) → ℂ) :=
    fun q ι => (sourceShiftedTailOrientedInvariant d r hrD m q).det ι
  have hdetMap_cont : Continuous detMap := by
    dsimp [detMap]
    fun_prop
  let γdet : Path (detMap (unnorm A₀)) (detMap (unnorm A₁)) :=
    γq.map hdetMap_cont
  rcases exists_pos_norm_bound_of_path γdet with
    ⟨Md, hMd_pos, hMd_bound⟩
  let M : ℝ := Mq + Mg + Md + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    linarith
  have hMq_le_M : ∀ t : unitInterval, ‖γq t‖ ≤ M := by
    intro t
    dsimp [M]
    linarith [hMq_bound t, hMg_pos, hMd_pos]
  have hMg_le_M : ∀ t : unitInterval, ‖γgram t‖ ≤ M := by
    intro t
    dsimp [M]
    linarith [hMg_bound t, hMq_pos, hMd_pos]
  have hMd_le_M : ∀ t : unitInterval, ‖γdet t‖ ≤ M := by
    intro t
    dsimp [M]
    linarith [hMd_bound t, hMq_pos, hMg_pos]
  let δ : ℝ := min Tail.tailCoordRadius Tail.tailEta
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min Tail.tailCoordRadius_pos Tail.tailEta_pos
  rcases exists_pos_mul_lt hδ_pos M with ⟨ρ₀, hρ₀_pos, hρ₀_small⟩
  let ρ : ℝ := min ρ₀ 1
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρ₀_pos zero_lt_one
  have hρ_le_one : ρ ≤ 1 := by
    dsimp [ρ]
    exact min_le_right ρ₀ 1
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := by
    dsimp [ρ]
    exact min_le_left ρ₀ 1
  have hρM_delta : ρ * M < δ := by
    rw [mul_comm ρ M]
    exact (mul_le_mul_of_nonneg_left hρ_le_ρ₀ hM_pos.le).trans_lt hρ₀_small
  have hρM_coord : ρ * M < Tail.tailCoordRadius :=
    lt_of_lt_of_le hρM_delta (min_le_left _ _)
  have hρM_eta : ρ * M < Tail.tailEta :=
    lt_of_lt_of_le hρM_delta (min_le_right _ _)
  have hrad₀ :
      JoinedIn
        (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
          {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
            (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
        q₀ (fun u μ => (ρ : ℂ) * q₀ u μ) :=
    sourceShiftedTailTupleWindow_tailRank_joined_radial_smul
      d n r hrD hrn Tail hq₀ hρ_pos hρ_le_one
  have hrad₁ :
      JoinedIn
        (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
          {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
            (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
        q₁ (fun u μ => (ρ : ℂ) * q₁ u μ) :=
    sourceShiftedTailTupleWindow_tailRank_joined_radial_smul
      d n r hrD hrn Tail hq₁ hρ_pos hρ_le_one
  have hsource₀ :
      (fun u μ => (ρ : ℂ) * q₀ u μ) =
        (fun u μ => (ρ : ℂ) * unnorm A₀ u μ) := by
    ext u μ
    simp [unnorm, A₀, N.scale_ne_zero μ]
  have hsource₁ :
      (fun u μ => (ρ : ℂ) * q₁ u μ) =
        (fun u μ => (ρ : ℂ) * unnorm A₁ u μ) := by
    ext u μ
    simp [unnorm, A₁, N.scale_ne_zero μ]
  let scaleUnnorm : (Fin m → Fin D → ℂ) → Fin m → Fin D → ℂ :=
    fun A u μ => (ρ : ℂ) * unnorm A u μ
  have hscaleUnnorm_cont : Continuous scaleUnnorm := by
    dsimp [scaleUnnorm, unnorm]
    fun_prop
  have hmiddle :
      JoinedIn
        (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
          {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
            (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})
        (fun u μ => (ρ : ℂ) * q₀ u μ)
        (fun u μ => (ρ : ℂ) * q₁ u μ) := by
    refine ⟨(γ.map hscaleUnnorm_cont).cast hsource₀ hsource₁, ?_⟩
    intro t
    constructor
    · constructor
      · intro u μ
        have hcoord_le :
            ‖unnorm (γ t) u μ‖ ≤ ‖γq t‖ := by
          exact (norm_le_pi_norm (unnorm (γ t) u) μ).trans
            (norm_le_pi_norm (γq t) u)
        calc
          ‖(ρ : ℂ) * unnorm (γ t) u μ‖ =
              ρ * ‖unnorm (γ t) u μ‖ := by
                rw [norm_mul, Complex.norm_of_nonneg hρ_pos.le]
          _ ≤ ρ * ‖γq t‖ :=
                mul_le_mul_of_nonneg_left hcoord_le hρ_pos.le
          _ ≤ ρ * M :=
                mul_le_mul_of_nonneg_left (hMq_le_M t) hρ_pos.le
          _ < Tail.tailCoordRadius := hρM_coord
      constructor
      · intro u v
        have hentry_le :
            ‖sourceShiftedTailGram d r hrD m (unnorm (γ t)) u v‖ ≤ M := by
          exact
            ((norm_le_pi_norm
              (sourceShiftedTailGram d r hrD m (unnorm (γ t)) u) v).trans
              (norm_le_pi_norm (γgram t) u)).trans (hMg_le_M t)
        calc
          ‖(sourceShiftedTailOrientedInvariant d r hrD m
              (fun u μ => (ρ : ℂ) * unnorm (γ t) u μ)).gram u v‖ =
              ‖(ρ : ℂ) * (ρ : ℂ) *
                (sourceShiftedTailOrientedInvariant d r hrD m
                  (unnorm (γ t))).gram u v‖ := by
                rw [sourceShiftedTailOrientedInvariant_smul_gram]
          _ = ρ * ρ *
                ‖(sourceShiftedTailOrientedInvariant d r hrD m
                  (unnorm (γ t))).gram u v‖ := by
                rw [norm_mul, norm_mul]
                simp [abs_of_nonneg hρ_pos.le, mul_assoc]
          _ ≤ ρ * M := by
                calc
                  ρ * ρ *
                      ‖(sourceShiftedTailOrientedInvariant d r hrD m
                        (unnorm (γ t))).gram u v‖
                      ≤ ρ * 1 *
                      ‖(sourceShiftedTailOrientedInvariant d r hrD m
                        (unnorm (γ t))).gram u v‖ := by
                        gcongr
                  _ = ρ *
                      ‖sourceShiftedTailGram d r hrD m
                        (unnorm (γ t)) u v‖ := by
                        simp [sourceShiftedTailOrientedInvariant]
                  _ ≤ ρ * M := mul_le_mul_of_nonneg_left hentry_le hρ_pos.le
          _ < Tail.tailEta := hρM_eta
      · intro ι
        have hentry_le :
            ‖(sourceShiftedTailOrientedInvariant d r hrD m
                (unnorm (γ t))).det ι‖ ≤ M := by
          exact (norm_le_pi_norm (γdet t) ι).trans (hMd_le_M t)
        have hpow_le : ‖(ρ : ℂ) ^ D‖ ≤ ρ := by
          rw [norm_pow, Complex.norm_of_nonneg hρ_pos.le]
          exact real_pow_le_self_of_pos_of_le_one hρ_pos hρ_le_one hDpos
        calc
          ‖(sourceShiftedTailOrientedInvariant d r hrD m
              (fun u μ => (ρ : ℂ) * unnorm (γ t) u μ)).det ι‖ =
              ‖(ρ : ℂ) ^ D *
                (sourceShiftedTailOrientedInvariant d r hrD m
                  (unnorm (γ t))).det ι‖ := by
                dsimp [D]
                rw [sourceShiftedTailOrientedInvariant_smul_det]
          _ = ‖(ρ : ℂ) ^ D‖ *
                ‖(sourceShiftedTailOrientedInvariant d r hrD m
                  (unnorm (γ t))).det ι‖ := norm_mul _ _
          _ ≤ ρ * M := mul_le_mul hpow_le hentry_le (norm_nonneg _) hρ_pos.le
          _ < Tail.tailEta := hρM_eta
    · have hscaled_full :
          (fun u μ => (ρ : ℂ) * γ t u μ) ∈
            sourceFullRankConfigurations m D :=
        sourceFullRankConfigurations_smul_mem (hγ_mem t)
          (by exact_mod_cast hρ_pos.ne')
      have hnormalized_eq :
          (fun u μ =>
              N.scale μ * ((ρ : ℂ) * unnorm (γ t) u μ)) =
            (fun u μ => (ρ : ℂ) * γ t u μ) := by
        ext u μ
        simp [unnorm, N.scale_ne_zero μ, mul_left_comm, mul_comm]
      dsimp [m, D] at hscaled_full
      change
        (sourceShiftedTailGram d r hrD (n - r)
          (fun u μ => (ρ : ℂ) * unnorm (γ t) u μ)).rank =
          d + 1 - r
      rw [sourceShiftedTailGram_rank_eq_iff_normalized_fullRank]
      simpa [N, m, D, hnormalized_eq] using hscaled_full
  exact (hrad₀.trans hmiddle).trans hrad₁.symm

/-- The residual-tail exact-rank slice of the target-shaped window is
nonempty in the hard range. -/
theorem sourceShiftedTailTupleWindow_tailRank_nonempty
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (hn : d + 1 ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
      {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}).Nonempty := by
  have hDpos : 0 < d + 1 - r := by omega
  have hDle : d + 1 - r ≤ n - r := by omega
  let N := sourceShiftedTailMetricNormalization d r hrD
  let A : Fin (n - r) → Fin (d + 1 - r) → ℂ :=
    standardFullRankConfiguration (n - r) (d + 1 - r) hDle
  let qraw : Fin (n - r) → Fin (d + 1 - r) → ℂ :=
    fun u μ => (N.scale μ)⁻¹ * A u μ
  let gramRaw : Fin (n - r) → Fin (n - r) → ℂ :=
    fun u v => sourceShiftedTailGram d r hrD (n - r) qraw u v
  let detRaw : (Fin (d + 1 - r) ↪ Fin (n - r)) → ℂ :=
    fun ι => (sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).det ι
  let M : ℝ := ‖qraw‖ + ‖gramRaw‖ + ‖detRaw‖ + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  let δ : ℝ := min Tail.tailCoordRadius Tail.tailEta
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min Tail.tailCoordRadius_pos Tail.tailEta_pos
  rcases exists_pos_mul_lt hδ_pos M with ⟨ρ₀, hρ₀_pos, hρ₀_small⟩
  let ρ : ℝ := min ρ₀ 1
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρ₀_pos zero_lt_one
  have hρ_le_one : ρ ≤ 1 := by
    dsimp [ρ]
    exact min_le_right ρ₀ 1
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := by
    dsimp [ρ]
    exact min_le_left ρ₀ 1
  have hρM_delta : ρ * M < δ := by
    rw [mul_comm ρ M]
    exact (mul_le_mul_of_nonneg_left hρ_le_ρ₀ hM_pos.le).trans_lt hρ₀_small
  have hρM_coord : ρ * M < Tail.tailCoordRadius :=
    lt_of_lt_of_le hρM_delta (min_le_left _ _)
  have hρM_eta : ρ * M < Tail.tailEta :=
    lt_of_lt_of_le hρM_delta (min_le_right _ _)
  let q : Fin (n - r) → Fin (d + 1 - r) → ℂ :=
    fun u μ => (ρ : ℂ) * qraw u μ
  refine ⟨q, ?_⟩
  constructor
  · constructor
    · intro u μ
      have hcoord_le : ‖qraw u μ‖ ≤ ‖qraw‖ := by
        exact (norm_le_pi_norm (qraw u) μ).trans (norm_le_pi_norm qraw u)
      have hqraw_le_M : ‖qraw‖ ≤ M := by
        dsimp [M]
        linarith [norm_nonneg gramRaw, norm_nonneg detRaw]
      calc
        ‖q u μ‖ = ρ * ‖qraw u μ‖ := by
          rw [norm_mul, Complex.norm_of_nonneg hρ_pos.le]
        _ ≤ ρ * ‖qraw‖ := mul_le_mul_of_nonneg_left hcoord_le hρ_pos.le
        _ ≤ ρ * M := mul_le_mul_of_nonneg_left hqraw_le_M hρ_pos.le
        _ < Tail.tailCoordRadius := hρM_coord
    constructor
    · intro u v
      have hentry_le : ‖gramRaw u v‖ ≤ M := by
        have hgram_le : ‖gramRaw u v‖ ≤ ‖gramRaw‖ :=
          (norm_le_pi_norm (gramRaw u) v).trans (norm_le_pi_norm gramRaw u)
        have hgram_M : ‖gramRaw‖ ≤ M := by
          dsimp [M]
          linarith [norm_nonneg qraw, norm_nonneg detRaw]
        exact hgram_le.trans hgram_M
      calc
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ =
            ‖(ρ : ℂ) * (ρ : ℂ) *
              (sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).gram u v‖ := by
              dsimp [q]
              rw [sourceShiftedTailOrientedInvariant_smul_gram]
        _ = ρ * ρ *
              ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).gram u v‖ := by
              rw [norm_mul, norm_mul]
              simp [abs_of_nonneg hρ_pos.le, mul_assoc]
        _ ≤ ρ * M := by
              calc
                ρ * ρ *
                    ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).gram u v‖
                    ≤ ρ * 1 *
                    ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).gram u v‖ := by
                      gcongr
                _ = ρ * ‖gramRaw u v‖ := by
                      simp [gramRaw, sourceShiftedTailOrientedInvariant]
                _ ≤ ρ * M := mul_le_mul_of_nonneg_left hentry_le hρ_pos.le
        _ < Tail.tailEta := hρM_eta
    · intro ι
      have hentry_le : ‖detRaw ι‖ ≤ M := by
        have hdet_le : ‖detRaw ι‖ ≤ ‖detRaw‖ := norm_le_pi_norm detRaw ι
        have hdet_M : ‖detRaw‖ ≤ M := by
          dsimp [M]
          linarith [norm_nonneg qraw, norm_nonneg gramRaw]
        exact hdet_le.trans hdet_M
      have hpow_le : ‖(ρ : ℂ) ^ (d + 1 - r)‖ ≤ ρ := by
        rw [norm_pow, Complex.norm_of_nonneg hρ_pos.le]
        exact real_pow_le_self_of_pos_of_le_one hρ_pos hρ_le_one hDpos
      calc
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ =
            ‖(ρ : ℂ) ^ (d + 1 - r) *
              (sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).det ι‖ := by
              dsimp [q]
              rw [sourceShiftedTailOrientedInvariant_smul_det]
        _ = ‖(ρ : ℂ) ^ (d + 1 - r)‖ *
              ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) qraw).det ι‖ :=
              norm_mul _ _
        _ ≤ ρ * M := by
              simpa [detRaw] using
                (mul_le_mul hpow_le hentry_le (norm_nonneg _) hρ_pos.le)
        _ < Tail.tailEta := hρM_eta
  · have hA_full :
        A ∈ sourceFullRankConfigurations (n - r) (d + 1 - r) :=
      standardFullRankConfiguration_mem_sourceFullRankConfigurations hDle
    have hscaled_full :
        (fun u μ => (ρ : ℂ) * A u μ) ∈
          sourceFullRankConfigurations (n - r) (d + 1 - r) :=
      sourceFullRankConfigurations_smul_mem hA_full
        (by exact_mod_cast hρ_pos.ne')
    have hnormalized_eq :
        (fun u μ => N.scale μ * q u μ) =
          (fun u μ => (ρ : ℂ) * A u μ) := by
      ext u μ
      simp [q, qraw, N.scale_ne_zero μ, mul_left_comm, mul_comm]
    change (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r
    rw [sourceShiftedTailGram_rank_eq_iff_normalized_fullRank]
    simpa [N, hnormalized_eq] using hscaled_full

/-- The residual-tail exact-rank slice of the target-shaped shifted-tail window
is path-connected in the hard range. -/
theorem isPathConnected_sourceShiftedTailTupleWindow_tailRank
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (hn : d + 1 ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsPathConnected
      (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}) := by
  rw [isPathConnected_iff]
  constructor
  · exact sourceShiftedTailTupleWindow_tailRank_nonempty d n r hrD hrn hn Tail
  · intro q₀ hq₀ q₁ hq₁
    exact sourceShiftedTailTupleWindow_tailRank_joined d n r hrD hrn hn Tail hq₀ hq₁

/-- Connectedness form of
`isPathConnected_sourceShiftedTailTupleWindow_tailRank`, for downstream
Schur-window consumers. -/
theorem isConnected_sourceShiftedTailTupleWindow_tailRank
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (hn : d + 1 ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsConnected
      (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}) :=
  (isPathConnected_sourceShiftedTailTupleWindow_tailRank
    d n r hrD hrn hn Tail).isConnected

end BHW
