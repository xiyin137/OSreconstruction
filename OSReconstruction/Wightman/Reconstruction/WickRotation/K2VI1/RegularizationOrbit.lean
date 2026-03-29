import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Bounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.RegularizationSeminorm

noncomputable section

open MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The one-point embedding into `Fin 1` Schwartz space is continuous with
respect to the Schwartz seminorm family, so every target seminorm is controlled
by a finite supremum of source seminorms. -/
private theorem onePointToFin1_seminorm_bound_exists_vi1Orbit_local
    {d : ℕ}
    (p l : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ g : SchwartzSpacetime d,
        SchwartzMap.seminorm ℝ p l
            (onePointToFin1CLM d g : SchwartzNPoint d 1) ≤
          (C • s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) g := by
  let L : SchwartzSpacetime d →L[ℂ] SchwartzNPoint d 1 := onePointToFin1CLM d
  let q : Seminorm ℝ (SchwartzSpacetime d) :=
    (schwartzSeminormFamily ℝ (Fin 1 → SpacetimeDim d) ℂ (p, l)).comp
      (L.restrictScalars ℝ).toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun g : SchwartzSpacetime d =>
      schwartzSeminormFamily ℝ (Fin 1 → SpacetimeDim d) ℂ (p, l) (L g))
    exact ((schwartz_withSeminorms ℝ (Fin 1 → SpacetimeDim d) ℂ).continuous_seminorm (p, l)).comp
      L.continuous
  obtain ⟨s, C, hC_ne, hq_bound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (SpacetimeDim d) ℂ) q hq_cont
  refine ⟨s, C, hC_ne, ?_⟩
  intro g
  change (schwartzSeminormFamily ℝ (Fin 1 → SpacetimeDim d) ℂ (p, l)) (L g) ≤
    (C • s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) g
  simpa [q] using hq_bound g

/-- A finite supremum of Schwartz seminorms is uniformly bounded on the
regularized reflected-probe sequence once each individual seminorm is. -/
private theorem reflected_negativeApproxIdentity_convolution_sup_seminorm_uniform_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : Finset (ℕ × ℕ))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      (s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ))
        (((positiveTimeCompactSupportConvolution
            (⟨reflectedSchwartzSpacetime (φ_seq n),
              ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                  (hφ_compact n)⟩⟩)
            h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) ≤ C := by
  induction s using Finset.cons_induction with
  | empty =>
      refine ⟨0, le_rfl, ?_⟩
      intro n
      simp [Seminorm.bot_eq_zero, Seminorm.zero_apply]
  | cons a s has hs =>
      obtain ⟨Ca, hCa_nonneg, hCa⟩ :=
        positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_seminorm_uniform_local
          (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball a.1 a.2 h
      obtain ⟨Cs, hCs_nonneg, hCs⟩ := hs
      refine ⟨Ca + Cs, add_nonneg hCa_nonneg hCs_nonneg, ?_⟩
      intro n
      rw [Finset.sup_cons, Seminorm.sup_apply]
      refine max_le ?_ ?_
      · exact le_trans (hCa n) (by linarith)
      · exact le_trans (hCs n) (by linarith)

/-- Every fixed one-point Schwartz seminorm of the regularized reflected-probe
sequence is uniformly bounded in `n`. This is the first OS-side consumer of the
regularization stack. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_onePoint_seminorm_uniform_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (p l : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      SchwartzMap.seminorm ℝ p l
        (onePointToFin1CLM d
          (((positiveTimeCompactSupportConvolution
              (⟨reflectedSchwartzSpacetime (φ_seq n),
                ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                  reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                    (hφ_compact n)⟩⟩)
              h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) ≤ C := by
  obtain ⟨s, C0, hC0_ne, hbound⟩ :=
    onePointToFin1_seminorm_bound_exists_vi1Orbit_local (d := d) p l
  obtain ⟨Cs, hCs_nonneg, hCs⟩ :=
    reflected_negativeApproxIdentity_convolution_sup_seminorm_uniform_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball s h
  refine ⟨(C0 : ℝ) * Cs, mul_nonneg (NNReal.coe_nonneg C0) hCs_nonneg, ?_⟩
  intro n
  have hmain :=
    hbound
      (((positiveTimeCompactSupportConvolution
          (⟨reflectedSchwartzSpacetime (φ_seq n),
            ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
              reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                (hφ_compact n)⟩⟩)
          h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
  calc
    SchwartzMap.seminorm ℝ p l
        (onePointToFin1CLM d
          (((positiveTimeCompactSupportConvolution
              (⟨reflectedSchwartzSpacetime (φ_seq n),
                ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                  reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                    (hφ_compact n)⟩⟩)
              h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))
        ≤ (C0 • s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ))
            (((positiveTimeCompactSupportConvolution
                (⟨reflectedSchwartzSpacetime (φ_seq n),
                  ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                    reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                      (hφ_compact n)⟩⟩)
                h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) := hmain
    _ = (C0 : ℝ) *
          (s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ))
            (((positiveTimeCompactSupportConvolution
                (⟨reflectedSchwartzSpacetime (φ_seq n),
                  ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                    reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                      (hφ_compact n)⟩⟩)
                h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) := by
          simp [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    _ ≤ (C0 : ℝ) * Cs := by
          exact mul_le_mul_of_nonneg_left (hCs n) (NNReal.coe_nonneg C0)

/-- A positive-time compact-support spacetime test gives an ordered
positive-time one-point Schwartz test. This local copy keeps the new VI.1 orbit
file independent of the frozen support layer. -/
private theorem onePointToFin1_tsupport_orderedPositiveTime_vi1Orbit_local
    {d : ℕ}
    (f : SchwartzSpacetime d)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d f : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  have hv0 : v 0 ∈ tsupport (f : SpacetimeDim d → ℂ) := by
    have :=
      tsupport_comp_subset_preimage (f : SpacetimeDim d → ℂ)
        (f := fun w : Fin 1 → SpacetimeDim d => w 0) (continuous_apply 0) hv
    exact this
  exact Set.mem_setOf.mp (hf hv0)

/-- Uniform OS pre-Hilbert self-inner bound for the regularized reflected-probe
one-point vectors. This is the first direct Hilbert-space consumer of the VI.1
regularization/seminorm stack. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_inner_self_uniform_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      let ψn : positiveTimeCompactSupportSubmodule d :=
        ⟨reflectedSchwartzSpacetime (φ_seq n),
          ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
            reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
              (hφ_compact n)⟩⟩
      let gn : positiveTimeCompactSupportSubmodule d :=
        positiveTimeCompactSupportConvolution ψn h
      let fn : SchwartzNPoint d 1 := onePointToFin1CLM d (gn : SchwartzSpacetime d)
      let hfn : tsupport ((fn : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
          OrderedPositiveTimeRegion d 1 :=
        onePointToFin1_tsupport_orderedPositiveTime_vi1Orbit_local (d := d)
          (gn : SchwartzSpacetime d) gn.property.1
      ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          (⟦PositiveTimeBorchersSequence.single 1 fn hfn⟧ : OSPreHilbertSpace OS)
          (⟦PositiveTimeBorchersSequence.single 1 fn hfn⟧ : OSPreHilbertSpace OS)‖ ≤ C := by
  let s := lgc.sobolev_index
  have hs_uniform : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      SchwartzMap.seminorm ℝ s i
        (onePointToFin1CLM d
          (((positiveTimeCompactSupportConvolution
              (⟨reflectedSchwartzSpacetime (φ_seq n),
                ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                  reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                    (hφ_compact n)⟩⟩)
              h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) ≤ C := by
    intro i
    exact
      positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_onePoint_seminorm_uniform_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball s i h
  have h0_uniform : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      SchwartzMap.seminorm ℝ 0 i
        (onePointToFin1CLM d
          (((positiveTimeCompactSupportConvolution
              (⟨reflectedSchwartzSpacetime (φ_seq n),
                ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                  reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                    (hφ_compact n)⟩⟩)
              h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) ≤ C := by
    intro i
    exact
      positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_onePoint_seminorm_uniform_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball 0 i h
  choose Cs hCs_nonneg hCs using hs_uniform
  choose C0 hC0_nonneg hC0 using h0_uniform
  let P : ℝ :=
    lgc.alpha * lgc.beta ^ 2 * ((2).factorial : ℝ) ^ lgc.gamma
  let B : ℝ :=
    2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
      (Cs i * C0 (s - i) + C0 i * Cs (s - i))
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    have halpha_nonneg : 0 ≤ lgc.alpha := le_of_lt lgc.alpha_pos
    have hbeta_nonneg : 0 ≤ lgc.beta ^ 2 := by
      exact pow_nonneg (le_of_lt lgc.beta_pos) _
    have hfac_nonneg : 0 ≤ ((2).factorial : ℝ) := by positivity
    have hrpow_nonneg : 0 ≤ ((2).factorial : ℝ) ^ lgc.gamma := by
      simpa using Real.rpow_nonneg hfac_nonneg lgc.gamma
    exact mul_nonneg (mul_nonneg halpha_nonneg hbeta_nonneg) hrpow_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact Finset.sum_nonneg (by
        intro i hi
        refine mul_nonneg (Nat.cast_nonneg _) ?_
        refine add_nonneg ?_ ?_
        · exact mul_nonneg (hCs_nonneg i) (hC0_nonneg (s - i))
        · exact mul_nonneg (hC0_nonneg i) (hCs_nonneg (s - i)))
  refine ⟨P * B, mul_nonneg hP_nonneg hB_nonneg, ?_⟩
  intro n
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let gn : positiveTimeCompactSupportSubmodule d := positiveTimeCompactSupportConvolution ψn h
  let fn : SchwartzNPoint d 1 := onePointToFin1CLM d (gn : SchwartzSpacetime d)
  let hfn : tsupport ((fn : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
      OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1Orbit_local (d := d)
      (gn : SchwartzSpacetime d) gn.property.1
  have hzero :
      VanishesToInfiniteOrderOnCoincidence (fn.osConjTensorProduct fn) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1) (f := fn) (g := fn) hfn hfn
  have hsingle :
      PositiveTimeBorchersSequence.osInner OS
        (PositiveTimeBorchersSequence.single 1 fn hfn)
        (PositiveTimeBorchersSequence.single 1 fn hfn) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (fn.osConjTensorProduct fn)) := by
    unfold PositiveTimeBorchersSequence.osInner
    simpa using
      (OSInnerProduct_single_single (d := d) OS.S OS.E0_linear 1 1 fn fn)
  have hgrowth :
      ‖OS.S 2 ⟨fn.osConjTensorProduct fn, hzero⟩‖ ≤
        P * SchwartzMap.seminorm ℝ s s (fn.osConjTensorProduct fn) := by
    simpa [P, s] using lgc.growth_estimate 2 ⟨fn.osConjTensorProduct fn, hzero⟩
  have htensor :
      SchwartzMap.seminorm ℝ s s (fn.osConjTensorProduct fn) ≤ B := by
    calc
      SchwartzMap.seminorm ℝ s s (fn.osConjTensorProduct fn)
          = SchwartzMap.seminorm ℝ s s (fn.osConj.tensorProduct fn) := by
              rfl
      _ ≤ 2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
            ((SchwartzMap.seminorm ℝ s i fn.osConj) * (SchwartzMap.seminorm ℝ 0 (s - i) fn) +
              (SchwartzMap.seminorm ℝ 0 i fn.osConj) * (SchwartzMap.seminorm ℝ s (s - i) fn)) :=
            SchwartzMap.tensorProduct_seminorm_le (p := s) (l := s) fn.osConj fn
      _ ≤ B := by
        dsimp [B]
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
        intro i hi
        have hfi : SchwartzMap.seminorm ℝ s i fn.osConj ≤ SchwartzMap.seminorm ℝ s i fn :=
          SchwartzNPoint.seminorm_osConj_le (d := d) s i fn
        have hf0i : SchwartzMap.seminorm ℝ 0 i fn.osConj ≤ SchwartzMap.seminorm ℝ 0 i fn :=
          SchwartzNPoint.seminorm_osConj_le (d := d) 0 i fn
        have hci : (0 : ℝ) ≤ ↑(s.choose i) := Nat.cast_nonneg _
        have h0_nonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 (s - i) fn := by
          exact apply_nonneg (SchwartzMap.seminorm ℝ 0 (s - i)) _
        have hs_nonneg : 0 ≤ SchwartzMap.seminorm ℝ s (s - i) fn := by
          exact apply_nonneg (SchwartzMap.seminorm ℝ s (s - i)) _
        have hfi_nonneg : 0 ≤ SchwartzMap.seminorm ℝ s i fn.osConj := by
          exact apply_nonneg (SchwartzMap.seminorm ℝ s i) _
        have hf0i_nonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 i fn.osConj := by
          exact apply_nonneg (SchwartzMap.seminorm ℝ 0 i) _
        apply mul_le_mul_of_nonneg_left ?_ hci
        refine add_le_add ?_ ?_
        · exact mul_le_mul (le_trans hfi (hCs i n)) (hC0 (s - i) n)
            h0_nonneg (hCs_nonneg i)
        · exact mul_le_mul (le_trans hf0i (hC0 i n)) (hCs (s - i) n)
            hs_nonneg (hC0_nonneg i)
  calc
    ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        (⟦PositiveTimeBorchersSequence.single 1 fn hfn⟧ : OSPreHilbertSpace OS)
        (⟦PositiveTimeBorchersSequence.single 1 fn hfn⟧ : OSPreHilbertSpace OS)‖
      = ‖OS.S 2 (ZeroDiagonalSchwartz.ofClassical (fn.osConjTensorProduct fn))‖ := by
          rw [OSPreHilbertSpace.inner_eq]
          rw [hsingle]
    _ = ‖OS.S 2 ⟨fn.osConjTensorProduct fn, hzero⟩‖ := by
          rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := fn.osConjTensorProduct fn) hzero]
    _ ≤ P * SchwartzMap.seminorm ℝ s s (fn.osConjTensorProduct fn) := hgrowth
    _ ≤ P * B := by exact mul_le_mul_of_nonneg_left htensor hP_nonneg
    _ = P * (2 ^ s *
          ∑ i ∈ Finset.range (s + 1),
            ↑(s.choose i) *
              (Cs i * C0 (s - i) + C0 i * Cs (s - i))) := by
          rfl

/-- Uniform OS semigroup-group bound for the regularized reflected-probe
one-point vectors. This is the orbit-side bound supplied by the VI.1
regularization stack. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_osSemigroupGroupMatrixElement_uniform_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
      let ψn : positiveTimeCompactSupportSubmodule d :=
        ⟨reflectedSchwartzSpacetime (φ_seq n),
          ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
            reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
              (hφ_compact n)⟩⟩
      let gn : positiveTimeCompactSupportSubmodule d :=
        positiveTimeCompactSupportConvolution ψn h
      let fn : SchwartzNPoint d 1 := onePointToFin1CLM d (gn : SchwartzSpacetime d)
      let hfn : tsupport ((fn : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
          OrderedPositiveTimeRegion d 1 :=
        onePointToFin1_tsupport_orderedPositiveTime_vi1Orbit_local (d := d)
          (gn : SchwartzSpacetime d) gn.property.1
      let xpre : OSPreHilbertSpace OS := (⟦PositiveTimeBorchersSequence.single 1 fn hfn⟧ :
        OSPreHilbertSpace OS)
      let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from xpre) : OSHilbertSpace OS))
      ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ ≤ C := by
  obtain ⟨C0, hC0_nonneg, hC0⟩ :=
    positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_inner_self_uniform_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball h
  refine ⟨2 * C0, by positivity, ?_⟩
  intro n t a ht
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let gn : positiveTimeCompactSupportSubmodule d := positiveTimeCompactSupportConvolution ψn h
  let fn : SchwartzNPoint d 1 := onePointToFin1CLM d (gn : SchwartzSpacetime d)
  let hfn : tsupport ((fn : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
      OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1Orbit_local (d := d)
      (gn : SchwartzSpacetime d) gn.property.1
  let xpre : OSPreHilbertSpace OS := (⟦PositiveTimeBorchersSequence.single 1 fn hfn⟧ :
    OSPreHilbertSpace OS)
  let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from xpre) : OSHilbertSpace OS))
  have hx_sq_eq :
      ‖x‖ ^ 2 =
        ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            xpre xpre‖ := by
    calc
      ‖x‖ ^ 2 = ‖@inner ℂ (OSHilbertSpace OS) _ x x‖ := by
        simpa using (norm_sq_eq (x := x))
      _ = ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            xpre xpre‖ := by
          rw [show x = (((show OSPreHilbertSpace OS from xpre) : OSHilbertSpace OS)) by rfl]
          rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
  have hx_sq_le : ‖x‖ ^ 2 ≤ C0 := by
    rw [hx_sq_eq]
    simpa [ψn, gn, fn, hfn, xpre] using hC0 n
  calc
    ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ ≤ 2 * ‖x‖ ^ 2 :=
      osSemigroupGroupMatrixElement_norm_le_two_mul_norm_sq_vi1Bounds_local
        (d := d) OS lgc x t a ht
    _ ≤ 2 * C0 := by
      exact mul_le_mul_of_nonneg_left hx_sq_le (by positivity)

end OSReconstruction
