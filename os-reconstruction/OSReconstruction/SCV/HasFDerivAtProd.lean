import Mathlib

noncomputable section

open scoped Topology

namespace OSReconstruction

section

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
private lemma segment_secondFiber_mem_ball
    (p h : E × F) {z : E} {δ : ℝ}
    (hz : z ∈ segment ℝ p.1 (p.1 + h.1))
    (hδ : ‖h‖ < δ) :
    (z, p.2 + h.2) ∈ Metric.ball p δ := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hz' : z ∈ Metric.closedBall p.1 (dist p.1 (p.1 + h.1)) :=
    (segment_subset_closedBall_left p.1 (p.1 + h.1)) hz
  have hz'' : ‖z - p.1‖ ≤ ‖h.1‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hprod : ‖h.1‖ ≤ ‖h‖ ∧ ‖h.2‖ ≤ ‖h‖ := (norm_prod_le_iff.mp le_rfl)
  rw [show (z, p.2 + h.2) - p = (z - p.1, h.2) by ext <;> simp, Prod.norm_def, max_lt_iff]
  exact ⟨lt_of_le_of_lt (hz''.trans hprod.1) hδ, lt_of_le_of_lt hprod.2 hδ⟩

/-- First-order product-domain differentiability from partial derivatives, in the
asymmetric form needed for the branch-`3b` joint Fourier argument. -/
theorem hasFDerivAt_of_partialFDerivsAt
    {f : E × F → G}
    {φE : E × F → E →L[ℝ] G}
    {φF : E × F → F →L[ℝ] G}
    (p : E × F)
    (hE : ∀ q : E × F, HasFDerivAt (fun e : E => f (e, q.2)) (φE q) q.1)
    (hF : HasFDerivAt (fun g : F => f (p.1, g)) (φF p) p.2)
    (hEcont : ContinuousAt φE p) :
    HasFDerivAt f
      ((φE p).comp (ContinuousLinearMap.fst ℝ E F) +
        (φF p).comp (ContinuousLinearMap.snd ℝ E F))
      p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  change
    (fun h : E × F =>
      f (p.1 + h.1, p.2 + h.2) - f p -
        (((φE p).comp (ContinuousLinearMap.fst ℝ E F) +
          (φF p).comp (ContinuousLinearMap.snd ℝ E F)) h)) =o[𝓝 0] fun h : E × F => h
  let A : E × F → G := fun h =>
    f (p.1 + h.1, p.2 + h.2) - f (p.1, p.2 + h.2) - φE p h.1
  let B : E × F → G := fun h =>
    f (p.1, p.2 + h.2) - f p - φF p h.2
  have hB0 :
      (fun k : F => f (p.1, p.2 + k) - f p - φF p k) =o[𝓝 0] fun k : F => k := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hasFDerivAt_iff_isLittleO_nhds_zero.1 hF)
  have hB_to_snd : B =o[𝓝 0] fun h : E × F => h.2 := by
    simpa [B] using hB0.comp_tendsto (ContinuousLinearMap.snd ℝ E F).continuous.continuousAt.tendsto
  have hB : B =o[𝓝 0] fun h : E × F => h := by
    exact hB_to_snd.trans_isBigO Asymptotics.isBigO_snd_prod'
  have hA : A =o[𝓝 0] fun h : E × F => h := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hcont_norm : ContinuousAt (fun q : E × F => ‖φE q - φE p‖) p :=
      (hEcont.sub continuousAt_const).norm
    have hc0 : (fun q : E × F => ‖φE q - φE p‖) p < c := by
      simpa using hc
    rcases Metric.mem_nhds_iff.1 (hcont_norm (Iio_mem_nhds hc0)) with ⟨δ, hδpos, hδ⟩
    filter_upwards [Metric.ball_mem_nhds (0 : E × F) hδpos] with h hh
    have hh' : ‖h‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hh
    let g : E → G := fun e => f (e, p.2 + h.2)
    have hder :
        ∀ x ∈ segment ℝ p.1 (p.1 + h.1),
          HasFDerivWithinAt g (φE (x, p.2 + h.2)) (segment ℝ p.1 (p.1 + h.1)) x := by
      intro x hx
      simpa [g] using (hE (x, p.2 + h.2)).hasFDerivWithinAt
    have hbound :
        ∀ x ∈ segment ℝ p.1 (p.1 + h.1), ‖φE (x, p.2 + h.2) - φE p‖ ≤ c := by
      intro x hx
      exact le_of_lt <| hδ <| segment_secondFiber_mem_ball p h hx hh'
    have hmv :=
      (convex_segment p.1 (p.1 + h.1)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (f := g) (f' := fun x => φE (x, p.2 + h.2)) (φ := φE p)
        hder hbound
        (left_mem_segment ℝ p.1 (p.1 + h.1))
        (right_mem_segment ℝ p.1 (p.1 + h.1))
    have hprod : ‖h.1‖ ≤ ‖h‖ ∧ ‖h.2‖ ≤ ‖h‖ := (norm_prod_le_iff.mp le_rfl)
    have hfst_le : ‖(p.1 + h.1) - p.1‖ ≤ ‖h‖ := by
      simpa using hprod.1
    have hA_bound : ‖A h‖ ≤ c * ‖h‖ := by
      have := hmv
      simpa [A, g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        this.trans <| mul_le_mul_of_nonneg_left hfst_le (le_of_lt hc)
    exact hA_bound
  have hsum : (fun h : E × F => A h + B h) =o[𝓝 0] fun h : E × F => h := hA.add hB
  simpa [A, B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] using hsum

/-- Finite-dimensional basis criterion for continuity into a CLM space over
`Fin n → ℝ`. -/
theorem continuousAt_clm_of_continuousAt_apply_basisFin
    {n : ℕ} {X : Type*} [PseudoMetricSpace X] {x₀ : X}
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : X → (Fin n → ℝ) →L[ℝ] G}
    (h : ∀ i : Fin n, ContinuousAt (fun x => φ x (Pi.single i (1 : ℝ))) x₀) :
    ContinuousAt φ x₀ := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set N : ℝ := (n : ℝ) + 1 with hN_def
  have hN_pos : 0 < N := by positivity
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have h_each :
      ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ < ε / N := by
    intro i
    have hi := h i
    rw [ContinuousAt, Metric.tendsto_nhds] at hi
    have := hi (ε / N) (by positivity)
    refine this.mono fun x hx => ?_
    simpa [ContinuousLinearMap.sub_apply, dist_eq_norm] using hx
  have h_ev :
      ∀ᶠ x in 𝓝 x₀,
        ∀ i : Fin n, ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ < ε / N := by
    have := (Filter.eventually_all_finset (I := (Finset.univ : Finset (Fin n)))
      (p := fun i x => ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ < ε / N)).mpr
      (fun i _ => h_each i)
    refine this.mono fun x hx i => hx i (Finset.mem_univ i)
  refine h_ev.mono fun x hx => ?_
  rw [dist_eq_norm]
  have hop_bound :
      ‖φ x - φ x₀‖ ≤ ∑ i : Fin n, ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun v => ?_)
    have hv_sum :
        v = ∑ i : Fin n, (v i : ℝ) • (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) := by
      funext j
      rw [Finset.sum_apply]
      simp [Pi.single_apply, Finset.mem_univ]
    have hbound_each : ∀ i : Fin n, |v i| ≤ ‖v‖ := fun i => by
      simpa [Real.norm_eq_abs] using (norm_le_pi_norm (v : Fin n → ℝ) i)
    calc ‖(φ x - φ x₀) v‖
        = ‖(φ x - φ x₀) (∑ i : Fin n,
              (v i : ℝ) • (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)))‖ := by
            rw [← hv_sum]
      _ = ‖∑ i : Fin n, (v i) • (φ x - φ x₀) (Pi.single i (1 : ℝ))‖ := by
          rw [map_sum]
          simp
      _ ≤ ∑ i : Fin n, ‖(v i) • (φ x - φ x₀) (Pi.single i (1 : ℝ))‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin n, |v i| * ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ := by
          simp [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin n, ‖v‖ * ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_right (hbound_each i) (norm_nonneg _)
      _ = (∑ i : Fin n, ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖) * ‖v‖ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
  have h_sum_bound :
      ∑ i : Fin n, ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ < ε := by
    have h_each_bd : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖ ≤ ε / N := fun i _ =>
      le_of_lt (hx i)
    have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
    calc ∑ i : Fin n, ‖(φ x - φ x₀) (Pi.single i (1 : ℝ))‖
        ≤ ∑ _ ∈ (Finset.univ : Finset (Fin n)), ε / N :=
            Finset.sum_le_sum h_each_bd
      _ = (n : ℝ) * (ε / N) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ < N * (ε / N) := by
            have hpos : 0 < ε / N := by positivity
            have hlt : (n : ℝ) < N := by simp [hN_def]
            exact (mul_lt_mul_of_pos_right hlt hpos)
      _ = ε := by field_simp [hN_ne]
  exact lt_of_le_of_lt hop_bound h_sum_bound

end

end OSReconstruction
