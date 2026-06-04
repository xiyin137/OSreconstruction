/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.Osgood
import OSReconstruction.SCV.TotallyRealIdentity

/-!
# OS II Malgrange-Zerner Log Domain

OS II V.1 passes from positive coefficient variables `u_i^mu` to logarithmic
variables `r_i^mu = log u_i^mu`.  The Malgrange-Zerner convex envelope is the
log-coordinate carrier `sum_i |Im r_i^mu| < pi / 2`.

This file records the neutral carrier geometry and the two analytic handoff
lemmas needed after the scalar MZ representative has been constructed:
Osgood on the exact carrier and the totally-real identity theorem on its real
edge.
-/

noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

/-- The OS-II V.1 log-coordinate MZ carrier with aperture `α`.

For the paper's domain use `α = Real.pi / 2`. -/
def osiiMZLogDomain (m : ℕ) (α : ℝ) : Set (Fin m → ℂ) :=
  {r | ∑ i : Fin m, |(r i).im| < α}

/-- The real edge of the log-coordinate carrier. -/
def osiiMZLogRealEmbed {m : ℕ} (x : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (x i : ℂ)

/-- The log-coordinate MZ carrier is open. -/
theorem isOpen_osiiMZLogDomain (m : ℕ) (α : ℝ) :
    IsOpen (osiiMZLogDomain m α) := by
  have hcont :
      Continuous fun r : Fin m → ℂ => ∑ i : Fin m, |(r i).im| := by
    exact continuous_finset_sum _ fun i _ =>
      (Complex.continuous_im.comp (continuous_apply i)).abs
  simpa [osiiMZLogDomain] using isOpen_lt hcont continuous_const

/-- The log-coordinate MZ carrier is convex. -/
theorem convex_osiiMZLogDomain (m : ℕ) (α : ℝ) :
    Convex ℝ (osiiMZLogDomain m α) := by
  intro z hz w hw a b ha hb hab
  simp only [osiiMZLogDomain, Set.mem_setOf_eq] at hz hw ⊢
  have hpoint : ∀ i : Fin m,
      |((a • z + b • w) i).im| ≤
        a * |(z i).im| + b * |(w i).im| := by
    intro i
    have him :
        ((a • z + b • w) i).im =
          a * (z i).im + b * (w i).im := by
      simp [Pi.smul_apply, Complex.add_im]
    rw [him]
    calc
      |a * (z i).im + b * (w i).im|
          ≤ |a * (z i).im| + |b * (w i).im| := abs_add_le _ _
      _ = a * |(z i).im| + b * |(w i).im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsum_le :
      (∑ i : Fin m, |((a • z + b • w) i).im|) ≤
        a * (∑ i : Fin m, |(z i).im|) +
          b * (∑ i : Fin m, |(w i).im|) := by
    calc
      (∑ i : Fin m, |((a • z + b • w) i).im|)
          ≤ ∑ i : Fin m,
              (a * |(z i).im| + b * |(w i).im|) :=
            Finset.sum_le_sum fun i _ => hpoint i
      _ = a * (∑ i : Fin m, |(z i).im|) +
            b * (∑ i : Fin m, |(w i).im|) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib]
  have hlt :
      a * (∑ i : Fin m, |(z i).im|) +
          b * (∑ i : Fin m, |(w i).im|) < α := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      simpa [hb1] using hw
    · by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by linarith
        simpa [ha1] using hz
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hzmul :
            a * (∑ i : Fin m, |(z i).im|) < a * α :=
          mul_lt_mul_of_pos_left hz ha_pos
        have hwmul :
            b * (∑ i : Fin m, |(w i).im|) < b * α :=
          mul_lt_mul_of_pos_left hw hb_pos
        have hαcomb : a * α + b * α = α := by
          calc
            a * α + b * α = (a + b) * α := by ring
            _ = α := by rw [hab]; ring
        linarith
  exact lt_of_le_of_lt hsum_le hlt

/-- Every real log-coordinate point lies on the real edge of the MZ carrier. -/
theorem osiiMZLogRealEmbed_mem
    {m : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin m → ℝ) :
    osiiMZLogRealEmbed x ∈ osiiMZLogDomain m α := by
  simp [osiiMZLogDomain, osiiMZLogRealEmbed, hα]

/-- For positive aperture, the log-coordinate MZ carrier is connected. -/
theorem isConnected_osiiMZLogDomain
    (m : ℕ) {α : ℝ} (hα : 0 < α) :
    IsConnected (osiiMZLogDomain m α) := by
  refine ⟨⟨0, ?_⟩, (convex_osiiMZLogDomain m α).isPreconnected⟩
  simpa [osiiMZLogDomain] using hα

/-- The paper's concrete aperture `π / 2` is positive. -/
theorem osiiMZLogDomain_pi_half_connected (m : ℕ) :
    IsConnected (osiiMZLogDomain m (Real.pi / 2)) := by
  exact isConnected_osiiMZLogDomain m (by positivity)

/-- Osgood handoff on the exact OS-II log-coordinate carrier.

Once Malgrange-Zerner has supplied a scalar function on
`sum_i |Im r_i| < alpha`, coordinate-slice holomorphy plus continuity on this
carrier implies joint holomorphy on the whole carrier. -/
theorem differentiableOn_osiiMZLogDomain_of_coordinate_slices
    {m : ℕ} {α : ℝ}
    (F : (Fin m → ℂ) → ℂ)
    (hcont : ContinuousOn F (osiiMZLogDomain m α))
    (hsep : ∀ z ∈ osiiMZLogDomain m α, ∀ i : Fin m,
      DifferentiableOn ℂ
        (fun w : ℂ => F (Function.update z i w))
        {w : ℂ | Function.update z i w ∈ osiiMZLogDomain m α}) :
    DifferentiableOn ℂ F (osiiMZLogDomain m α) := by
  apply SCV.osgood_lemma (isOpen_osiiMZLogDomain m α) F hcont
  intro z hz i
  have hupdate_cont :
      Continuous (fun w : ℂ => Function.update z i w) := by
    exact continuous_pi fun j => by
      by_cases hji : j = i
      · subst hji
        simpa [Function.update] using continuous_id
      · simpa [Function.update, hji] using continuous_const
  have hline_open :
      IsOpen {w : ℂ | Function.update z i w ∈ osiiMZLogDomain m α} :=
    (isOpen_osiiMZLogDomain m α).preimage hupdate_cont
  have hline_mem :
      z i ∈ {w : ℂ | Function.update z i w ∈ osiiMZLogDomain m α} := by
    have hupdate_self : Function.update z i (z i) = z := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [Function.update]
      · simp [Function.update, hji]
    simpa [hupdate_self] using hz
  exact (hsep z hz i).differentiableAt (hline_open.mem_nhds hline_mem)

/-- Exact-carrier real-edge identity theorem for the OS-II log domain. -/
theorem eqOn_osiiMZLogDomain_of_real_edge_agreement
    {m : ℕ} {α : ℝ} (hα : 0 < α)
    (F G : (Fin m → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (osiiMZLogDomain m α))
    (hG : DifferentiableOn ℂ G (osiiMZLogDomain m α))
    (hreal :
      ∀ x : Fin m → ℝ,
        F (osiiMZLogRealEmbed x) = G (osiiMZLogRealEmbed x)) :
    Set.EqOn F G (osiiMZLogDomain m α) := by
  intro z hz
  have hzero :
      SCV.realToComplex (0 : Fin m → ℝ) ∈ osiiMZLogDomain m α := by
    simpa [SCV.realToComplex] using
      osiiMZLogRealEmbed_mem (m := m) (α := α) hα (0 : Fin m → ℝ)
  have hreal' :
      ∀ x : Fin m → ℝ, SCV.realToComplex x ∈ osiiMZLogDomain m α →
        F (SCV.realToComplex x) = G (SCV.realToComplex x) := by
    intro x _
    simpa [osiiMZLogRealEmbed, SCV.realToComplex] using hreal x
  exact SCV.holomorphic_eq_of_eq_on_real_of_connected
    (isOpen_osiiMZLogDomain m α)
    (isConnected_osiiMZLogDomain m hα)
    hF hG hzero hreal' z hz

/-- Scalarized OS-II MZ handoff once the directional branches are already
holomorphic on the log carrier and have a common real-edge value.

The construction chooses one branch as the representative and uses the
totally-real identity theorem to prove that every other branch agrees with it
on `sum |Im r_q| < α`.  The remaining OS-specific producer is the proof of the
common real-edge Schwinger agreement for the directional branches. -/
theorem exists_osiiMZLog_representative_of_common_real_edge
    {m : ℕ} [Nonempty (Fin m)] {α : ℝ} (hα : 0 < α)
    (D : Fin m → (Fin m → ℂ) → ℂ)
    (hD : ∀ q, DifferentiableOn ℂ (D q) (osiiMZLogDomain m α))
    (realEdge : (Fin m → ℝ) → ℂ)
    (hreal : ∀ q x, D q (osiiMZLogRealEmbed x) = realEdge x) :
    ∃ Γ : (Fin m → ℂ) → ℂ,
      DifferentiableOn ℂ Γ (osiiMZLogDomain m α) ∧
        (∀ x : Fin m → ℝ, Γ (osiiMZLogRealEmbed x) = realEdge x) ∧
          ∀ q, Set.EqOn Γ (D q) (osiiMZLogDomain m α) := by
  classical
  let q₀ : Fin m := Classical.choice inferInstance
  refine ⟨D q₀, hD q₀, ?_, ?_⟩
  · intro x
    exact hreal q₀ x
  · intro q
    exact eqOn_osiiMZLogDomain_of_real_edge_agreement
      (m := m) (α := α) hα (D q₀) (D q)
      (hD q₀) (hD q) (fun x => (hreal q₀ x).trans (hreal q x).symm)

end OSReconstruction
