import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBoostFrequency
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVILorentzSupport
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Saturating temporal support by actual finite boosts

A finite sequence of coordinate boosts sends every future timelike covector
to a positive time axis. Negating each rapidity gives the inverse-transpose
action. This supplies the existing Lorentz transport interface directly from
finite boost invariance, without a physical-tube or spectrum premise.
-/

noncomputable section

open Complex Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat}

/-- Apply the listed actual coordinate boosts in their listed order. -/
def osiiBoostWordCLE (d : Nat) : List (Fin d × Real) ->
    (Fin (d + 1) -> Real) ≃L[Real] (Fin (d + 1) -> Real)
  | [] => ContinuousLinearEquiv.refl Real _
  | b :: w => (osiiPlanarBoostCLE d b.1 b.2).trans (osiiBoostWordCLE d w)

/-- The same finite sequence, diagonally in canonical momentum blocks. -/
def osiiFlatBoostWordCLE (d k : Nat) : List (Fin d × Real) ->
    (Fin (k * (d + 1)) -> Real) ≃L[Real] (Fin (k * (d + 1)) -> Real)
  | [] => ContinuousLinearEquiv.refl Real _
  | b :: w => (osiiFlatBoostCLE d k b.1 b.2).trans (osiiFlatBoostWordCLE d k w)

/-- Inverse transpose keeps the composition order and negates every rapidity. -/
def osiiDualBoostWord (w : List (Fin d × Real)) : List (Fin d × Real) :=
  w.map (fun b => (b.1, -b.2))

theorem osiiBoostWordCLE_append (w v : List (Fin d × Real)) :
    osiiBoostWordCLE d (w ++ v) = (osiiBoostWordCLE d w).trans (osiiBoostWordCLE d v) := by
  apply ContinuousLinearEquiv.ext
  funext x
  induction w generalizing x with
  | nil => rfl
  | cons b w ih => simp only [List.cons_append, osiiBoostWordCLE,
      ContinuousLinearEquiv.trans_apply, ih]

theorem osiiFlatBoostWordCLE_block (w : List (Fin d × Real))
    (p : Fin (k * (d + 1)) -> Real) (j : Fin k) (mu : Fin (d + 1)) :
    osiiFlatBoostWordCLE d k w p (finProdFinEquiv (j, mu)) =
      osiiBoostWordCLE d w (fun nu => p (finProdFinEquiv (j, nu))) mu := by
  induction w generalizing p with
  | nil => rfl
  | cons b w ih =>
    change osiiFlatBoostWordCLE d k w (osiiFlatBoostCLE d k b.1 b.2 p)
        (finProdFinEquiv (j, mu)) = _
    rw [ih]
    simp only [osiiFlatBoostCLE_block, osiiBoostWordCLE, ContinuousLinearEquiv.trans_apply]

theorem osiiBoostWordCLE_dual_pair (w : List (Fin d × Real))
    (x y : Fin (d + 1) -> Real) :
    dotProduct (osiiBoostWordCLE d w x) (osiiBoostWordCLE d (osiiDualBoostWord w) y) =
      dotProduct x y := by
  induction w generalizing x y with
  | nil => rfl
  | cons b w ih =>
    change dotProduct
        (osiiBoostWordCLE d w (osiiPlanarBoostCLE d b.1 b.2 x))
        (osiiBoostWordCLE d (osiiDualBoostWord w) (osiiPlanarBoostCLE d b.1 (-b.2) y)) = _
    rw [ih, osiiPlanarBoostCLE_dotProduct, ← osiiPlanarBoostCLE_symm,
      ContinuousLinearEquiv.apply_symm_apply]

theorem osiiFlatBoostWord_pairing_eq
    (T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex)
    (hBoost : ∀ (a : Fin d) (t : Real) (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex),
      T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) phi) = T phi)
    (w : List (Fin d × Real)) (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostWordCLE d k w) phi) =
      T phi := by
  induction w generalizing phi with
  | nil =>
    congr 1
  | cons b w ih =>
    rw [show SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (osiiFlatBoostWordCLE d k (b :: w)) phi =
        SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k b.1 b.2)
          (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostWordCLE d k w) phi)
      from by ext p; rfl]
    rw [hBoost, ih]

variable [NeZero d]

private theorem planarBoost_mem_forwardCone (a : Fin d) (t : Real)
    {y : Fin (d + 1) -> Real} (hy : InOpenForwardCone d y) :
    InOpenForwardCone d (osiiPlanarBoostCLE d a t y) := by
  exact (inOpenForwardCone_iff _).mp
    (BHW.real_lorentz_preserves_forwardCone (LorentzLieGroup.boostElement d a t) y
      ((inOpenForwardCone_iff y).mpr hy))

private theorem exists_planarBoost_zero_axis (a : Fin d)
    {y : Fin (d + 1) -> Real} (hy : InOpenForwardCone d y) :
    ∃ t : Real, osiiPlanarBoostCLE d a t y a.succ = 0 := by
  have hsum : (y a.succ) ^ 2 ≤ ∑ b : Fin d, (y b.succ) ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (y b.succ)) (Finset.mem_univ a)
  have hsq : (y a.succ) ^ 2 < (y 0) ^ 2 := by
    have h := hy.2
    rw [MinkowskiSpace.minkowskiNormSq_decomp] at h
    change -(y 0) ^ 2 + ∑ b : Fin d, (y b.succ) ^ 2 < 0 at h
    linarith
  have habs : |y a.succ| < y 0 :=
    (sq_lt_sq₀ (abs_nonneg _) hy.1.le).mp (by simpa only [sq_abs] using hsq)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hr : -y a.succ / y 0 ∈ Ioo (-1 : Real) 1 := by
    constructor
    · apply (lt_div_iff₀ hy.1).mpr
      linarith
    · apply (div_lt_iff₀ hy.1).mpr
      linarith
  let t := Real.artanh (-y a.succ / y 0)
  have hratio : Real.sinh t / Real.cosh t = -y a.succ / y 0 := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using Real.tanh_artanh hr
  have heq := (div_eq_div_iff (ne_of_gt (Real.cosh_pos t)) (ne_of_gt hy.1)).mp hratio
  refine ⟨t, ?_⟩
  rw [osiiPlanarBoostCLE_axis]
  linear_combination heq

private theorem exists_boostWord_zero_on (s : Finset (Fin d))
    {y : Fin (d + 1) -> Real} (hy : InOpenForwardCone d y) :
    ∃ w : List (Fin d × Real), InOpenForwardCone d (osiiBoostWordCLE d w y) ∧
      ∀ a ∈ s, osiiBoostWordCLE d w y a.succ = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨[], hy, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨w, hw, hz⟩ := ih
    obtain ⟨t, ht⟩ := exists_planarBoost_zero_axis a hw
    refine ⟨w ++ [(a, t)], ?_, ?_⟩
    · simpa [osiiBoostWordCLE_append, osiiBoostWordCLE] using planarBoost_mem_forwardCone a t hw
    · intro b hb
      rw [osiiBoostWordCLE_append]
      change osiiPlanarBoostCLE d a t (osiiBoostWordCLE d w y) b.succ = 0
      rcases Finset.mem_insert.mp hb with hba | hbs
      · subst b
        exact ht
      · rw [osiiPlanarBoostCLE_other a b (by intro h; subst b; exact ha hbs)]
        exact hz b hbs

/-- Coordinate boosts alone send every future timelike covector to a
positive multiple of the time axis, in every spatial dimension. -/
theorem exists_boostWord_timeAxis {y : Fin (d + 1) -> Real}
    (hy : InOpenForwardCone d y) :
    ∃ (w : List (Fin d × Real)) (r : Real), 0 < r ∧
      osiiBoostWordCLE d w y = Fin.cons r (fun _ : Fin d => 0) := by
  obtain ⟨w, hw, hz⟩ := exists_boostWord_zero_on Finset.univ hy
  refine ⟨w, osiiBoostWordCLE d w y 0, hw.1, ?_⟩
  ext mu
  refine Fin.cases ?_ (fun b => ?_) mu
  · rfl
  · exact hz b (Finset.mem_univ b)

theorem osiiFullFlatToTimeSpatialCLE_time
    (p : Fin (k * (d + 1)) -> Real) (j : Fin k) :
    (osiiFullFlatToTimeSpatialCLE d k p).1 j = p (finProdFinEquiv (j, 0)) := by
  let z := osiiFullFlatTimeSpatialReindexCLE d k p
  have hs := section43TimeSpatialFlatCLE_splitFirst d k
    ((section43TimeSpatialFlatCLE d k).symm z).1
    ((section43TimeSpatialFlatCLE d k).symm z).2
  simp only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply] at hs
  change ((section43TimeSpatialFlatCLE d k).symm z).1 j = _
  rw [← hs]
  change (osiiFullFlatTimeSpatialReindexCLE d k p) (Fin.castAdd (k * d) j) = _
  rw [← osiiFullFlatTimeSpatialIndexEquiv_time j]
  exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (k + k * d) => Real)
    (osiiFullFlatTimeSpatialIndexEquiv d k) p (finProdFinEquiv (j, 0))

theorem mem_osiiCanonicalFrequencyTemporalCylinder_iff
    (p : Fin (k * (d + 1)) -> Real) :
    p ∈ osiiCanonicalFrequencyTemporalCylinder d k ↔
      ∀ j : Fin k, 0 ≤ p (finProdFinEquiv (j, 0)) := by
  change (osiiFullFlatToTimeSpatialCLE d k p).1 ∈ DualConeFlat (osiiTimePositiveCone k) ↔ _
  rw [dualConeFlat_osiiTimePositiveCone]
  change (∀ j : Fin k, 0 ≤ (osiiFullFlatToTimeSpatialCLE d k p).1 j) ↔ _
  simp only [osiiFullFlatToTimeSpatialCLE_time]

/-- The existing Lorentz support handoff is produced from actual finite
coordinate boosts. The witness is a literal inverse-transpose boost word. -/
theorem osiiCanonicalFrequencyLorentzTransport_of_boosts
    (T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex)
    (hBoost : ∀ (a : Fin d) (t : Real) (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex),
      T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) phi) = T phi) :
    OSIICanonicalFrequencyLorentzTransport d k T := by
  intro j y hy
  obtain ⟨w, r, hr, hwy⟩ := exists_boostWord_timeAxis hy
  let e := osiiFlatBoostWordCLE d k (osiiDualBoostWord w)
  refine ⟨e, ?_, ?_⟩
  · intro phi
    have h := osiiFlatBoostWord_pairing_eq T hBoost (osiiDualBoostWord w)
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm phi)
    have hc : SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm phi) = phi := by
      ext p
      change phi (e.symm (e p)) = phi p
      rw [e.symm_apply_apply]
    rw [show osiiFlatBoostWordCLE d k (osiiDualBoostWord w) = e from rfl, hc] at h
    exact h.symm
  · intro p hp hep
    have ht := (mem_osiiCanonicalFrequencyTemporalCylinder_iff (e p)).mp hep j
    have hd := osiiBoostWordCLE_dual_pair w y (osiiCanonicalFrequencyParticleBlock d k p j)
    rw [hwy] at hd
    have hd' : r * osiiBoostWordCLE d (osiiDualBoostWord w)
        (osiiCanonicalFrequencyParticleBlock d k p j) 0 =
        dotProduct y (osiiCanonicalFrequencyParticleBlock d k p j) := by
      simpa [dotProduct, Fin.sum_univ_succ] using hd
    change ¬ 0 ≤ dotProduct y (osiiCanonicalFrequencyParticleBlock d k p j) at hp
    apply hp
    rw [← hd']
    apply mul_nonneg hr.le
    simpa only [e, osiiFlatBoostWordCLE_block, osiiCanonicalFrequencyParticleBlock] using ht

end OSReconstruction
