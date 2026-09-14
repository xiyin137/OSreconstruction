/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEClustering









noncomputable section

open scoped Topology
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

local instance (n : ℕ) : AddCommGroup (ZeroDiagonalSchwartz d n) :=
  inferInstanceAs (AddCommGroup ↥(zeroDiagonalSubmodule d n))

/-- The actual reconstructed Schwinger functional on its zero-diagonal domain. -/
def rToESchwingerCLM (Wfn : WightmanFunctions d) (n : ℕ) :
    ZeroDiagonalSchwartz d n →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := constructSchwingerFunctions Wfn n
      map_add' := (constructedZeroDiagonalSchwinger_linear Wfn n).map_add
      map_smul' := (constructedZeroDiagonalSchwinger_linear Wfn n).map_smul }
  cont := constructedSchwinger_tempered_zeroDiagonal Wfn n

private def reflectedTensor {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    ZeroDiagonalSchwartz d (n + m) :=
  ⟨f.1.osConjTensorProduct g.1,
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f.1) (g := g.1) f.2 g.2⟩

/-- The reflected pairing on ordered positive-time Schwartz sources. -/
def rToEReflectedPairing (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) : ℂ :=
  rToESchwingerCLM Wfn (n + m) (reflectedTensor f g)

theorem rToEReflectedPairing_apply (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    rToEReflectedPairing Wfn f g =
      wickRotatedBoundaryPairing Wfn (n + m) (f.1.osConjTensorProduct g.1) := rfl

theorem continuous_rToEReflectedPairing (Wfn : WightmanFunctions d) (n m : ℕ) :
    Continuous (fun p : euclideanPositiveTimeSubmodule (d := d) n ×
      euclideanPositiveTimeSubmodule (d := d) m => rToEReflectedPairing Wfn p.1 p.2) := by
  apply (rToESchwingerCLM Wfn (n + m)).continuous.comp
  apply Continuous.subtype_mk
  exact (SchwartzNPoint.osConjTensorProduct_continuous (d := d) (n := n) (m := m)).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

private theorem ordered_compact_approximation {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    ∃ u : ℕ → euclideanPositiveTimeSubmodule (d := d) n,
      (∀ k, HasCompactSupport ((u k).1 : NPointDomain d n → ℂ)) ∧
      Tendsto u atTop (𝓝 f) := by
  let F := PositiveTimeBorchersSequence.single n f.1 f.2
  let U k := compactApproxPositiveTimeBorchers F k
  refine ⟨fun k => ⟨(U k).toBorchersSequence.funcs n, (U k).ordered_tsupport n⟩,
    fun k => compactApproxPositiveTimeBorchers_component_compact F k n, ?_⟩
  rw [tendsto_subtype_rng]
  simpa [U, F, PositiveTimeBorchersSequence.single] using
    tendsto_compactApproxPositiveTimeBorchers_component F n

private theorem wightman_sharp_bound (Wfn : WightmanFunctions d)
    (F G : BorchersSequence d) :
    ‖WightmanInnerProduct d Wfn.W F G‖ ^ 2 ≤
      (WightmanInnerProduct d Wfn.W F F).re *
        (WightmanInnerProduct d Wfn.W G G).re := by
  let w := WightmanInnerProduct d Wfn.W F G
  let H := starRingEnd ℂ w • G
  have hpair : (WightmanInnerProduct d Wfn.W F H).re = ‖w‖ ^ 2 := by
    rw [show H = starRingEnd ℂ w • G from rfl,
      WightmanInnerProduct_smul_right d Wfn.W Wfn.linear]
    change ((starRingEnd ℂ w) * w).re = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hself : (WightmanInnerProduct d Wfn.W H H).re =
      ‖w‖ ^ 2 * (WightmanInnerProduct d Wfn.W G G).re := by
    simp only [H, WightmanInnerProduct_smul_left d Wfn.W Wfn.linear,
      WightmanInnerProduct_smul_right d Wfn.W Wfn.linear]
    rw [show (starRingEnd ℂ) ((starRingEnd ℂ) w) = w from star_star w]
    rw [← mul_assoc, Complex.mul_conj, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]
  have hq := quadratic_nonneg_sq_le
    (WightmanInnerProduct d Wfn.W F F).re (WightmanInnerProduct d Wfn.W H H).re
    (WightmanInnerProduct d Wfn.W F H).re (Wfn.positive_definite F)
    (Wfn.positive_definite H) (fun t => by
      rw [← WightmanInnerProduct_quadratic_re_of Wfn.W Wfn.linear Wfn.hermitian F H t]
      exact Wfn.positive_definite _)
  rw [hpair, hself] at hq
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ^ 2 ≤ _
    rw [hw]
    simpa using mul_nonneg (Wfn.positive_definite F) (Wfn.positive_definite G)
  · have hwpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))
    nlinarith

private theorem compact_reflected_pairing_bound
    (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg : HasCompactSupport (g.1 : NPointDomain d m → ℂ)) :
    ‖rToEReflectedPairing Wfn f g‖ ^ 2 ≤
      (rToEReflectedPairing Wfn f f).re * (rToEReflectedPairing Wfn g g).re := by
  obtain ⟨φ, hφ⟩ := section43FrequencyProjection_surjective d n
    (section43FourierLaplaceTransformComponent d n f.1 f.2 hf)
  obtain ⟨ψ, hψ⟩ := section43FrequencyProjection_surjective d m
    (section43FourierLaplaceTransformComponent d m g.1 g.2 hg)
  simp only [rToEReflectedPairing_apply]
  rw [rToE_compact_pairing_eq_of_transformComponent Wfn f g hf hg φ ψ hφ hψ,
    rToE_compact_pairing_eq_of_transformComponent Wfn f f hf hf φ φ hφ hφ,
    rToE_compact_pairing_eq_of_transformComponent Wfn g g hg hg ψ ψ hψ hψ]
  simpa only [WightmanInnerProduct_single_single d Wfn.W Wfn.linear] using
    wightman_sharp_bound Wfn (BorchersSequence.single n φ) (BorchersSequence.single m ψ)

/-- The positive-form estimate extends to all ordered Schwartz sources. -/
theorem rToE_reflected_pairing_cauchy_schwarz (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    ‖rToEReflectedPairing Wfn f g‖ ^ 2 ≤
      (rToEReflectedPairing Wfn f f).re * (rToEReflectedPairing Wfn g g).re := by
  obtain ⟨u, hu, huf⟩ := ordered_compact_approximation f
  obtain ⟨v, hv, hvg⟩ := ordered_compact_approximation g
  have hfg := (continuous_rToEReflectedPairing Wfn n m).continuousAt.tendsto.comp
    (huf.prodMk_nhds hvg)
  have hff := (continuous_rToEReflectedPairing Wfn n n).continuousAt.tendsto.comp
    (huf.prodMk_nhds huf)
  have hgg := (continuous_rToEReflectedPairing Wfn m m).continuousAt.tendsto.comp
    (hvg.prodMk_nhds hvg)
  apply le_of_tendsto_of_tendsto
    (hfg.norm.pow 2)
    ((Complex.continuous_re.continuousAt.tendsto.comp hff).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hgg))
  exact Eventually.of_forall fun k => compact_reflected_pairing_bound Wfn (u k) (v k) (hu k) (hv k)

/-- The original coarse estimate used by the density arguments. -/
theorem rToE_reflected_pairing_bound (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    ‖rToEReflectedPairing Wfn f g‖ ^ 2 ≤
      2 * (rToEReflectedPairing Wfn f f).re * (rToEReflectedPairing Wfn g g).re := by
  have h := rToE_reflected_pairing_cauchy_schwarz Wfn f g
  nlinarith [sq_nonneg ‖rToEReflectedPairing Wfn f g‖]

private def spatialTranslate {n : ℕ} (a : Fin d → ℝ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨translateSchwartzNPoint (Fin.cons 0 a) f.1,
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (Fin.cons 0 a) (by simp) f.1 f.2⟩

private theorem reflected_pairing_translate_self (Wfn : WightmanFunctions d)
    {n : ℕ} (a : Fin d → ℝ) (f : euclideanPositiveTimeSubmodule (d := d) n) :
    rToEReflectedPairing Wfn (spatialTranslate a f) (spatialTranslate a f) =
      rToEReflectedPairing Wfn f f := by
  symm
  apply wickRotatedBoundaryPairing_translation_invariant Wfn (n + n)
    (-Fin.cons 0 a)
  intro x
  change ((translateSchwartzNPoint (Fin.cons 0 a) f.1).osConjTensorProduct
      (translateSchwartzNPoint (Fin.cons 0 a) f.1)) x =
    (f.1.osConjTensorProduct f.1) (fun i => x i + -Fin.cons 0 a)
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, translateSchwartzNPoint_apply]
  have harg : (fun i => (timeReflectionN d (splitFirst n n x)) i - Fin.cons 0 a) =
      timeReflectionN d (splitFirst n n (fun i => x i + -Fin.cons 0 a)) := by
    ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, timeReflection, splitFirst]
    · simp [timeReflectionN, timeReflection, splitFirst, hμ, sub_eq_add_neg]
  rw [harg]
  rfl

theorem rToEReflectedPairing_sub_left (Wfn : WightmanFunctions d) {n m : ℕ}
    (f h : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    rToEReflectedPairing Wfn (f - h) g =
      rToEReflectedPairing Wfn f g - rToEReflectedPairing Wfn h g := by
  have ht : reflectedTensor (f - h) g = reflectedTensor f g - reflectedTensor h g := by
    apply Subtype.ext
    ext x
    change ((f.1 - h.1).osConjTensorProduct g.1) x =
      (f.1.osConjTensorProduct g.1 - h.1.osConjTensorProduct g.1) x
    simp [SchwartzNPoint.osConjTensorProduct,
      SchwartzMap.tensorProduct_apply, SchwartzNPoint.osConj_apply, sub_mul]
  exact (congrArg (rToESchwingerCLM Wfn (n + m)) ht).trans (map_sub _ _ _)

theorem rToEReflectedPairing_sub_right (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g h : euclideanPositiveTimeSubmodule (d := d) m) :
    rToEReflectedPairing Wfn f (g - h) =
      rToEReflectedPairing Wfn f g - rToEReflectedPairing Wfn f h := by
  have ht : reflectedTensor f (g - h) = reflectedTensor f g - reflectedTensor f h := by
    apply Subtype.ext
    ext x
    change (f.1.osConjTensorProduct (g.1 - h.1)) x =
      (f.1.osConjTensorProduct g.1 - f.1.osConjTensorProduct h.1) x
    simp [SchwartzNPoint.osConjTensorProduct,
      SchwartzMap.tensorProduct_apply, mul_sub]
  exact (congrArg (rToESchwingerCLM Wfn (n + m)) ht).trans (map_sub _ _ _)

private theorem spatialTranslate_sub {n : ℕ} (a : Fin d → ℝ)
    (g h : euclideanPositiveTimeSubmodule (d := d) n) :
    spatialTranslate a (g - h) = spatialTranslate a g - spatialTranslate a h := by
  apply Subtype.ext
  exact map_sub _ _ _

private theorem pairing_zero (Wfn : WightmanFunctions d) (n : ℕ) :
    rToEReflectedPairing Wfn (0 : euclideanPositiveTimeSubmodule (d := d) n)
      (0 : euclideanPositiveTimeSubmodule (d := d) n) = 0 := by
  have ht : reflectedTensor (0 : euclideanPositiveTimeSubmodule (d := d) n)
      (0 : euclideanPositiveTimeSubmodule (d := d) n) = 0 := by
    apply Subtype.ext
    ext x
    simp [reflectedTensor]
  exact (congrArg (rToESchwingerCLM Wfn (n + n)) ht).trans (map_zero _)

attribute [local irreducible] rToEReflectedPairing

set_option backward.isDefEq.respectTransparency true in
/-- Approximation of reflected pairings is uniform over all spatial shifts. -/
private theorem rToE_reflected_pairing_uniform_approximation
    (Wfn : WightmanFunctions d) {n m : ℕ}
    (u : ℕ → euclideanPositiveTimeSubmodule (d := d) n)
    (v : ℕ → euclideanPositiveTimeSubmodule (d := d) m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hu : Tendsto u atTop (𝓝 f)) (hv : Tendsto v atTop (𝓝 g))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ a : Fin d → ℝ,
      ‖rToEReflectedPairing Wfn f (spatialTranslate a g) -
        rToEReflectedPairing Wfn (u k) (spatialTranslate a (v k))‖ < ε := by
  let Q n (f : euclideanPositiveTimeSubmodule (d := d) n) :=
    (rToEReflectedPairing Wfn f f).re
  have hQ n : Continuous (Q n) := by
    change Continuous (fun f : euclideanPositiveTimeSubmodule (d := d) n =>
      (rToEReflectedPairing Wfn f f).re)
    have hdiag : Continuous (fun f : euclideanPositiveTimeSubmodule (d := d) n => (f, f)) :=
      continuous_id.prodMk continuous_id
    have hp : Continuous (fun f : euclideanPositiveTimeSubmodule (d := d) n =>
        rToEReflectedPairing Wfn f f) :=
      (continuous_rToEReflectedPairing Wfn n n).comp hdiag
    exact Complex.continuous_re.comp hp
  have hQzero n : Q n 0 = 0 := by simp only [Q, pairing_zero, Complex.zero_re]
  have hdu : Tendsto (fun k => f - u k) atTop (𝓝 0) := by
    rw [tendsto_subtype_rng]
    have hu' := continuous_subtype_val.continuousAt.tendsto.comp hu
    simpa using
      (show Tendsto (fun _ : ℕ => f.1) atTop (𝓝 f.1) from tendsto_const_nhds).sub hu'
  have hdv : Tendsto (fun k => g - v k) atTop (𝓝 0) := by
    rw [tendsto_subtype_rng]
    have hv' := continuous_subtype_val.continuousAt.tendsto.comp hv
    simpa using
      (show Tendsto (fun _ : ℕ => g.1) atTop (𝓝 g.1) from tendsto_const_nhds).sub hv'
  have hQu : Tendsto (fun k => Q n (f - u k)) atTop (𝓝 0) := by
    simpa only [hQzero] using (hQ n).continuousAt.tendsto.comp hdu
  have hQv : Tendsto (fun k => Q m (g - v k)) atTop (𝓝 0) := by
    simpa only [hQzero] using (hQ m).continuousAt.tendsto.comp hdv
  have hA : Tendsto (fun k => 2 * Q n (f - u k) * Q m g) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hQu).mul tendsto_const_nhds
  have hB : Tendsto (fun k => 2 * Q n (u k) * Q m (g - v k)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((hQ n).continuousAt.tendsto.comp hu)).mul hQv
  have hsmall : 0 < (ε / 2) ^ 2 := sq_pos_of_pos (by linarith)
  filter_upwards [hA.eventually (gt_mem_nhds hsmall), hB.eventually (gt_mem_nhds hsmall)]
    with k hkA hkB
  intro a
  have hleft := rToE_reflected_pairing_bound Wfn (f - u k) (spatialTranslate a g)
  have hright := rToE_reflected_pairing_bound Wfn (u k) (spatialTranslate a (g - v k))
  rw [reflected_pairing_translate_self] at hleft hright
  have hleft' : ‖rToEReflectedPairing Wfn (f - u k) (spatialTranslate a g)‖ < ε / 2 := by
    change 2 * (rToEReflectedPairing Wfn (f - u k) (f - u k)).re *
      (rToEReflectedPairing Wfn g g).re < _ at hkA
    nlinarith [norm_nonneg (rToEReflectedPairing Wfn (f - u k) (spatialTranslate a g))]
  have hright' : ‖rToEReflectedPairing Wfn (u k) (spatialTranslate a (g - v k))‖ < ε / 2 := by
    change 2 * (rToEReflectedPairing Wfn (u k) (u k)).re *
      (rToEReflectedPairing Wfn (g - v k) (g - v k)).re < _ at hkB
    nlinarith [norm_nonneg (rToEReflectedPairing Wfn (u k) (spatialTranslate a (g - v k)))]
  have heq : rToEReflectedPairing Wfn f (spatialTranslate a g) -
      rToEReflectedPairing Wfn (u k) (spatialTranslate a (v k)) =
      rToEReflectedPairing Wfn (f - u k) (spatialTranslate a g) +
        rToEReflectedPairing Wfn (u k) (spatialTranslate a (g - v k)) := by
    rw [rToEReflectedPairing_sub_left, spatialTranslate_sub, rToEReflectedPairing_sub_right]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

private theorem continuous_ordered_scalar (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (fun f : euclideanPositiveTimeSubmodule (d := d) n =>
      wickRotatedBoundaryPairing Wfn n f.1) := by
  let lift : euclideanPositiveTimeSubmodule (d := d) n → ZeroDiagonalSchwartz d n :=
    fun f => ⟨f.1,
      VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion f.1 f.2⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  exact (rToESchwingerCLM Wfn n).continuous.comp hlift

/-- Reflected OS-I clustering for all ordered positive-time Schwartz sources,
without compact-support or Ruelle hypotheses. This proves the individual
terms in the finite-sequence E4 formula on printed page 88 of OS I. -/
theorem rToE_reflected_cluster (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : Fin d → ℝ, (∑ i, (a i)^2) > R^2 →
      ‖wickRotatedBoundaryPairing Wfn (n + m)
          (f.1.osConjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) g.1)) -
        starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) *
          wickRotatedBoundaryPairing Wfn m g.1‖ < ε := by
  obtain ⟨u, hu, huf⟩ := ordered_compact_approximation f
  obtain ⟨v, hv, hvg⟩ := ordered_compact_approximation g
  have happ := rToE_reflected_pairing_uniform_approximation Wfn u v f g huf hvg
    (show 0 < ε / 3 by linarith)
  let P (f : euclideanPositiveTimeSubmodule (d := d) n)
      (g : euclideanPositiveTimeSubmodule (d := d) m) :=
    starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) *
      wickRotatedBoundaryPairing Wfn m g.1
  have hfactor : Tendsto (fun k => P (u k) (v k)) atTop (𝓝 (P f g)) :=
    (continuous_star.continuousAt.tendsto.comp
      ((continuous_ordered_scalar Wfn n).continuousAt.tendsto.comp huf)).mul
      ((continuous_ordered_scalar Wfn m).continuousAt.tendsto.comp hvg)
  have hfac := Metric.tendsto_nhds.mp hfactor (ε / 3) (by linarith)
  obtain ⟨k, hkapp, hkfac⟩ := (happ.and hfac).exists
  obtain ⟨R, hR, hcluster⟩ :=
    rToE_compact_reflected_cluster Wfn (u k) (v k) (hu k) (hv k) (ε / 3) (by linarith)
  refine ⟨R, hR, ?_⟩
  intro a ha
  let X := rToEReflectedPairing Wfn f (spatialTranslate a g)
  let Y := rToEReflectedPairing Wfn (u k) (spatialTranslate a (v k))
  have hX : X = wickRotatedBoundaryPairing Wfn (n + m)
      (f.1.osConjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) g.1)) := by
    simpa only [X, spatialTranslate] using
      rToEReflectedPairing_apply Wfn f (spatialTranslate a g)
  rw [← hX]
  change ‖X - P f g‖ < ε
  have hxy : ‖X - Y‖ < ε / 3 := hkapp a
  have hyp : ‖Y - P (u k) (v k)‖ < ε / 3 := by
    simpa only [Y, P, rToEReflectedPairing_apply, spatialTranslate] using hcluster a ha
  have hpp : ‖P (u k) (v k) - P f g‖ < ε / 3 := by
    simpa only [dist_eq_norm] using hkfac
  have h1 := dist_triangle X Y (P f g)
  have h2 := dist_triangle Y (P (u k) (v k)) (P f g)
  simp only [dist_eq_norm] at h1 h2
  linarith

end OSReconstruction
