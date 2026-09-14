import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceClosure

/-!
# Uniform Schwartz closure of spatial clustering

Positivity and translation invariance bound translated pairings uniformly.
Thus clustering on dense test sets extends to full Schwartz space. No
analytic continuation, spectral condition, or reconstructed record is used.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d : Nat} [NeZero d]

private theorem uniform_conjTensor_approximation
    (W : (n : Nat) -> SchwartzNPoint d n →L[Complex] Complex)
    (hherm : ∀ n (f g : SchwartzNPoint d n),
      (∀ x, g x = starRingEnd Complex (f (fun i => x (Fin.rev i)))) ->
      W n g = starRingEnd Complex (W n f))
    (hpos : Wightman.IsPositiveDefinite d (fun n f => W n f))
    (htrans : IsTranslationInvariantWeak d (fun n f => W n f))
    (n m : Nat) (fK : Nat -> SchwartzNPoint d n) (f : SchwartzNPoint d n)
    (gK : Nat -> SchwartzNPoint d m) (g : SchwartzNPoint d m)
    (hfK : Tendsto fK atTop (𝓝 f)) (hgK : Tendsto gK atTop (𝓝 g))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ K in atTop, ∀ a : SpacetimeDim d,
      ‖W (n + m) (f.conjTensorProduct (translateSchwartzNPoint a g)) -
        W (n + m) ((fK K).conjTensorProduct (translateSchwartzNPoint a (gK K)))‖ < epsilon := by
  let Q := fun n (f : SchwartzNPoint d n) => (W (n + n) (f.conjTensorProduct f)).re
  have hlin n : IsLinearMap Complex (fun f => W n f) := ⟨(W n).map_add, (W n).map_smul⟩
  have hQ n : Continuous (Q n) :=
    Complex.continuous_re.comp ((W (n + n)).continuous.comp
      (conjTensorProduct_continuous_closure.comp (continuous_id.prodMk continuous_id)))
  have hQzero n : Q n 0 = 0 := by simp [Q]
  have hbound (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (a : SpacetimeDim d) :
      ‖W (n + m) (f.conjTensorProduct (translateSchwartzNPoint a g))‖ ^ 2 ≤
        2 * Q n f * Q m g := by
    have h := WightmanInnerProduct_norm_sq_le_two_mul_of (fun n f => W n f) hlin hherm hpos
      (BorchersSequence.single n f) (BorchersSequence.single m (translateSchwartzNPoint a g))
    simp only [WightmanInnerProduct_single_single d _ hlin] at h
    have heq := htrans (m + m) (-a) (g.conjTensorProduct g)
      ((translateSchwartzNPoint a g).conjTensorProduct (translateSchwartzNPoint a g)) (by
        intro x
        change ((translateSchwartzNPoint a g).conjTensorProduct
          (translateSchwartzNPoint a g)) x = (g.conjTensorProduct g) (fun i => x i + (-a))
        rw [SchwartzMap.conjTensorProduct_apply, SchwartzMap.conjTensorProduct_apply]
        simp only [translateSchwartzNPoint_apply]
        congr 1)
    change W (m + m) (g.conjTensorProduct g) = W (m + m)
      ((translateSchwartzNPoint a g).conjTensorProduct (translateSchwartzNPoint a g)) at heq
    rw [← heq] at h
    exact h
  have hfdiff : Tendsto (fun K => f - fK K) atTop (𝓝 0) := by
    simpa using (show Tendsto (fun _ : Nat => f) atTop (𝓝 f) from tendsto_const_nhds).sub hfK
  have hgdiff : Tendsto (fun K => g - gK K) atTop (𝓝 0) := by
    simpa using (show Tendsto (fun _ : Nat => g) atTop (𝓝 g) from tendsto_const_nhds).sub hgK
  have hQfdiff : Tendsto (fun K => Q n (f - fK K)) atTop (𝓝 0) := by
    simpa only [hQzero] using (hQ n).continuousAt.tendsto.comp hfdiff
  have hQgdiff : Tendsto (fun K => Q m (g - gK K)) atTop (𝓝 0) := by
    simpa only [hQzero] using (hQ m).continuousAt.tendsto.comp hgdiff
  have hA : Tendsto (fun K => 2 * Q n (f - fK K) * Q m g) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hQfdiff).mul tendsto_const_nhds
  have hB : Tendsto (fun K => 2 * Q n (fK K) * Q m (g - gK K)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((hQ n).continuousAt.tendsto.comp hfK)).mul hQgdiff
  have hsmall : 0 < (epsilon / 2) ^ 2 := sq_pos_of_pos (by linarith)
  filter_upwards [hA.eventually (gt_mem_nhds hsmall), hB.eventually (gt_mem_nhds hsmall)]
    with K hAK hBK
  intro a
  have hleft : ‖W (n + m) ((f - fK K).conjTensorProduct (translateSchwartzNPoint a g))‖ <
      epsilon / 2 := by
    have h := hbound (f - fK K) g a
    nlinarith [norm_nonneg (W (n + m) ((f - fK K).conjTensorProduct (translateSchwartzNPoint a g)))]
  have hright : ‖W (n + m) ((fK K).conjTensorProduct
      (translateSchwartzNPoint a (g - gK K)))‖ < epsilon / 2 := by
    have h := hbound (fK K) (g - gK K) a
    nlinarith [norm_nonneg (W (n + m) ((fK K).conjTensorProduct
      (translateSchwartzNPoint a (g - gK K))))]
  have hsplit : f.conjTensorProduct (translateSchwartzNPoint a g) -
      (fK K).conjTensorProduct (translateSchwartzNPoint a (gK K)) =
        (f - fK K).conjTensorProduct (translateSchwartzNPoint a g) +
          (fK K).conjTensorProduct (translateSchwartzNPoint a (g - gK K)) := by
    ext x
    simp only [SchwartzMap.sub_apply, SchwartzMap.add_apply,
      SchwartzMap.conjTensorProduct_apply, translateSchwartzNPoint_apply, map_sub]
    ring
  rw [← map_sub, hsplit, map_add]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Dense source clustering extends by a translation-uniform positive-form
estimate. The left slot is written in Borchers-conjugate convention. -/
theorem schwartz_cluster_of_dense_conjTensor
    (W : (n : Nat) -> SchwartzNPoint d n →L[Complex] Complex)
    (hherm : ∀ n (f g : SchwartzNPoint d n),
      (∀ x, g x = starRingEnd Complex (f (fun i => x (Fin.rev i)))) ->
      W n g = starRingEnd Complex (W n f))
    (hpos : Wightman.IsPositiveDefinite d (fun n f => W n f))
    (htrans : IsTranslationInvariantWeak d (fun n f => W n f))
    (n m : Nat) (D : Set (SchwartzNPoint d n)) (E : Set (SchwartzNPoint d m))
    (hD : Dense D) (hE : Dense E)
    (hsource : ∀ f ∈ D, ∀ g ∈ E, ∀ epsilon : Real, 0 < epsilon ->
      ∃ R : Real, 0 < R ∧ ∀ a : Fin d -> Real, (∑ i, (a i)^2) > R^2 ->
        ‖W (n + m) (f.conjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) g)) -
          starRingEnd Complex (W n f) * W m g‖ < epsilon)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Real, 0 < R ∧ ∀ a : Fin d -> Real, (∑ i, (a i)^2) > R^2 ->
      ‖W (n + m) (f.conjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) g)) -
        starRingEnd Complex (W n f) * W m g‖ < epsilon := by
  obtain ⟨fK, hfmem, hfK⟩ := mem_closure_iff_seq_limit.mp (hD f)
  obtain ⟨gK, hgmem, hgK⟩ := mem_closure_iff_seq_limit.mp (hE g)
  have happ := uniform_conjTensor_approximation W hherm hpos htrans n m fK f gK g hfK hgK
    (show 0 < epsilon / 3 by linarith)
  have hfactor : Tendsto (fun K => starRingEnd Complex (W n (fK K)) * W m (gK K)) atTop
      (𝓝 (starRingEnd Complex (W n f) * W m g)) :=
    (continuous_star.continuousAt.tendsto.comp ((W n).continuous.continuousAt.tendsto.comp hfK)).mul
      ((W m).continuous.continuousAt.tendsto.comp hgK)
  have hfac := (Metric.tendsto_nhds.mp hfactor) (epsilon / 3) (by linarith)
  obtain ⟨K, hKapp, hKfac⟩ := (happ.and hfac).exists
  obtain ⟨R, hR, hRK⟩ := hsource (fK K) (hfmem K) (gK K) (hgmem K)
    (epsilon / 3) (by linarith)
  refine ⟨R, hR, ?_⟩
  intro a ha
  let X := W (n + m) (f.conjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) g))
  let Y := W (n + m) ((fK K).conjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) (gK K)))
  let P := starRingEnd Complex (W n f) * W m g
  let Q := starRingEnd Complex (W n (fK K)) * W m (gK K)
  change ‖X - P‖ < epsilon
  have hxy : ‖X - Y‖ < epsilon / 3 := hKapp (Fin.cons 0 a)
  have hyq : ‖Y - Q‖ < epsilon / 3 := hRK a ha
  have hqp : ‖Q - P‖ < epsilon / 3 := by simpa only [dist_eq_norm] using hKfac
  calc
    ‖X - P‖ ≤ ‖X - Y‖ + ‖Y - Q‖ + ‖Q - P‖ := by
      have h1 := dist_triangle X Y P
      have h2 := dist_triangle Y Q P
      simp only [dist_eq_norm] at h1 h2
      linarith
    _ < epsilon := by linarith

end OSReconstruction
