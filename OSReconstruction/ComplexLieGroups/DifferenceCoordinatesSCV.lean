import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.SCV.TubeDomainExtension

noncomputable section

open Complex

namespace BHW

variable {d n : ℕ}

/-- `SCV.TubeDomain` membership for flattened configurations is exactly
    the flattened-imaginary-part cone condition. -/
theorem mem_tubeDomain_flatProductForwardConeReal
    (ξ : Fin n → Fin (d + 1) → ℂ) :
    flattenCfg n d ξ ∈ SCV.TubeDomain (FlatProductForwardConeReal d n) ↔
      (fun i => (flattenCfg n d ξ i).im) ∈ FlatProductForwardConeReal d n := by
  rfl

/-- Forward tube rewritten as a `SCV.TubeDomain` statement via
    difference coordinates and flattening. -/
theorem forwardTube_iff_flattened_diff_tubeDomain [NeZero d]
    (z : Fin n → Fin (d + 1) → ℂ) :
    ForwardTube d n z ↔
      flattenCfg n d (diffCoordEquiv n d z) ∈
        SCV.TubeDomain (FlatProductForwardConeReal d n) := by
  rw [mem_tubeDomain_flatProductForwardConeReal]
  exact forwardTube_iff_flattened_diffCone (n := n) (d := d) z

/-- Flattened difference-coordinate chart map. -/
def toDiffFlat (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → (Fin (n * (d + 1)) → ℂ) :=
  fun z => flattenCfg n d (diffCoordEquiv n d z)

/-- Inverse chart from flattened difference coordinates back to configurations. -/
def fromDiffFlat (n d : ℕ) :
    (Fin (n * (d + 1)) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
  fun u => (diffCoordEquiv n d).symm (unflattenCfg n d u)

lemma toDiffFlat_fromDiffFlat (n d : ℕ) (u : Fin (n * (d + 1)) → ℂ) :
    toDiffFlat n d (fromDiffFlat n d u) = u := by
  unfold toDiffFlat fromDiffFlat
  simp [flatten_unflatten_cfg]

private theorem differentiable_unflattenCfg (n d : ℕ) :
    Differentiable ℂ (unflattenCfg n d :
      (Fin (n * (d + 1)) → ℂ) → (Fin n → Fin (d + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro k
  rw [differentiable_pi]
  intro μ
  simpa [unflattenCfg] using (differentiable_apply (finProdFinEquiv (k, μ)))

private theorem differentiable_fromDiffFlat (n d : ℕ) :
    Differentiable ℂ (fromDiffFlat n d) := by
  unfold fromDiffFlat
  exact (diffCoordEquiv n d).symm.differentiable.comp (differentiable_unflattenCfg n d)

private theorem isOpen_forwardTube' (n d : ℕ) [NeZero d] : IsOpen (ForwardTube d n) := by
  simpa [forwardTube_eq_diffCoord_preimage (n := n) (d := d)] using
    (isOpen_productForwardCone (n := n) (d := d)).preimage (diffCoordEquiv n d).continuous

/-- Transport holomorphicity from `ForwardTube` to flattened difference coordinates. -/
theorem differentiableOn_fromDiffFlat_of_holo [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n)) :
    DifferentiableOn ℂ (fun u : Fin (n * (d + 1)) → ℂ => F (fromDiffFlat n d u))
      (SCV.TubeDomain (FlatProductForwardConeReal d n)) := by
  intro u hu
  have hz : fromDiffFlat n d u ∈ ForwardTube d n := by
    have hziff :=
      (forwardTube_iff_flattened_diff_tubeDomain (d := d) (n := n) (fromDiffFlat n d u))
    have hflat_to : toDiffFlat n d (fromDiffFlat n d u) ∈
        SCV.TubeDomain (FlatProductForwardConeReal d n) := by
      simpa [toDiffFlat_fromDiffFlat (n := n) (d := d) u] using hu
    have hflat : flattenCfg n d (diffCoordEquiv n d (fromDiffFlat n d u)) ∈
        SCV.TubeDomain (FlatProductForwardConeReal d n) := by
      simpa [toDiffFlat] using hflat_to
    exact hziff.mpr hflat
  have hF_at : DifferentiableAt ℂ F (fromDiffFlat n d u) :=
    (hF_holo _ hz).differentiableAt ((isOpen_forwardTube' (n := n) (d := d)).mem_nhds hz)
  exact (hF_at.comp u (differentiable_fromDiffFlat n d u)).differentiableWithinAt

private theorem differentiable_negFlat (n d : ℕ) :
    Differentiable ℂ (fun u : Fin (n * (d + 1)) → ℂ => fun i => -u i) := by
  rw [differentiable_pi]
  intro i
  simpa using (differentiable_apply i).neg

/-- A `-`-twisted transport variant useful for opposite-tube EOW branches. -/
theorem differentiableOn_fromDiffFlat_neg_of_holo [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n)) :
    DifferentiableOn ℂ
      (fun u : Fin (n * (d + 1)) → ℂ => F (fromDiffFlat n d (fun i => -u i)))
      (SCV.TubeDomain (Neg.neg '' FlatProductForwardConeReal d n)) := by
  intro u hu
  have hu_neg : (fun i => -(u i).im) ∈ FlatProductForwardConeReal d n := by
    simpa [SCV.tubeDomain_neg] using hu
  have hneg_mem : (fun i => -u i) ∈ SCV.TubeDomain (FlatProductForwardConeReal d n) := by
    change (fun i => ((-u i)).im) ∈ FlatProductForwardConeReal d n
    simpa using hu_neg
  have hbase : DifferentiableOn ℂ
      (fun v : Fin (n * (d + 1)) → ℂ => F (fromDiffFlat n d v))
      (SCV.TubeDomain (FlatProductForwardConeReal d n)) :=
    differentiableOn_fromDiffFlat_of_holo (n := n) (d := d) F hF_holo
  have hAt : DifferentiableAt ℂ
      (fun v : Fin (n * (d + 1)) → ℂ => F (fromDiffFlat n d v))
      (fun i => -u i) :=
    (hbase _ hneg_mem).differentiableAt
      ((SCV.tubeDomain_isOpen
        (isOpen_flatProductForwardConeReal (n := n) (d := d))).mem_nhds hneg_mem)
  exact (hAt.comp u (differentiable_negFlat n d u)).differentiableWithinAt

/-- Direct flattened-coordinate instantiation of
    `SCV.edge_of_the_wedge_theorem` using
    `flatProductForwardConeReal_eowReady`. -/
theorem edge_of_the_wedge_flat_instantiation
    [NeZero d] [NeZero n]
    (f_plus f_minus : (Fin (n * (d + 1)) → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus
      (SCV.TubeDomain (FlatProductForwardConeReal d n)))
    (hf_minus : DifferentiableOn ℂ f_minus
      (SCV.TubeDomain (Neg.neg '' FlatProductForwardConeReal d n)))
    (E : Set (Fin (n * (d + 1)) → ℝ)) (hE : IsOpen E)
    (bv : (Fin (n * (d + 1)) → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus
        (nhdsWithin (SCV.realEmbed x)
          (SCV.TubeDomain (FlatProductForwardConeReal d n)))
        (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (SCV.realEmbed x)
          (SCV.TubeDomain (Neg.neg '' FlatProductForwardConeReal d n)))
        (nhds (bv x))) :
    ∃ (U : Set (Fin (n * (d + 1)) → ℂ)) (F : (Fin (n * (d + 1)) → ℂ) → ℂ),
      IsOpen U ∧
      (∀ x ∈ E, SCV.realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ SCV.TubeDomain (FlatProductForwardConeReal d n), F z = f_plus z) ∧
      (∀ z ∈ U ∩ SCV.TubeDomain (Neg.neg '' FlatProductForwardConeReal d n), F z = f_minus z) ∧
      (∀ (G : (Fin (n * (d + 1)) → ℂ) → ℂ), DifferentiableOn ℂ G U →
        (∀ z ∈ U ∩ SCV.TubeDomain (FlatProductForwardConeReal d n), G z = f_plus z) →
        ∀ z ∈ U, G z = F z) := by
  rcases flatProductForwardConeReal_eowReady (n := n) (d := d) with
    ⟨hC_open, hC_conv, hC0, hC_cone, hC_ne⟩
  simpa using SCV.edge_of_the_wedge_theorem
    (C := FlatProductForwardConeReal d n)
    hC_open hC_conv hC0 hC_cone hC_ne
    f_plus f_minus hf_plus hf_minus E hE bv hbv_cont hf_plus_bv hf_minus_bv

end BHW
