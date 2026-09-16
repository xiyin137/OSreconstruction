/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEPointClustering
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToERotatedSeparation
import OSReconstruction.GeneralResults.SchwartzWeightedFlatness
import OSReconstruction.Wightman.Reconstruction.WickRotation.RuelleClusterBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketUniformBounds
















noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace OSReconstruction
variable {d n : ℕ} [NeZero d]
set_option maxHeartbeats 800000

private def orderedBox (d n : ℕ) (M δ : ℝ) : Set (NPointDomain d n) :=
  {z | ‖z‖ ≤ 2*M+1 ∧ ∀ i, 1 ≤ z i 0 ∧ ∀ j, i < j → δ ≤ z j 0 - z i 0}

omit [NeZero d] in
private theorem orderedBox_isCompact (M δ : ℝ) : IsCompact (orderedBox d n M δ) := by
  have ht : IsClosed {z : NPointDomain d n |
      ∀ i, 1 ≤ z i 0 ∧ ∀ j, i < j → δ ≤ z j 0 - z i 0} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    refine (isClosed_le (continuous_const (y := (1 : ℝ)))
      (show Continuous (fun z : NPointDomain d n => z i 0) from by fun_prop)).inter ?_
    change IsClosed {z : NPointDomain d n | ∀ j, i < j → δ ≤ z j 0 - z i 0}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hij
    exact isClosed_le (continuous_const (y := δ))
      (show Continuous (fun z : NPointDomain d n => z j 0 - z i 0) from by fun_prop)
  have hc : IsClosed (orderedBox d n M δ) :=
    (isClosed_le continuous_norm continuous_const).inter ht
  refine (isCompact_closedBall (0 : NPointDomain d n) (2*M+1)).of_isClosed_subset hc ?_
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1

omit [NeZero d] in
private theorem orderedBox_subset_ordered (M δ : ℝ) (hδ : 0 < δ) :
    orderedBox d n M δ ⊆ OrderedPositiveTimeRegion d n := by
  intro z hz i
  refine ⟨lt_of_lt_of_le zero_lt_one (hz.2 i).1, fun j hij => ?_⟩
  have hgap := (hz.2 i).2 j hij
  linarith

omit [NeZero d] in
private theorem exists_uniform_point_gap (x : NPointDomain d n)
    (hx : Function.Injective x) (c : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin n, i ≠ j → δ ≤ c * ‖x i - x j‖ := by
  classical
  let P := {p : Fin n × Fin n // p.1 ≠ p.2}
  let f (p : P) := min 1 (c * ‖x p.1.1 - x p.1.2‖)
  have hf (p : P) : 0 < f p := by
    exact lt_min zero_lt_one (mul_pos hc (norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne p.2))))
  refine ⟨∏ p, f p, Finset.prod_pos (fun p _ => hf p), fun i j hij => ?_⟩
  have h := prod_le_factor_mul_pow_card f 1 (⟨(i,j),hij⟩ : P)
    (fun p => (hf p).le) (fun p => min_le_left _ _) le_rfl
  simp only [one_pow, mul_one] at h
  exact h.trans (min_le_right _ _)

omit [NeZero d] in
private theorem exists_sorted_in_orderedBox (z : NPointDomain d n)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hz : ‖z‖ ≤ M)
    (hgap : ∀ i j : Fin n, i ≠ j → δ ≤ |z i 0 - z j 0|) :
    ∃ π : Equiv.Perm (Fin n),
      (fun i => z (π i) + timeShiftVec d (M+1)) ∈ orderedBox d n M δ := by
  classical
  let π := Tuple.sort (fun i => z i 0)
  have hinj : Function.Injective (fun i => z i 0) := by
    intro i j hij
    by_contra hne
    have h := hgap i j hne
    change z i 0 = z j 0 at hij
    rw [hij, sub_self, abs_zero] at h
    linarith
  have hstrict : StrictMono ((fun i => z i 0) ∘ π) :=
    (Tuple.monotone_sort (fun i => z i 0)).strictMono_of_injective (hinj.comp π.injective)
  have hcoord (i : Fin n) (μ : Fin (d+1)) : |z i μ| ≤ M := by
    calc
      |z i μ| = ‖z i μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖z i‖ := norm_le_pi_norm (z i) μ
      _ ≤ ‖z‖ := norm_le_pi_norm z i
      _ ≤ M := hz
  refine ⟨π, ?_, fun i => ⟨?_, fun j hij => ?_⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro μ
    rw [Real.norm_eq_abs]
    change |z (π i) μ + (if μ = 0 then M+1 else 0)| ≤ 2*M+1
    by_cases hμ : μ = 0
    · rw [if_pos hμ]
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (by linarith : 0 ≤ M+1)]; linarith [hcoord (π i) μ])
    · rw [if_neg hμ, add_zero]
      linarith [hcoord (π i) μ]
  · change 1 ≤ z (π i) 0 + (M+1)
    linarith [(abs_le.mp (hcoord (π i) 0)).1]
  · change δ ≤ (z (π j) 0 + (M+1)) - (z (π i) 0 + (M+1))
    have hg := hgap (π i) (π j) (π.injective.ne (ne_of_lt hij))
    have hlt : z (π i) 0 < z (π j) 0 := hstrict hij
    rw [abs_of_neg (sub_neg.mpr hlt)] at hg
    linarith

omit [NeZero d] in
private theorem norm_timeReflectionN_le (z : NPointDomain d n) :
    ‖timeReflectionN d z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro μ
  have h : ‖z i μ‖ ≤ ‖z‖ := (norm_le_pi_norm (z i) μ).trans (norm_le_pi_norm z i)
  by_cases hμ : μ = 0
  · subst μ
    simpa [timeReflectionN, timeReflection] using h
  · simpa [timeReflectionN, timeReflection, hμ] using h

omit [NeZero d] in
private theorem exists_compact_rotated_ordered_family (x : NPointDomain d n)
    (hx : Function.Injective x) (c : ℝ) (hc : 0 < c) :
    ∃ K : Set (NPointDomain d n), IsCompact K ∧ K ⊆ OrderedPositiveTimeRegion d n ∧
      ∀ (R : Matrix (Fin (d+1)) (Fin (d+1)) ℝ), R.transpose * R = 1 →
        (∀ i j : Fin n, i ≠ j → c * ‖x i - x j‖ ≤ |R.mulVec (x i - x j) 0|) →
        ∃ π σ : Equiv.Perm (Fin n),
          (fun i => R.mulVec (x (π i)) + timeShiftVec d ((d+1 : ℝ)*‖x‖+1)) ∈ K ∧
          (fun i => timeReflection d (R.mulVec (x (σ i))) +
            timeShiftVec d ((d+1 : ℝ)*‖x‖+1)) ∈ K := by
  obtain ⟨δ, hδ, hdist⟩ := exists_uniform_point_gap x hx c hc
  let M : ℝ := (d+1 : ℝ)*‖x‖
  have hM : 0 ≤ M := by positivity
  refine ⟨orderedBox d n M δ, orderedBox_isCompact M δ,
    orderedBox_subset_ordered M δ hδ, fun R hR hproj => ?_⟩
  let z : NPointDomain d n := fun i => R.mulVec (x i)
  have hzn : ‖z‖ ≤ M := norm_matrix_mulVec_npoint_le_of_orthogonal R hR x
  have hzδ (i j : Fin n) (hij : i ≠ j) : δ ≤ |z i 0 - z j 0| := by
    simpa only [z, Matrix.mulVec_sub, Pi.sub_apply] using (hdist i j hij).trans (hproj i j hij)
  have hθn : ‖timeReflectionN d z‖ ≤ M := (norm_timeReflectionN_le z).trans hzn
  have hθδ (i j : Fin n) (hij : i ≠ j) :
      δ ≤ |timeReflectionN d z i 0 - timeReflectionN d z j 0| := by
    change δ ≤ |-z i 0 - -z j 0|
    rw [neg_sub_neg, abs_sub_comm]
    exact hzδ i j hij
  obtain ⟨π, hπ⟩ := exists_sorted_in_orderedBox z M δ hM hδ hzn hzδ
  obtain ⟨σ, hσ⟩ := exists_sorted_in_orderedBox (timeReflectionN d z) M δ hM hδ hθn hθδ
  exact ⟨π, σ, hπ, hσ⟩

private def kernel (Wfn : WightmanFunctions d) (x : NPointDomain d n) : ℂ :=
  F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (x i))

/-- Euclidean reflection reality at each time-injective configuration. -/
theorem rToE_point_kernel_timeReflection (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (hx : Function.Injective (fun i => x i 0)) :
    starRingEnd ℂ (F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (x i))) =
      F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (timeReflectionN d x i)) := by
  let r (y : NPointDomain d n) := fun i => timeReflection d (y (Fin.rev i))
  have hr : Continuous r := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    dsimp [r, timeReflection]
    split_ifs <;> fun_prop
  have href : Function.Injective (fun i => timeReflectionN d x i 0) := by
    intro i j hij
    apply hx
    simpa [timeReflectionN, timeReflection] using hij
  have hrx : Function.Injective (fun i => r x i 0) := by
    intro i j hij
    apply Fin.rev_injective
    apply hx
    simpa [r, timeReflection] using hij
  let S : Set (NPointDomain d n) := {y | starRingEnd ℂ (kernel Wfn y) = kernel Wfn (r y)}
  have hae : ∀ᵐ y : NPointDomain d n, y ∈ S := bhw_euclidean_reality_ae Wfn n
  have hs : x ∈ closure S := (Measure.dense_of_ae (μ := volume) hae) x
  haveI : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hs
  have hl : ContinuousAt (fun y => starRingEnd ℂ (kernel Wfn y)) x :=
    Complex.continuous_conj.continuousAt.comp
    (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
      (wick_mem_translatedPET_of_time_injective x hx))
  have hright := (continuousAt_euclidean_kernel_of_mem_translatedPET Wfn
    (wick_mem_translatedPET_of_time_injective (r x) hrx)).comp (f := r) (x := x) hr.continuousAt
  have hl' : Tendsto (fun y => starRingEnd ℂ (kernel Wfn y)) (𝓝[S] x)
      (𝓝 (starRingEnd ℂ (kernel Wfn x))) := hl.tendsto.mono_left nhdsWithin_le_nhds
  have hr' : Tendsto (fun y => kernel Wfn (r y)) (𝓝[S] x) (𝓝 (kernel Wfn (r x))) :=
    hright.tendsto.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ y in 𝓝[S] x, y ∈ S := self_mem_nhdsWithin
  have heq : starRingEnd ℂ (kernel Wfn x) = kernel Wfn (r x) :=
    tendsto_nhds_unique hl' (hr'.congr'
      (hmem.mono fun y hy => hy.symm))
  have hperm := F_ext_permutation_invariant_translated Wfn n Fin.revPerm (timeReflectionN d x)
    (wick_mem_translatedPET_of_time_injective _ href)
  exact heq.trans hperm.symm

private theorem kernel_rigid_reindex (Wfn : WightmanFunctions d)
    (x : NPointDomain d n)
    (hx : (fun i => wickRotatePoint (x i)) ∈ TranslatedPET d n)
    (R : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (π : Equiv.Perm (Fin n)) (b : SpacetimeDim d) :
    kernel Wfn x = kernel Wfn (fun i => R.mulVec (x (π i)) + b) := by
  let u := R.transpose.mulVec b
  let z : NPointDomain d n := fun i => x (π i) + u
  have hπ : (fun i => wickRotatePoint (x (π i))) ∈ TranslatedPET d n :=
    translatedPET_perm π hx
  have hz : (fun i => wickRotatePoint (z i)) ∈ TranslatedPET d n := by
    change (fun i => wickRotatePoint (fun μ => x (π i) μ + u μ)) ∈ TranslatedPET d n
    simp_rw [wickRotatePoint_add]
    exact translatedPET_translate hπ (wickRotatePoint u)
  have hperm := F_ext_permutation_invariant_translated Wfn n π x hx
  have htrans := F_ext_translation_invariant_translated Wfn n u (fun i => x (π i)) hπ hz
  have hrot := F_ext_rotation_invariant_translated Wfn n R hR hdet z hz
  have hRu : R.mulVec u = b := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, (mul_eq_one_comm.mp hR), Matrix.one_mulVec]
  have heq : (fun i => R.mulVec (z i)) = (fun i => R.mulVec (x (π i)) + b) := by
    funext i
    simp only [z, Matrix.mulVec_add, hRu]
  exact (hperm.trans htrans).trans (hrot.trans (congrArg (kernel Wfn) heq))

/-- One spatial radius works in every direction, without positive-time ordering. -/
theorem rToE_point_kernel_cluster_spatial_norm {m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hxy : Function.Injective (fun i => Fin.append x y i 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : SpacetimeDim d, a 0 = 0 → A < ‖a‖ →
      ‖F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (Fin.append x (fun j => y j + a) i)) -
        F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (x i)) *
          F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (y i))‖ < ε := by
  classical
  obtain ⟨c, hc, hgeometry⟩ :=
    rToE_exists_proper_rotation_separating_time_and_space (d := d) (n+m)
  have hxt : Function.Injective (fun i => x i 0) := by
    intro i j hij
    have h : Fin.castAdd m i = Fin.castAdd m j := hxy (by simpa using hij)
    simpa using h
  have hyt : Function.Injective (fun i => y i 0) := by
    intro i j hij
    have h : Fin.natAdd n i = Fin.natAdd n j := hxy (by simpa using hij)
    simpa using h
  have hxi : Function.Injective x := fun i j hij => hxt (congrArg (fun v => v 0) hij)
  have hyi : Function.Injective y := fun i j hij => hyt (congrArg (fun v => v 0) hij)
  obtain ⟨Kx, hKx, hKxo, hFx⟩ := exists_compact_rotated_ordered_family x hxi c hc
  obtain ⟨Ky, hKy, hKyo, hFy⟩ := exists_compact_rotated_ordered_family y hyi c hc
  obtain ⟨r, hr, hcluster⟩ := rToE_reflected_point_kernel_cluster_uniform_on_isCompact
    Wfn (Kx ×ˢ Ky) (hKx.prod hKy) (fun p hp => ⟨hKxo hp.1, hKyo hp.2⟩) ε hε
  let Mx : ℝ := (d+1 : ℝ)*‖x‖
  let My : ℝ := (d+1 : ℝ)*‖y‖
  let Tx : ℝ := Mx+1
  let Ty : ℝ := My+1
  let A : ℝ := (Mx+My+2+r)/c+1
  have hMx : 0 ≤ Mx := by positivity
  have hMy : 0 ≤ My := by positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, fun a ha0 ha => ?_⟩
  have hlarge : Mx+My+2+r < c*‖a‖ := by
    have hdiv : (Mx+My+2+r)/c < ‖a‖ := by dsimp [A] at ha; linarith
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hdiv
  obtain ⟨R, hR, hRdet, hRt, hRs, hRp⟩ := hgeometry (Fin.append x y) a ha0
  have hRx (i j : Fin n) (hij : i ≠ j) :
      c*‖x i - x j‖ ≤ |R.mulVec (x i - x j) 0| := by
    simpa using hRp (Fin.castAdd m i) (Fin.castAdd m j) (by simpa using hij)
  have hRy (i j : Fin m) (hij : i ≠ j) :
      c*‖y i - y j‖ ≤ |R.mulVec (y i - y j) 0| := by
    simpa using hRp (Fin.natAdd n i) (Fin.natAdd n j) (by simpa using hij)
  obtain ⟨_, σ, _, hα⟩ := hFx R hR hRx
  obtain ⟨τ, _, hβ, _⟩ := hFy R hR hRy
  let α : NPointDomain d n := fun i => timeReflection d (R.mulVec (x (σ i))) + timeShiftVec d Tx
  let β : NPointDomain d m := fun i => R.mulVec (y (τ i)) + timeShiftVec d Ty
  change α ∈ Kx at hα
  change β ∈ Ky at hβ
  have hαo := hKxo hα
  have hβo := hKyo hβ
  let t : ℝ := R.mulVec a 0 - Tx - Ty
  have ht : 0 ≤ t := by dsimp [t, Tx, Ty]; linarith
  have hsep : (∑ j : Fin d, (R.mulVec a j.succ)^2) > r^2 := by
    have hcr : r < c*‖a‖ := by linarith
    nlinarith
  let b : Fin d → ℝ := fun j => R.mulVec a j.succ
  have hcl := hcluster (α,β) ⟨hα,hβ⟩ 0 t le_rfl ht b hsep
  have hzero : (fun _ : Fin n => timeShiftVec d (0 : ℝ)) = 0 := by
    funext i μ
    simp [timeShiftVec]
  simp only [hzero, add_zero] at hcl
  let joint : NPointDomain d (n+m) := Fin.append (timeReflectionN d α)
    ((β + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 b)
  change ‖kernel Wfn joint - starRingEnd ℂ (kernel Wfn α) * kernel Wfn β‖ < ε at hcl
  have hαt : Function.Injective (fun i => α i 0) :=
    (show StrictMono (fun i => α i 0) from fun i j hij => (hαo i).2 j hij).injective
  have hαθ : timeReflectionN d α =
      (fun i => R.mulVec (x (σ i)) + timeShiftVec d (-Tx)) := by
    funext i μ
    refine Fin.cases ?_ (fun j => ?_) μ
    · simp [timeReflectionN, timeReflection, α, timeShiftVec, add_comm]
    · simp [timeReflectionN, timeReflection, α, timeShiftVec]
  have hαvalue : starRingEnd ℂ (kernel Wfn α) = kernel Wfn x := by
    have hrefl : starRingEnd ℂ (kernel Wfn α) = kernel Wfn (timeReflectionN d α) :=
      rToE_point_kernel_timeReflection Wfn α hαt
    rw [hrefl, hαθ]
    exact (kernel_rigid_reindex Wfn x (wick_mem_translatedPET_of_time_injective x hxt)
      R hR hRdet σ (timeShiftVec d (-Tx))).symm
  have hβvalue : kernel Wfn β = kernel Wfn y :=
    (kernel_rigid_reindex Wfn y (wick_mem_translatedPET_of_time_injective y hyt)
      R hR hRdet τ (timeShiftVec d Ty)).symm
  let ρ : Equiv.Perm (Fin (n+m)) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr σ τ)).trans finSumFinEquiv
  have hρl (i : Fin n) : ρ (Fin.castAdd m i) = Fin.castAdd m (σ i) := by simp [ρ]
  have hρr (i : Fin m) : ρ (Fin.natAdd n i) = Fin.natAdd n (τ i) := by simp [ρ]
  let orig : NPointDomain d (n+m) := Fin.append x (fun i => y i + a)
  have horigt : Function.Injective (fun i => orig i 0) := by
    have heq : (fun i => orig i 0) = (fun i => Fin.append x y i 0) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [orig]
      · simp [orig, ha0]
    rw [heq]
    exact hxy
  have horig := kernel_rigid_reindex Wfn orig (wick_mem_translatedPET_of_time_injective orig horigt)
    R hR hRdet ρ (timeShiftVec d (-Tx))
  have hjoint : joint = (fun i => R.mulVec (orig (ρ i)) + timeShiftVec d (-Tx)) := by
    funext i μ
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [joint, Fin.append_left, hρl, orig]
      refine Fin.cases ?_ (fun j => ?_) μ
      · simp [α, timeReflectionN, timeReflection, timeShiftVec, add_comm]
      · simp [α, timeReflectionN, timeReflection, timeShiftVec]
    · simp only [joint, Fin.append_right, hρr, orig]
      refine Fin.cases ?_ (fun j => ?_) μ
      · simp [β, timeShiftVec, Matrix.mulVec_add, t]
        ring
      · simp [β, timeShiftVec, Matrix.mulVec_add, b]
  have hJ : kernel Wfn joint = kernel Wfn orig := by
    rw [hjoint]
    exact horig.symm
  rw [hJ, hαvalue, hβvalue] at hcl
  exact hcl

/-- The actual point kernel clusters along the spatial cocompact filter. -/
theorem rToE_point_kernel_tendsto_spatial {m : ℕ} (Wfn : WightmanFunctions d)
    (x : NPointDomain d n) (y : NPointDomain d m)
    (hxy : Function.Injective (fun i => Fin.append x y i 0)) :
    Tendsto (fun a : Fin d → ℝ => F_ext_on_translatedPET_total Wfn
      (fun i => wickRotatePoint (Fin.append x (fun j => y j + Fin.cons 0 a) i)))
      (cocompact (Fin d → ℝ))
      (𝓝 (F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (x i)) *
        F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (y i)))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, _, hA⟩ := rToE_point_kernel_cluster_spatial_norm Wfn x y hxy ε hε
  have he : ∀ᶠ a : Fin d → ℝ in cocompact (Fin d → ℝ), A < ‖a‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop A)
  filter_upwards [he] with a ha
  have hn : ‖a‖ ≤ ‖(Fin.cons 0 a : SpacetimeDim d)‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
      simpa only [Fin.cons_succ] using norm_le_pi_norm (Fin.cons 0 a : SpacetimeDim d) j.succ
  rw [dist_eq_norm]
  exact hA (Fin.cons 0 a) (by simp) (ha.trans_le hn)

/-- Almost every joint configuration has the actual spatial cluster limit. -/
theorem rToE_point_kernel_tendsto_spatial_ae (m : ℕ) (Wfn : WightmanFunctions d) :
    ∀ᵐ z : NPointDomain d (n+m),
      Tendsto (fun a : Fin d → ℝ => F_ext_on_translatedPET_total Wfn (fun i =>
        wickRotatePoint (Fin.append (splitFirst n m z)
          (fun j => splitLast n m z j + Fin.cons 0 a) i)))
        (cocompact (Fin d → ℝ))
        (𝓝 (F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (splitFirst n m z i)) *
          F_ext_on_translatedPET_total Wfn (fun i => wickRotatePoint (splitLast n m z i)))) := by
  filter_upwards [ae_pairwise_distinct_timeCoords (d := d) (n := n+m)] with z hz
  have hsplit : Fin.append (splitFirst n m z) (splitLast n m z) = z := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [splitFirst]
    · simp [splitLast]
  apply rToE_point_kernel_tendsto_spatial Wfn (splitFirst n m z) (splitLast n m z)
  rw [hsplit]
  intro i j hij
  by_contra hne
  exact hz i j hne hij

omit [NeZero d] in
private theorem reflected_orderedBox_gap (M δ : ℝ) (hδ2 : δ ≤ 2)
    (x : NPointDomain d n) (hx : x ∈ orderedBox d n M δ) :
    ∀ i j : Fin (n+n), i ≠ j →
      δ ≤ |Fin.append (timeReflectionN d x) x i 0 -
        Fin.append (timeReflectionN d x) x j 0| := by
  have hgap (i j : Fin n) (hij : i ≠ j) : δ ≤ |x i 0 - x j 0| := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := (hx.2 i).2 j hlt
      exact h.trans (by simpa only [neg_sub] using neg_le_abs (x i 0 - x j 0))
    · exact ((hx.2 j).2 i hgt).trans (le_abs_self _)
  intro i j
  refine Fin.addCases (fun p => ?_) (fun p => ?_) i
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) j
    · intro hpq
      have hne : p ≠ q := fun h => hpq (congrArg (Fin.castAdd n) h)
      simp only [Fin.append_left]
      change δ ≤ |-x p 0 - -x q 0|
      rw [neg_sub_neg, abs_sub_comm]
      exact hgap p q hne
    · intro _
      simp only [Fin.append_left, Fin.append_right]
      change δ ≤ |-x p 0 - x q 0|
      rw [abs_of_neg (by linarith [(hx.2 p).1, (hx.2 q).1])]
      linarith [(hx.2 p).1, (hx.2 q).1]
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) j
    · intro _
      simp only [Fin.append_left, Fin.append_right]
      change δ ≤ |x p 0 - -x q 0|
      rw [abs_of_pos (by linarith [(hx.2 p).1, (hx.2 q).1])]
      linarith [(hx.2 p).1, (hx.2 q).1]
    · intro hpq
      have hne : p ≠ q := fun h => hpq (congrArg (Fin.natAdd n) h)
      simpa only [Fin.append_right] using hgap p q hne

omit [NeZero d] in
private theorem reflected_orderedBox_infDist_lower (M δ : ℝ) (hδ2 : δ ≤ 2)
    (x : NPointDomain d n) (hx : x ∈ orderedBox d n M δ)
    (hcoin : (CoincidenceLocus d (n+n)).Nonempty) :
    δ ≤ 2 * Metric.infDist (Fin.append (timeReflectionN d x) x)
      (CoincidenceLocus d (n+n)) := by
  let z : NPointDomain d (n+n) := Fin.append (timeReflectionN d x) x
  obtain ⟨i,j,hij,hbound⟩ := exists_pairDifference_le_two_infDist_CoincidenceLocus z hcoin
  have hcoord : |z i 0 - z j 0| ≤ ‖z i - z j‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z i - z j) 0
  exact ((reflected_orderedBox_gap M δ hδ2 x hx i j hij).trans hcoord).trans hbound

omit [NeZero d] in
private theorem reflected_orderedBox_norm_bound (M δ : ℝ) (hM : 0 ≤ M)
    (x : NPointDomain d n) (hx : x ∈ orderedBox d n M δ) :
    ‖Fin.append (timeReflectionN d x) x‖ ≤ 2*M+1 := by
  have hθ := (norm_timeReflectionN_le x).trans hx.1
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using (norm_le_pi_norm (timeReflectionN d x) j).trans hθ
  · simpa only [Fin.append_right] using (norm_le_pi_norm x j).trans hx.1

private theorem reflected_self_kernel_bound_on_orderedBox (Wfn : WightmanFunctions d)
    (hcoin : (CoincidenceLocus d (n+n)).Nonempty) :
    ∃ (C : ℝ) (N q : ℕ), 0 < C ∧
      ∀ M δ : ℝ, 0 ≤ M → 0 < δ → δ ≤ 1 →
      ∀ x ∈ orderedBox d n M δ,
        ‖kernel Wfn (Fin.append (timeReflectionN d x) x)‖ * δ^(q+1) ≤ C*(1+M)^N := by
  obtain ⟨C, N, q, hC, hgrowth⟩ :=
    wick_rotated_kernel_polynomial_growth_on_translatedPET (n := n+n) Wfn
  refine ⟨2^(q+1)*C*2^N, N, q, by positivity, fun M δ hM hδ hδ1 x hx => ?_⟩
  have hxo := orderedBox_subset_ordered M δ hδ hx
  have hg := hgrowth (Fin.append (timeReflectionN d x) x)
    (reflected_ordered_points_mem_translatedPET x x hxo hxo)
  let D := Metric.infDist (Fin.append (timeReflectionN d x) x) (CoincidenceLocus d (n+n))
  have hD : 0 ≤ D := Metric.infDist_nonneg
  have hδD : δ ≤ 2*D := reflected_orderedBox_infDist_lower M δ (by linarith) x hx hcoin
  have hnorm := reflected_orderedBox_norm_bound M δ hM x hx
  calc
    ‖kernel Wfn (Fin.append (timeReflectionN d x) x)‖ * δ^(q+1)
        ≤ ‖kernel Wfn (Fin.append (timeReflectionN d x) x)‖ * (2*D)^(q+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδD _) (norm_nonneg _)
    _ = 2^(q+1) * (‖kernel Wfn (Fin.append (timeReflectionN d x) x)‖ * D^(q+1)) := by
      rw [mul_pow]
      ring
    _ ≤ 2^(q+1) * (C*(1+‖Fin.append (timeReflectionN d x) x‖)^N) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤ 2^(q+1) * (C*(2*(1+M))^N) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact pow_le_pow_left₀ (by positivity) (by linarith) N
    _ = (2^(q+1)*C*2^N)*(1+M)^N := by
      rw [mul_pow]
      ring

omit [NeZero d] in
private theorem clear_min_regulator (K C D u ρ c : ℝ) (N p : ℕ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hu : 0 ≤ u)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ u) (hc : 0 < c)
    (hbound : K * (min 1 (c*ρ))^p ≤ C*(1+D*u)^N) :
    K*ρ^p ≤ C*(D+1)^N*(1+u)^(N+p)/(min 1 c)^p := by
  let b := min 1 c
  let δ := min 1 (c*ρ)
  have hb : 0 < b := lt_min zero_lt_one hc
  have hscale : b*ρ ≤ (1+u)*δ := by
    dsimp [δ]
    by_cases h : c*ρ ≤ 1
    · rw [min_eq_right h]
      calc
        b*ρ ≤ c*ρ := mul_le_mul_of_nonneg_right (min_le_right _ _) hρ
        _ ≤ (1+u)*(c*ρ) := by nlinarith [mul_nonneg hu (mul_nonneg hc.le hρ)]
    · rw [min_eq_left (le_of_not_ge h), mul_one]
      calc
        b*ρ ≤ ρ := by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (min_le_left 1 c) hρ
        _ ≤ 1+u := by linarith
  apply (le_div_iff₀ (pow_pos hb p)).2
  calc
    K*ρ^p*b^p = K*(b*ρ)^p := by rw [mul_pow]; ring
    _ ≤ K*((1+u)*δ)^p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hb.le hρ) hscale p) hK
    _ = (1+u)^p*(K*δ^p) := by rw [mul_pow]; ring
    _ ≤ (1+u)^p*(C*(1+D*u)^N) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (1+u)^p*(C*((D+1)*(1+u))^N) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) N
    _ = C*(D+1)^N*(1+u)^(N+p) := by rw [mul_pow, pow_add]; ring

private theorem reflected_self_kernel_weighted_bound (Wfn : WightmanFunctions d)
    (hcoin : (CoincidenceLocus d n).Nonempty) (c : ℝ) (hc : 0 < c) :
    ∃ (C : ℝ) (N q : ℕ), 0 < C ∧ ∀ (x α : NPointDomain d n),
      α ∈ orderedBox d n ((d+1 : ℝ)*‖x‖)
        (min 1 (c*Metric.infDist x (CoincidenceLocus d n))) →
      ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ *
        Metric.infDist x (CoincidenceLocus d n)^(q+1) ≤ C*(1+‖x‖)^N := by
  obtain ⟨z,i,j,hij,_⟩ := hcoin
  have hzero : (0 : NPointDomain d n) ∈ CoincidenceLocus d n := ⟨i,j,hij,rfl⟩
  have hself : (CoincidenceLocus d (n+n)).Nonempty :=
    ⟨0, Fin.castAdd n i, Fin.castAdd n j, by simpa using hij, rfl⟩
  obtain ⟨C,N,q,hC,hbound⟩ := reflected_self_kernel_bound_on_orderedBox Wfn hself
  let Cout : ℝ := C*(d+2 : ℝ)^N/(min 1 c)^(q+1)
  have hCout : 0 < Cout := by dsimp [Cout]; exact div_pos (by positivity) (pow_pos (lt_min zero_lt_one hc) _)
  refine ⟨Cout, N+(q+1), q, hCout, fun x α hα => ?_⟩
  let ρ := Metric.infDist x (CoincidenceLocus d n)
  have hρ : 0 ≤ ρ := Metric.infDist_nonneg
  have hρx : ρ ≤ ‖x‖ := by
    simpa only [dist_zero_right] using Metric.infDist_le_dist_of_mem hzero
  by_cases hρ0 : ρ = 0
  · change ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ * ρ^(q+1) ≤ _
    rw [hρ0, zero_pow (by omega), mul_zero]
    positivity
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρ0)
  have hδ : 0 < min 1 (c*ρ) := lt_min zero_lt_one (mul_pos hc hρpos)
  have hb := hbound ((d+1 : ℝ)*‖x‖) (min 1 (c*ρ)) (by positivity) hδ (min_le_left _ _) α hα
  have h := clear_min_regulator
    ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ C (d+1 : ℝ) ‖x‖ ρ c N (q+1)
    (norm_nonneg _) hC.le (by positivity) (norm_nonneg _) hρ hρx hc hb
  change ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ * ρ^(q+1) ≤ _
  convert h using 1
  dsimp [Cout]
  ring

private theorem reflected_self_kernel_test_majorant (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (hcoin : (CoincidenceLocus d n).Nonempty)
    (c : ℝ) (hc : 0 < c) :
    ∃ B : NPointDomain d n → ℝ, Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ (x α : NPointDomain d n),
        α ∈ orderedBox d n ((d+1 : ℝ)*‖x‖)
          (min 1 (c*Metric.infDist x (CoincidenceLocus d n))) →
        ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ * ‖f.1 x‖ ≤ B x := by
  obtain ⟨C,N,q,hC,hbound⟩ := reflected_self_kernel_weighted_bound Wfn hcoin c hc
  obtain ⟨B,hBi,hBn,hB⟩ :=
    SchwartzFlatness.schwartz_polynomial_kernel_integrable_majorant_uniform_pi f.1 q N
  refine ⟨fun x => C*B x, hBi.const_mul C, fun x => mul_nonneg hC.le (hBn x), ?_⟩
  intro x α hα
  exact hB (CoincidenceLocus d n) isClosed_CoincidenceLocus hcoin f.2 x
    ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ C (norm_nonneg _) (hbound x α hα)

private def pointRegulator (d n : ℕ) (c : ℝ) (x : NPointDomain d n) : ℝ := by
  classical
  exact if (CoincidenceLocus d n).Nonempty then min 1 (c*Metric.infDist x (CoincidenceLocus d n)) else 1

private theorem reflected_self_kernel_test_majorant_all_arities (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (c : ℝ) (hc : 0 < c) :
    ∃ B : NPointDomain d n → ℝ, Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ (x α : NPointDomain d n),
        α ∈ orderedBox d n ((d+1 : ℝ)*‖x‖) (pointRegulator d n c x) →
        ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ * ‖f.1 x‖ ≤ B x := by
  classical
  by_cases hcoin : (CoincidenceLocus d n).Nonempty
  · obtain ⟨B,hBi,hBn,hB⟩ := reflected_self_kernel_test_majorant Wfn f hcoin c hc
    exact ⟨B,hBi,hBn,fun x α hα => hB x α (by simpa only [pointRegulator, if_pos hcoin] using hα)⟩
  have hn : n ≤ 1 := by
    by_contra h
    apply hcoin
    exact ⟨0, ⟨0,by omega⟩, ⟨1,by omega⟩, by simp [Fin.ext_iff], rfl⟩
  interval_cases n
  · refine ⟨fun x => ‖kernel Wfn (0 : NPointDomain d 0)‖*‖f.1 x‖,
      f.1.integrable.norm.const_mul _, fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun x α hα => ?_⟩
    have heq : Fin.append (timeReflectionN d α) α = (0 : NPointDomain d 0) := by
      funext i
      exact Fin.elim0 i
    rw [heq]
  · have hself : (CoincidenceLocus d (1+1)).Nonempty :=
      ⟨0, (0 : Fin 2), (1 : Fin 2), by decide, rfl⟩
    obtain ⟨C,N,q,hC,hbound⟩ := reflected_self_kernel_bound_on_orderedBox Wfn hself
    let A : ℝ := C*(d+2 : ℝ)^N
    refine ⟨fun x => A*((1+‖x‖)^N*‖f.1 x‖),
      (schwartz_integrable_add_pow_mul (μ := volume) f.1 N).const_mul A,
      fun x => by dsimp [A]; positivity, fun x α hα => ?_⟩
    have hα' : α ∈ orderedBox d 1 ((d+1 : ℝ)*‖x‖) 1 := by
      simpa only [pointRegulator, if_neg hcoin] using hα
    have hb := hbound ((d+1 : ℝ)*‖x‖) 1 (by positivity) zero_lt_one le_rfl α hα'
    simp only [one_pow, mul_one] at hb
    have hp : (1+(d+1 : ℝ)*‖x‖)^N ≤ ((d+2 : ℝ)*(1+‖x‖))^N :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg x]) N
    calc
      ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ * ‖f.1 x‖
          ≤ (C*(1+(d+1 : ℝ)*‖x‖)^N)*‖f.1 x‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ (C*((d+2 : ℝ)*(1+‖x‖))^N)*‖f.1 x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (norm_nonneg _)
      _ = A*((1+‖x‖)^N*‖f.1 x‖) := by dsimp [A]; rw [mul_pow]; ring

omit [NeZero d] in
private theorem pointRegulator_pos (c : ℝ) (hc : 0 < c)
    (x : NPointDomain d n) (hx : Function.Injective x) :
    0 < pointRegulator d n c x := by
  classical
  unfold pointRegulator
  split_ifs with hcoin
  · have hnot : x ∉ CoincidenceLocus d n := by
      rintro ⟨i,j,hij,heq⟩
      exact hij (hx heq)
    exact lt_min zero_lt_one (mul_pos hc
      ((isClosed_CoincidenceLocus.notMem_iff_infDist_pos hcoin).mp hnot))
  · exact zero_lt_one

omit [NeZero d] in
private theorem pointRegulator_le_pair (c : ℝ) (hc : 0 ≤ c)
    (x : NPointDomain d n) (i j : Fin n) (hij : i ≠ j) :
    pointRegulator d n c x ≤ c*‖x i - x j‖ := by
  classical
  have hcoin : (CoincidenceLocus d n).Nonempty := ⟨0,i,j,hij,rfl⟩
  rw [pointRegulator, if_pos hcoin]
  exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left
    (infDist_CoincidenceLocus_le_pairDifference x i j hij) hc)

omit [NeZero d] in
private theorem integrable_split_product {m : ℕ}
    (F : NPointDomain d n → ℝ) (G : NPointDomain d m → ℝ)
    (hF : Integrable F) (hG : Integrable G) :
    Integrable (fun z : NPointDomain d (n+m) =>
      F (splitFirst n m z) * G (splitLast n m z)) := by
  let e := MeasurableEquiv.finAddProd n m (SpacetimeDim d)
  have he (z : NPointDomain d (n+m)) :
      e z = (splitFirst n m z, splitLast n m z) := by
    have hs : e.symm (splitFirst n m z, splitLast n m z) = z := by
      rw [MeasurableEquiv.finAddProd_symm_apply]
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [splitFirst]
      · simp [splitLast]
    calc
      e z = e (e.symm (splitFirst n m z, splitLast n m z)) := congrArg e hs.symm
      _ = (splitFirst n m z, splitLast n m z) := e.apply_symm_apply _
  have h := (volume_preserving_finAddProd n m (SpacetimeDim d)).integrable_comp_of_integrable
    (hF.mul_prod hG)
  change Integrable ((fun z => F z.1 * G z.2) ∘ e) at h
  exact h.congr (Filter.Eventually.of_forall fun z => by
    simp only [Function.comp_apply, he])

omit [NeZero d] in
private theorem exists_regulated_rotated_ordered_normalization
    (x : NPointDomain d n) (hx : Function.Injective x) (c : ℝ) (hc : 0 < c)
    (R : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hR : R.transpose * R = 1)
    (hproj : ∀ i j : Fin n, i ≠ j → c*‖x i - x j‖ ≤ |R.mulVec (x i - x j) 0|) :
    ∃ π σ : Equiv.Perm (Fin n),
      (fun i => R.mulVec (x (π i)) + timeShiftVec d ((d+1 : ℝ)*‖x‖+1)) ∈
        orderedBox d n ((d+1 : ℝ)*‖x‖) (pointRegulator d n c x) ∧
      (fun i => timeReflection d (R.mulVec (x (σ i))) +
        timeShiftVec d ((d+1 : ℝ)*‖x‖+1)) ∈
        orderedBox d n ((d+1 : ℝ)*‖x‖) (pointRegulator d n c x) := by
  let δ := pointRegulator d n c x
  have hδ : 0 < δ := pointRegulator_pos c hc x hx
  let M : ℝ := (d+1 : ℝ)*‖x‖
  have hM : 0 ≤ M := by positivity
  let z : NPointDomain d n := fun i => R.mulVec (x i)
  have hzn : ‖z‖ ≤ M := norm_matrix_mulVec_npoint_le_of_orthogonal R hR x
  have hzδ (i j : Fin n) (hij : i ≠ j) : δ ≤ |z i 0 - z j 0| := by
    simpa only [z, Matrix.mulVec_sub, Pi.sub_apply] using
      (pointRegulator_le_pair c hc.le x i j hij).trans (hproj i j hij)
  have hθn : ‖timeReflectionN d z‖ ≤ M := (norm_timeReflectionN_le z).trans hzn
  have hθδ (i j : Fin n) (hij : i ≠ j) :
      δ ≤ |timeReflectionN d z i 0 - timeReflectionN d z j 0| := by
    change δ ≤ |-z i 0 - -z j 0|
    rw [neg_sub_neg, abs_sub_comm]
    exact hzδ i j hij
  obtain ⟨π, hπ⟩ := exists_sorted_in_orderedBox z M δ hM hδ hzn hzδ
  obtain ⟨σ, hσ⟩ := exists_sorted_in_orderedBox (timeReflectionN d z) M δ hM hδ hθn hθδ
  exact ⟨π, σ, hπ, hσ⟩

/-- One integrable envelope controls all relatively separated spatial block kernels. -/
theorem rToE_spatial_bulk_kernel_test_majorant {m : ℕ} (Wfn : WightmanFunctions d)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m) :
    ∃ (L : ℝ) (B : NPointDomain d (n+m) → ℝ),
      0 < L ∧ Integrable B ∧ (∀ z, 0 ≤ B z) ∧
      ∀ (x : NPointDomain d n) (y : NPointDomain d m),
        Function.Injective (fun i => Fin.append x y i 0) →
        ∀ a : SpacetimeDim d, a 0 = 0 → L*(1+‖Fin.append x y‖) < ‖a‖ →
        ‖F_ext_on_translatedPET_total Wfn
          (fun i => wickRotatePoint (Fin.append x (fun j => y j + a) i))‖ *
          ‖f.1 x‖ * ‖g.1 y‖ ≤
          B (Fin.append x y) := by
  classical
  obtain ⟨c,hc,hgeometry⟩ :=
    rToE_exists_proper_rotation_separating_time_and_space (d := d) (n+m)
  obtain ⟨F,hFi,hFn,hF⟩ := reflected_self_kernel_test_majorant_all_arities Wfn f c hc
  obtain ⟨G,hGi,hGn,hG⟩ := reflected_self_kernel_test_majorant_all_arities Wfn g c hc
  let B : NPointDomain d (n+m) → ℝ := fun z =>
    F (splitFirst n m z)*‖g.1 (splitLast n m z)‖ +
      ‖f.1 (splitFirst n m z)‖*G (splitLast n m z)
  let L : ℝ := (2*(d+1 : ℝ)+2)/c
  refine ⟨L,B,by dsimp [L]; positivity,
    (integrable_split_product F (fun y => ‖g.1 y‖) hFi g.1.integrable.norm).add
      (integrable_split_product (fun x => ‖f.1 x‖) G f.1.integrable.norm hGi),
    fun z => add_nonneg (mul_nonneg (hFn _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (hGn _)), fun x y hxy a ha0 ha => ?_⟩
  have hxt : Function.Injective (fun i => x i 0) := by
    intro i j hij
    have h : Fin.castAdd m i = Fin.castAdd m j := hxy (by simpa using hij)
    simpa using h
  have hyt : Function.Injective (fun i => y i 0) := by
    intro i j hij
    have h : Fin.natAdd n i = Fin.natAdd n j := hxy (by simpa using hij)
    simpa using h
  have hxi : Function.Injective x := fun i j hij => hxt (congrArg (fun v => v 0) hij)
  have hyi : Function.Injective y := fun i j hij => hyt (congrArg (fun v => v 0) hij)
  have hxn : ‖x‖ ≤ ‖Fin.append x y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    simpa using norm_le_pi_norm (Fin.append x y) (Fin.castAdd m i)
  have hyn : ‖y‖ ≤ ‖Fin.append x y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    simpa using norm_le_pi_norm (Fin.append x y) (Fin.natAdd n i)
  let Mx : ℝ := (d+1 : ℝ)*‖x‖
  let My : ℝ := (d+1 : ℝ)*‖y‖
  let Tx : ℝ := Mx+1
  let Ty : ℝ := My+1
  have hlarge : Mx+My+2 < c*‖a‖ := by
    have hdiv : (2*(d+1 : ℝ)+2)*(1+‖Fin.append x y‖)/c < ‖a‖ := by
      simpa only [L, div_mul_eq_mul_div] using ha
    have hb := (div_lt_iff₀ hc).mp hdiv
    dsimp [Mx,My]
    nlinarith [norm_nonneg (Fin.append x y)]
  obtain ⟨R,hR,hRdet,hRt,_,hRp⟩ := hgeometry (Fin.append x y) a ha0
  have hRx (i j : Fin n) (hij : i ≠ j) :
      c*‖x i - x j‖ ≤ |R.mulVec (x i - x j) 0| := by
    simpa using hRp (Fin.castAdd m i) (Fin.castAdd m j) (by simpa using hij)
  have hRy (i j : Fin m) (hij : i ≠ j) :
      c*‖y i - y j‖ ≤ |R.mulVec (y i - y j) 0| := by
    simpa using hRp (Fin.natAdd n i) (Fin.natAdd n j) (by simpa using hij)
  obtain ⟨_,σ,_,hα⟩ := exists_regulated_rotated_ordered_normalization x hxi c hc R hR hRx
  obtain ⟨τ,_,hβ,_⟩ := exists_regulated_rotated_ordered_normalization y hyi c hc R hR hRy
  let α : NPointDomain d n := fun i => timeReflection d (R.mulVec (x (σ i))) + timeShiftVec d Tx
  let β : NPointDomain d m := fun i => R.mulVec (y (τ i)) + timeShiftVec d Ty
  have hαo : α ∈ OrderedPositiveTimeRegion d n :=
    orderedBox_subset_ordered Mx _ (pointRegulator_pos c hc x hxi) hα
  have hβo : β ∈ OrderedPositiveTimeRegion d m :=
    orderedBox_subset_ordered My _ (pointRegulator_pos c hc y hyi) hβ
  let t : ℝ := R.mulVec a 0 - Tx - Ty
  have ht : 0 ≤ t := by dsimp [t,Tx,Ty]; linarith
  let b : Fin d → ℝ := fun j => R.mulVec a j.succ
  have hcl := rToE_reflected_point_kernel_uniform_timeSpace_bound
    Wfn α β hαo hβo 0 t le_rfl ht b
  have hzero : (fun _ : Fin n => timeShiftVec d (0 : ℝ)) = 0 := by
    funext i μ
    simp [timeShiftVec]
  simp only [hzero,add_zero] at hcl
  let joint : NPointDomain d (n+m) := Fin.append (timeReflectionN d α)
    ((β + fun _ => timeShiftVec d t) + fun _ => Fin.cons 0 b)
  change ‖kernel Wfn joint‖^2 ≤
    ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖ *
      ‖kernel Wfn (Fin.append (timeReflectionN d β) β)‖ at hcl
  let ρ : Equiv.Perm (Fin (n+m)) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr σ τ)).trans finSumFinEquiv
  have hρl (i : Fin n) : ρ (Fin.castAdd m i) = Fin.castAdd m (σ i) := by simp [ρ]
  have hρr (i : Fin m) : ρ (Fin.natAdd n i) = Fin.natAdd n (τ i) := by simp [ρ]
  let orig : NPointDomain d (n+m) := Fin.append x (fun i => y i + a)
  have horigt : Function.Injective (fun i => orig i 0) := by
    have heq : (fun i => orig i 0) = (fun i => Fin.append x y i 0) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [orig]
      · simp [orig,ha0]
    rw [heq]
    exact hxy
  have horig := kernel_rigid_reindex Wfn orig (wick_mem_translatedPET_of_time_injective orig horigt)
    R hR hRdet ρ (timeShiftVec d (-Tx))
  have hjoint : joint = (fun i => R.mulVec (orig (ρ i)) + timeShiftVec d (-Tx)) := by
    funext i μ
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [joint,Fin.append_left,hρl,orig]
      refine Fin.cases ?_ (fun j => ?_) μ
      · simp [α,timeReflectionN,timeReflection,timeShiftVec,add_comm]
      · simp [α,timeReflectionN,timeReflection,timeShiftVec]
    · simp only [joint,Fin.append_right,hρr,orig]
      refine Fin.cases ?_ (fun j => ?_) μ
      · simp [β,timeShiftVec,Matrix.mulVec_add,t]
        ring
      · simp [β,timeShiftVec,Matrix.mulVec_add,b]
  have hJ : kernel Wfn joint = kernel Wfn orig := by rw [hjoint]; exact horig.symm
  rw [hJ] at hcl
  let Aα := ‖kernel Wfn (Fin.append (timeReflectionN d α) α)‖
  let Aβ := ‖kernel Wfn (Fin.append (timeReflectionN d β) β)‖
  have hAn : 0 ≤ Aα := norm_nonneg _
  have hBn : 0 ≤ Aβ := norm_nonneg _
  have hsum : ‖kernel Wfn orig‖ ≤ Aα+Aβ := by
    change ‖kernel Wfn orig‖^2 ≤ Aα*Aβ at hcl
    nlinarith [norm_nonneg (kernel Wfn orig),sq_nonneg Aα,sq_nonneg Aβ]
  have hfx : Aα*‖f.1 x‖ ≤ F x := hF x α hα
  have hgy : Aβ*‖g.1 y‖ ≤ G y := hG y β hβ
  calc
    ‖kernel Wfn orig‖*‖f.1 x‖*‖g.1 y‖ ≤ (Aα+Aβ)*‖f.1 x‖*‖g.1 y‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum (norm_nonneg _)) (norm_nonneg _)
    _ = (Aα*‖f.1 x‖)*‖g.1 y‖ + ‖f.1 x‖*(Aβ*‖g.1 y‖) := by ring
    _ ≤ F x*‖g.1 y‖ + ‖f.1 x‖*G y := add_le_add
      (mul_le_mul_of_nonneg_right hfx (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hgy (norm_nonneg _))
    _ = B (Fin.append x y) := by simp only [B,splitFirst_fin_append,splitLast_fin_append]

end OSReconstruction
