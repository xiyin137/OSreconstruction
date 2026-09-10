/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.deprecated.OSFixedOrderGrowth

















noncomputable section

open scoped BigOperators Classical

namespace OSReconstruction

variable {d n : ℕ}

private theorem abs_matrix_entry_le_one_of_orthogonal
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (i j : Fin (d + 1)) :
    |R i j| ≤ 1 := by
  have hRT : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hdiag : (R * R.transpose) i i = 1 := by
    rw [hRT]
    simp
  have hrow :
      (R * R.transpose) i i =
        ∑ k : Fin (d + 1), R i k ^ 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hs :
      R i j ^ 2 ≤ ∑ k : Fin (d + 1), R i k ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  rw [← hrow, hdiag] at hs
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (R i j)],
    by nlinarith [sq_nonneg (R i j)]⟩

/-- An orthogonal matrix stretches the nested `Pi` sup norm by at most the
spacetime dimension.  The bound is independent of the matrix. -/
theorem norm_matrix_mulVec_npoint_le_of_orthogonal
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (x : NPointDomain d n) :
    ‖fun k => R.mulVec (x k)‖ ≤ (d + 1 : ℝ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(R.mulVec (x k)) i|
        = |∑ j : Fin (d + 1), R i j * x k j| := by
            simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j : Fin (d + 1), |R i j * x k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin (d + 1), |R i j| * |x k j| := by
      simp_rw [abs_mul]
    _ ≤ ∑ _j : Fin (d + 1), 1 * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _hj
      gcongr
      · exact abs_matrix_entry_le_one_of_orthogonal R hR i j
      · calc
          |x k j| = ‖x k j‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x k‖ := norm_le_pi_norm (x k) j
          _ ≤ ‖x‖ := norm_le_pi_norm x k
    _ = (d + 1 : ℝ) * ‖x‖ := by
      simp [Finset.sum_const]

/-- The diagonal inverse-coordinate action of an orthogonal matrix has the
same dimension-only norm bound. -/
theorem norm_osiiEuclideanRotateNPointCLE_apply_le
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (x : NPointDomain d n) :
    ‖osiiEuclideanRotateNPointCLE (n := n) R hR x‖ ≤
      (d + 1 : ℝ) * ‖x‖ := by
  change ‖fun k => R.transpose.mulVec (x k)‖ ≤ _
  apply norm_matrix_mulVec_npoint_le_of_orthogonal R.transpose
  simpa using mul_eq_one_comm.mpr hR

/-- Orthogonal Euclidean rotations preserve the polynomial degree of every
Schwartz seminorm.  The multiplicative loss is uniform over the rotation, so
in particular it is independent of an axis-pair packet slope. -/
theorem seminorm_osiiEuclideanRotateSchwartz_le
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (p l : ℕ)
    (f : SchwartzNPoint d n) :
    SchwartzMap.seminorm ℝ p l
        (osiiEuclideanRotateSchwartz R hR f) ≤
      (d + 1 : ℝ) ^ (p + l) *
        SchwartzMap.seminorm ℝ p l f := by
  let e := osiiEuclideanRotateNPointCLE (n := n) R hR
  let c : ℝ := d + 1
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have he_norm :
      ‖e.toContinuousLinearMap‖ ≤ c := by
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro x
    simpa [e, c] using
      norm_osiiEuclideanRotateNPointCLE_apply_le R hR x
  apply SchwartzMap.seminorm_le_bound ℝ p l _
    (mul_nonneg (pow_nonneg hc _) (apply_nonneg _ _))
  intro x
  have hx :
      ‖x‖ ≤ c * ‖e x‖ := by
    have hrecover :
        (fun k => R.mulVec ((e x) k)) = x := by
      have hRT : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
      funext k
      change R.mulVec (R.transpose.mulVec (x k)) = x k
      rw [Matrix.mulVec_mulVec, hRT]
      simp
    calc
      ‖x‖ = ‖fun k => R.mulVec ((e x) k)‖ := by rw [hrecover]
      _ ≤ c * ‖e x‖ := by
        simpa [c] using
          norm_matrix_mulVec_npoint_le_of_orthogonal R hR (e x)
  have hderiv :
      ‖iteratedFDeriv ℝ l
          (fun y => f (e y)) x‖ ≤
        ‖iteratedFDeriv ℝ l f.toFun (e x)‖ * c ^ l := by
    change
      ‖iteratedFDeriv ℝ l (f.toFun ∘ e.toContinuousLinearMap) x‖ ≤ _
    rw [e.toContinuousLinearMap.iteratedFDeriv_comp_right
      (f := f.toFun) (f.smooth l) x le_rfl]
    calc
      ‖(iteratedFDeriv ℝ l f.toFun (e x)).compContinuousLinearMap
          (fun _ => e.toContinuousLinearMap)‖
          ≤ ‖iteratedFDeriv ℝ l f.toFun (e x)‖ *
              ∏ _i : Fin l, ‖e.toContinuousLinearMap‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ l f.toFun (e x)‖ *
            ∏ _i : Fin l, c := by
        gcongr with i
      _ = ‖iteratedFDeriv ℝ l f.toFun (e x)‖ * c ^ l := by
        simp
  change
    ‖x‖ ^ p *
        ‖iteratedFDeriv ℝ l (fun y => f (e y)) x‖ ≤ _
  calc
    ‖x‖ ^ p * ‖iteratedFDeriv ℝ l (fun y => f (e y)) x‖
        ≤ (c * ‖e x‖) ^ p *
            (‖iteratedFDeriv ℝ l f.toFun (e x)‖ * c ^ l) := by
          gcongr
    _ =
        c ^ (p + l) *
          (‖e x‖ ^ p *
            ‖iteratedFDeriv ℝ l f.toFun (e x)‖) := by
          rw [mul_pow, pow_add]
          ring
    _ ≤ c ^ (p + l) *
          SchwartzMap.seminorm ℝ p l f := by
      gcongr
      exact SchwartzMap.le_seminorm ℝ p l f (e x)

/-- Ordinary E0 selects one Schwartz order for all positive-time Hilbert
sources up to a prescribed state degree. -/
noncomputable def osiiOriginalOSBoundedStateSourceOrder
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ) : ℕ :=
  Classical.choose
    (exists_osiiPositiveTimeSingleVector_boundedArity_norm_sq_finsetSup_bound
      d N OS)

/-- The ordinary-E0 Hilbert coefficient paired with the common bounded-state
Schwartz order. -/
noncomputable def osiiOriginalOSBoundedStateHilbertConstant
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ) : ℝ :=
  Classical.choose
    (Classical.choose_spec
      (exists_osiiPositiveTimeSingleVector_boundedArity_norm_sq_finsetSup_bound
        d N OS))

theorem osiiOriginalOSBoundedStateHilbertConstant_nonneg
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ) :
    0 ≤ osiiOriginalOSBoundedStateHilbertConstant OS N :=
  (Classical.choose_spec
    (Classical.choose_spec
      (exists_osiiPositiveTimeSingleVector_boundedArity_norm_sq_finsetSup_bound
        d N OS))).1

/-- The preselected ordinary-E0 rectangle controls every actual reflected
Hilbert vector up to its chosen maximum state degree. -/
theorem osiiPositiveTimeSingleVector_norm_sq_le_boundedState_finsetSup_ofOS
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (hn : n ≤ N)
    (g : SchwartzNPoint d n)
    (hg : tsupport (g : NPointDomain d n → ℂ) ≤
      OrderedPositiveTimeRegion d n) :
    ‖osiiPositiveTimeSingleVectorCLM OS n ⟨g, hg⟩‖ ^ 2 ≤
      osiiOriginalOSBoundedStateHilbertConstant OS N *
        ((Finset.Iic
          (osiiOriginalOSBoundedStateSourceOrder OS N,
            osiiOriginalOSBoundedStateSourceOrder OS N)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) g) ^ 2 :=
  (Classical.choose_spec
    (Classical.choose_spec
      (exists_osiiPositiveTimeSingleVector_boundedArity_norm_sq_finsetSup_bound
        d N OS))).2 n hn g hg

/-- A uniformly seminorm-bounded transform family retains the original-E0
Hilbert source degree independently of its transform parameter. -/
theorem osiiPositiveTimeSingleVector_norm_sq_transform_translate_le_ofOS
    [NeZero d]
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (hn : n ≤ N)
    (transform : ι → SchwartzNPoint d n → SchwartzNPoint d n)
    (A : ℝ) (hA : 1 ≤ A)
    (htransform :
      ∀ i p l g,
        SchwartzMap.seminorm ℝ p l (transform i g) ≤
          A ^ (p + l) * SchwartzMap.seminorm ℝ p l g)
    (f : SchwartzNPoint d n)
    (i : ι)
    (a : NPointDomain d n)
    (hpositive :
      tsupport
          (transform i (translateSchwartzConfiguration a f) :
            NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) :
    let L := osiiOriginalOSBoundedStateSourceOrder OS N
    let Q := (Finset.Iic (L, L)).sup
      (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f
    ‖osiiPositiveTimeSingleVectorCLM OS n
        ⟨transform i (translateSchwartzConfiguration a f), hpositive⟩‖ ^ 2 ≤
      (osiiOriginalOSBoundedStateHilbertConstant OS N *
        (A ^ (L + L) * (2 : ℝ) ^ L * Q) ^ 2) *
          (1 + ‖a‖) ^ (L + L) := by
  dsimp only
  let L := osiiOriginalOSBoundedStateSourceOrder OS N
  let t : Finset (ℕ × ℕ) := Finset.Iic (L, L)
  let Q : ℝ := t.sup (schwartzSeminormFamily ℝ
    (NPointDomain d n) ℂ) f
  let translated := translateSchwartzConfiguration a f
  let g := transform i translated
  have hA_nonneg : 0 ≤ A := zero_le_one.trans hA
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have htransform_sup :
      t.sup (schwartzSeminormFamily ℝ
          (NPointDomain d n) ℂ) g ≤
        A ^ (L + L) * t.sup (schwartzSeminormFamily ℝ
          (NPointDomain d n) ℂ) translated := by
    apply Seminorm.finset_sup_apply_le
      (mul_nonneg (pow_nonneg hA_nonneg _) (apply_nonneg _ _))
    intro j hj
    have hjL := Finset.mem_Iic.mp hj
    calc
      SchwartzMap.seminorm ℝ j.1 j.2 g ≤
          A ^ (j.1 + j.2) *
            SchwartzMap.seminorm ℝ j.1 j.2 translated :=
        htransform i j.1 j.2 translated
      _ ≤ A ^ (L + L) *
          t.sup (schwartzSeminormFamily ℝ
            (NPointDomain d n) ℂ) translated := by
        apply mul_le_mul
        · exact pow_le_pow_right₀ hA (Nat.add_le_add hjL.1 hjL.2)
        · exact Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily ℝ
              (NPointDomain d n) ℂ) hj
        · exact apply_nonneg _ _
        · exact pow_nonneg hA_nonneg _
  have htranslated :
      t.sup (schwartzSeminormFamily ℝ
          (NPointDomain d n) ℂ) translated ≤
        (2 : ℝ) ^ L * (1 + ‖a‖) ^ L * Q := by
    exact osiiFiniteSchwartzSeminorm_translateSchwartzConfiguration_le
      L a f
  have hsource :
      t.sup (schwartzSeminormFamily ℝ
          (NPointDomain d n) ℂ) g ≤
        (A ^ (L + L) * (2 : ℝ) ^ L * Q) *
          (1 + ‖a‖) ^ L := by
    calc
      _ ≤ A ^ (L + L) *
          t.sup (schwartzSeminormFamily ℝ
            (NPointDomain d n) ℂ) translated := htransform_sup
      _ ≤ A ^ (L + L) *
          ((2 : ℝ) ^ L * (1 + ‖a‖) ^ L * Q) :=
        mul_le_mul_of_nonneg_left htranslated
          (pow_nonneg hA_nonneg _)
      _ = (A ^ (L + L) * (2 : ℝ) ^ L * Q) *
          (1 + ‖a‖) ^ L := by ring
  have hK := osiiOriginalOSBoundedStateHilbertConstant_nonneg OS N
  calc
    ‖osiiPositiveTimeSingleVectorCLM OS n
        ⟨g, hpositive⟩‖ ^ 2 ≤
      osiiOriginalOSBoundedStateHilbertConstant OS N *
        (t.sup (schwartzSeminormFamily ℝ
          (NPointDomain d n) ℂ) g) ^ 2 :=
      osiiPositiveTimeSingleVector_norm_sq_le_boundedState_finsetSup_ofOS
        OS N hn g hpositive
    _ ≤ osiiOriginalOSBoundedStateHilbertConstant OS N *
        ((A ^ (L + L) * (2 : ℝ) ^ L * Q) *
          (1 + ‖a‖) ^ L) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (apply_nonneg _ _) hsource 2) hK
    _ = (osiiOriginalOSBoundedStateHilbertConstant OS N *
        (A ^ (L + L) * (2 : ℝ) ^ L * Q) ^ 2) *
          (1 + ‖a‖) ^ (L + L) := by
      rw [pow_two, pow_add]
      ring

/-- A fixed Schwartz source has one ordinary-E0 Hilbert coefficient for an
entire uniformly bounded transform family, with the preselected state degree. -/
theorem
    exists_uniformDegree_osiiPositiveTimeSingleVector_norm_sq_transform_translate_bound_ofOS
    [NeZero d]
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (hn : n ≤ N)
    (transform : ι → SchwartzNPoint d n → SchwartzNPoint d n)
    (A : ℝ) (hA : 1 ≤ A)
    (htransform :
      ∀ i p l g,
        SchwartzMap.seminorm ℝ p l (transform i g) ≤
          A ^ (p + l) * SchwartzMap.seminorm ℝ p l g)
    (f : SchwartzNPoint d n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i a,
        ∀ hpositive :
          tsupport
              (transform i (translateSchwartzConfiguration a f) :
                NPointDomain d n → ℂ) ⊆
            OrderedPositiveTimeRegion d n,
          ‖osiiPositiveTimeSingleVectorCLM OS n
            ⟨transform i (translateSchwartzConfiguration a f),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS N +
                osiiOriginalOSBoundedStateSourceOrder OS N) := by
  let L := osiiOriginalOSBoundedStateSourceOrder OS N
  let Q : ℝ := (Finset.Iic (L, L)).sup
    (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f
  refine
    ⟨osiiOriginalOSBoundedStateHilbertConstant OS N *
        (A ^ (L + L) * (2 : ℝ) ^ L * Q) ^ 2,
      mul_nonneg
        (osiiOriginalOSBoundedStateHilbertConstant_nonneg OS N)
        (sq_nonneg _), ?_⟩
  intro i a hpositive
  exact osiiPositiveTimeSingleVector_norm_sq_transform_translate_le_ofOS
    OS N hn transform A hA htransform f i a hpositive

/-- A bounded family of Schwartz sources has one ordinary-E0 Hilbert
coefficient simultaneously for every source, transform, and translation. -/
theorem
    exists_uniformDegree_osiiPositiveTimeSingleVector_norm_sq_transform_translate_bound_of_isVonNBounded_ofOS
    [NeZero d]
    {ι υ : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (hn : n ≤ N)
    (transform : ι → SchwartzNPoint d n → SchwartzNPoint d n)
    (A : ℝ) (hA : 1 ≤ A)
    (htransform :
      ∀ i p l g,
        SchwartzMap.seminorm ℝ p l (transform i g) ≤
          A ^ (p + l) * SchwartzMap.seminorm ℝ p l g)
    (f : υ → SchwartzNPoint d n)
    (hf : Bornology.IsVonNBounded ℝ (Set.range f)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u i a,
        ∀ hpositive :
          tsupport
              (transform i (translateSchwartzConfiguration a (f u)) :
                NPointDomain d n → ℂ) ⊆
            OrderedPositiveTimeRegion d n,
          ‖osiiPositiveTimeSingleVectorCLM OS n
            ⟨transform i (translateSchwartzConfiguration a (f u)),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS N +
                osiiOriginalOSBoundedStateSourceOrder OS N) := by
  let L := osiiOriginalOSBoundedStateSourceOrder OS N
  let t : Finset (ℕ × ℕ) := Finset.Iic (L, L)
  have hf_seminorm :=
    (schwartz_withSeminorms ℝ
      (NPointDomain d n) ℂ).isVonNBounded_iff_seminorm_bounded.mp hf
  choose B hB_pos hB_bound using hf_seminorm
  let R : ℝ := ∑ j ∈ t, B j
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg fun j _ => (hB_pos j).le
  have hQ :
      ∀ u, t.sup (schwartzSeminormFamily ℝ
        (NPointDomain d n) ℂ) (f u) ≤ R := by
    intro u
    apply Seminorm.finset_sup_apply_le hR
    intro j hj
    calc
      SchwartzMap.seminorm ℝ j.1 j.2 (f u) ≤ B j :=
        (hB_bound j (f u) (Set.mem_range_self u)).le
      _ ≤ R := Finset.single_le_sum
        (fun q _ => (hB_pos q).le) hj
  let P : ℝ := A ^ (L + L) * (2 : ℝ) ^ L
  have hP : 0 ≤ P := by
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hA) _)
      (by positivity)
  let K := osiiOriginalOSBoundedStateHilbertConstant OS N
  have hK : 0 ≤ K :=
    osiiOriginalOSBoundedStateHilbertConstant_nonneg OS N
  refine ⟨K * (P * R) ^ 2, mul_nonneg hK (sq_nonneg _), ?_⟩
  intro u i a hpositive
  have hpoint :=
    osiiPositiveTimeSingleVector_norm_sq_transform_translate_le_ofOS
      OS N hn transform A hA htransform (f u) i a hpositive
  have hbase : 0 ≤ (1 + ‖a‖) ^ (L + L) := by positivity
  have hsource_nonneg :
      0 ≤ t.sup (schwartzSeminormFamily ℝ
        (NPointDomain d n) ℂ) (f u) := apply_nonneg _ _
  calc
    ‖osiiPositiveTimeSingleVectorCLM OS n
        ⟨transform i (translateSchwartzConfiguration a (f u)),
          hpositive⟩‖ ^ 2 ≤
      (K * (P * t.sup (schwartzSeminormFamily ℝ
        (NPointDomain d n) ℂ) (f u)) ^ 2) *
        (1 + ‖a‖) ^ (L + L) := by
      simpa [K, P, L, t] using hpoint
    _ ≤ (K * (P * R) ^ 2) * (1 + ‖a‖) ^ (L + L) := by
      apply mul_le_mul_of_nonneg_right _ hbase
      apply mul_le_mul_of_nonneg_left _ hK
      exact pow_le_pow_left₀ (mul_nonneg hP hsource_nonneg)
        (mul_le_mul_of_nonneg_left (hQ u) hP) 2

variable {k : ℕ} [NeZero d]

/-- The left packet's rotation followed by time reflection has the same
dimension-only seminorm loss for every slope. -/
theorem seminorm_osiiPacketLeftPositiveCLM_le
    (T : ℝ) (q : osiiAxisPairMultiGapIndex d k)
    (p l : ℕ)
    (f : SchwartzNPoint d (osiiChronologicalGapLeftArity q.1)) :
    SchwartzMap.seminorm ℝ p l
        (osiiPacketLeftPositiveCLM T q f) ≤
      (d + 1 : ℝ) ^ (p + l) *
        SchwartzMap.seminorm ℝ p l f := by
  calc
    SchwartzMap.seminorm ℝ p l
        (osiiPacketLeftPositiveCLM T q f)
        ≤ SchwartzMap.seminorm ℝ p l
            (osiiEuclideanRotateSchwartz
              (osiiAxisPairRotationData T q.2).matrix
              (osiiAxisPairRotationData T q.2).orthogonal f) := by
          simpa [osiiPacketLeftPositiveCLM] using
            SchwartzNPoint.seminorm_timeReflect_le
              (d := d) p l
              (osiiEuclideanRotateSchwartz
                (osiiAxisPairRotationData T q.2).matrix
                (osiiAxisPairRotationData T q.2).orthogonal f)
    _ ≤ (d + 1 : ℝ) ^ (p + l) *
          SchwartzMap.seminorm ℝ p l f :=
      seminorm_osiiEuclideanRotateSchwartz_le
        (osiiAxisPairRotationData T q.2).matrix
        (osiiAxisPairRotationData T q.2).orthogonal p l f

/-- The right packet rotation has a dimension-only seminorm loss for every
slope. -/
theorem seminorm_osiiPacketRightPositiveCLM_le
    (T : ℝ) (q : osiiAxisPairMultiGapIndex d k)
    (p l : ℕ)
    (f : SchwartzNPoint d (osiiChronologicalGapRightArity q.1)) :
    SchwartzMap.seminorm ℝ p l
        (osiiPacketRightPositiveCLM T q f) ≤
      (d + 1 : ℝ) ^ (p + l) *
        SchwartzMap.seminorm ℝ p l f := by
  simpa [osiiPacketRightPositiveCLM] using
    seminorm_osiiEuclideanRotateSchwartz_le
      (osiiAxisPairRotationData T q.2).matrix
      (osiiAxisPairRotationData T q.2).orthogonal p l f

/-- Every left packet rotation has the same original-E0 translation degree,
uniformly over its auxiliary slope and all reflected splits. -/
theorem
    exists_osiiPacketLeftPositiveCLM_norm_sq_translate_bound_uniform_slope_ofOS
    (OS : OsterwalderSchraderAxioms d)
    (q : osiiAxisPairMultiGapIndex d k)
    (f : SchwartzNPoint d (osiiChronologicalGapLeftArity q.1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T a,
        ∀ hpositive :
          tsupport
              (osiiPacketLeftPositiveCLM T q
                  (translateSchwartzConfiguration a f) :
                NPointDomain d
                  (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
            OrderedPositiveTimeRegion d
              (osiiChronologicalGapLeftArity q.1),
          ‖osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapLeftArity q.1)
            ⟨osiiPacketLeftPositiveCLM T q
                (translateSchwartzConfiguration a f),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  have hstate : osiiChronologicalGapLeftArity q.1 ≤ k + 1 := by
    have hq := q.1.isLt
    simp only [osiiChronologicalGapLeftArity]
    omega
  have hdimension : (1 : ℝ) ≤ d + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  apply
    exists_uniformDegree_osiiPositiveTimeSingleVector_norm_sq_transform_translate_bound_ofOS
      OS (k + 1) hstate (fun T => osiiPacketLeftPositiveCLM T q)
      (d + 1 : ℝ) hdimension
  intro T p l g
  exact seminorm_osiiPacketLeftPositiveCLM_le T q p l g

/-- Every right packet rotation has the same original-E0 translation degree
as the left arm, independently of slope and reflected split. -/
theorem
    exists_osiiPacketRightPositiveCLM_norm_sq_translate_bound_uniform_slope_ofOS
    (OS : OsterwalderSchraderAxioms d)
    (q : osiiAxisPairMultiGapIndex d k)
    (f : SchwartzNPoint d (osiiChronologicalGapRightArity q.1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T a,
        ∀ hpositive :
          tsupport
              (osiiPacketRightPositiveCLM T q
                  (translateSchwartzConfiguration a f) :
                NPointDomain d
                  (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
            OrderedPositiveTimeRegion d
              (osiiChronologicalGapRightArity q.1),
          ‖osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapRightArity q.1)
            ⟨osiiPacketRightPositiveCLM T q
                (translateSchwartzConfiguration a f),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  have hstate : osiiChronologicalGapRightArity q.1 ≤ k + 1 := by
    simp only [osiiChronologicalGapRightArity]
    omega
  have hdimension : (1 : ℝ) ≤ d + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  apply
    exists_uniformDegree_osiiPositiveTimeSingleVector_norm_sq_transform_translate_bound_ofOS
      OS (k + 1) hstate (fun T => osiiPacketRightPositiveCLM T q)
      (d + 1 : ℝ) hdimension
  intro T p l g
  exact seminorm_osiiPacketRightPositiveCLM_le T q p l g

/-- A bounded family of left packet references has one original-E0
coefficient and degree for every source index and every packet slope. -/
theorem
    exists_osiiPacketLeftPositiveCLM_norm_sq_translate_bound_uniform_family_slope_ofOS
    {υ : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (q : osiiAxisPairMultiGapIndex d k)
    (f : υ → SchwartzNPoint d (osiiChronologicalGapLeftArity q.1))
    (hf : Bornology.IsVonNBounded ℝ (Set.range f)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u T a,
        ∀ hpositive :
          tsupport
              (osiiPacketLeftPositiveCLM T q
                  (translateSchwartzConfiguration a (f u)) :
                NPointDomain d
                  (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
            OrderedPositiveTimeRegion d
              (osiiChronologicalGapLeftArity q.1),
          ‖osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapLeftArity q.1)
            ⟨osiiPacketLeftPositiveCLM T q
                (translateSchwartzConfiguration a (f u)),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  have hstate : osiiChronologicalGapLeftArity q.1 ≤ k + 1 := by
    have hq := q.1.isLt
    simp only [osiiChronologicalGapLeftArity]
    omega
  have hdimension : (1 : ℝ) ≤ d + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  apply
    exists_uniformDegree_osiiPositiveTimeSingleVector_norm_sq_transform_translate_bound_of_isVonNBounded_ofOS
      OS (k + 1) hstate (fun T => osiiPacketLeftPositiveCLM T q)
      (d + 1 : ℝ) hdimension
  · intro T p l g
    exact seminorm_osiiPacketLeftPositiveCLM_le T q p l g
  · exact hf

/-- A bounded family of right packet references has the identical original-
OS state degree, uniformly over source index and packet slope. -/
theorem
    exists_osiiPacketRightPositiveCLM_norm_sq_translate_bound_uniform_family_slope_ofOS
    {υ : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (q : osiiAxisPairMultiGapIndex d k)
    (f : υ → SchwartzNPoint d (osiiChronologicalGapRightArity q.1))
    (hf : Bornology.IsVonNBounded ℝ (Set.range f)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u T a,
        ∀ hpositive :
          tsupport
              (osiiPacketRightPositiveCLM T q
                  (translateSchwartzConfiguration a (f u)) :
                NPointDomain d
                  (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
            OrderedPositiveTimeRegion d
              (osiiChronologicalGapRightArity q.1),
          ‖osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapRightArity q.1)
            ⟨osiiPacketRightPositiveCLM T q
                (translateSchwartzConfiguration a (f u)),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  have hstate : osiiChronologicalGapRightArity q.1 ≤ k + 1 := by
    simp only [osiiChronologicalGapRightArity]
    omega
  have hdimension : (1 : ℝ) ≤ d + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  apply
    exists_uniformDegree_osiiPositiveTimeSingleVector_norm_sq_transform_translate_bound_of_isVonNBounded_ofOS
      OS (k + 1) hstate (fun T => osiiPacketRightPositiveCLM T q)
      (d + 1 : ℝ) hdimension
  · intro T p l g
    exact seminorm_osiiPacketRightPositiveCLM_le T q p l g
  · exact hf

/-- The actual left reflected packet vector has one source-dependent
coefficient and the fixed original-E0 degree for every auxiliary slope. -/
theorem OSIIChronologicalCompactFactors.exists_packetLeftVector_norm_sq_bound_uniform_slope_ofOS
    {k : ℕ}
    [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (hT : 1 < T)
        (hordered :
          ∀ a : osiiAxisPairIndex d,
            ∀ i j : Fin (k + 1), i < j →
              ∀ y ∈ tsupport
                  ((F.factors i : SchwartzSpacetime d) :
                    SpacetimeDim d → ℂ),
                ∀ z ∈ tsupport
                    ((F.factors j : SchwartzSpacetime d) :
                      SpacetimeDim d → ℂ),
                  ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                    ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
        (x : Fin k → osiiAxisPairIndex d → ℝ),
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 ≤
          C * (1 + ‖F.packetLeftConfiguration T hordered x q‖) ^
            (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
              osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_osiiPacketLeftPositiveCLM_norm_sq_translate_bound_uniform_slope_ofOS
      OS q (F.packetLeftReference q)
  refine ⟨C, hC, ?_⟩
  intro T hT hordered x
  let a := F.packetLeftConfiguration T hordered x q
  have heq :
      F.packetLeftPositiveSource T hordered x q =
        osiiPacketLeftPositiveCLM T q
          (translateSchwartzConfiguration a (F.packetLeftReference q)) := by
    exact F.packetLeftPositiveSource_eq_configurationTranslate
      T hordered x q
  have hs :
      tsupport
          (osiiPacketLeftPositiveCLM T q
              (translateSchwartzConfiguration a (F.packetLeftReference q)) :
            NPointDomain d
              (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
        OrderedPositiveTimeRegion d
          (osiiChronologicalGapLeftArity q.1) := by
    rw [← heq]
    exact F.packetLeftPositiveSource_support T hT hordered x q
  have h := hbound T a hs
  simpa [a, ← heq] using h

/-- The actual right reflected packet vector has the same original-E0
degree and a coefficient valid for every auxiliary slope. -/
theorem OSIIChronologicalCompactFactors.exists_packetRightVector_norm_sq_bound_uniform_slope_ofOS
    {k : ℕ}
    [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (hT : 1 < T)
        (hordered :
          ∀ a : osiiAxisPairIndex d,
            ∀ i j : Fin (k + 1), i < j →
              ∀ y ∈ tsupport
                  ((F.factors i : SchwartzSpacetime d) :
                    SpacetimeDim d → ℂ),
                ∀ z ∈ tsupport
                    ((F.factors j : SchwartzSpacetime d) :
                      SpacetimeDim d → ℂ),
                  ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                    ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
        (x : Fin k → osiiAxisPairIndex d → ℝ),
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 ≤
          C * (1 + ‖F.packetRightConfiguration T hordered x q‖) ^
            (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
              osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_osiiPacketRightPositiveCLM_norm_sq_translate_bound_uniform_slope_ofOS
      OS q (F.packetRightReference q)
  refine ⟨C, hC, ?_⟩
  intro T hT hordered x
  let a := F.packetRightConfiguration T hordered x q
  have heq :
      F.packetRightPositiveSource T hordered x q =
        osiiPacketRightPositiveCLM T q
          (translateSchwartzConfiguration a (F.packetRightReference q)) := by
    exact F.packetRightPositiveSource_eq_configurationTranslate
      T hordered x q
  have hs :
      tsupport
          (osiiPacketRightPositiveCLM T q
              (translateSchwartzConfiguration a (F.packetRightReference q)) :
            NPointDomain d
              (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
        OrderedPositiveTimeRegion d
          (osiiChronologicalGapRightArity q.1) := by
    rw [← heq]
    exact F.packetRightPositiveSource_support T hT hordered x q
  have h := hbound T a hs
  simpa [a, ← heq] using h

/-- At fixed gap arity, ordinary E0 supplies one packet cosh rate independent
of the auxiliary slope, reflected split, and compact source carrier. -/
noncomputable def osiiOriginalOSUniformPacketCoshRate
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ) : ℝ :=
  let L := osiiOriginalOSBoundedStateSourceOrder OS (k + 1)
  4 * (((L + L) + (L + L) : ℕ) : ℝ)

theorem osiiOriginalOSUniformPacketCoshRate_nonneg
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ) :
    0 ≤ osiiOriginalOSUniformPacketCoshRate OS k := by
  exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- The genuine original-OS compensated packet has one damping rate for
every auxiliary slope and reflected coordinate at fixed gap arity. -/
theorem
    OSIIChronologicalCompactFactors.exists_compensatedMovingPacket_branchOfOS_cosh_bound_uniform_slope_rate
    {k : ℕ}
    [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin k → osiiAxisPairIndex d → ℝ)
        (z : ℂ), 0 < z.re →
        ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
            T hT
            (osiiAxisPairPositiveCoefficients (x q.1))
            (fun b =>
              le_of_lt
                (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
            q.2
            (F.packetLeftSource T hordered x q)
            (F.packetLeftSource_support T hT hordered x q)
            (F.packetRightSource T hordered x q)
            (F.packetRightSource_support T hT hordered x q)).branchOfOS
              OS z‖ ≤
          C * Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
  let L := osiiOriginalOSBoundedStateSourceOrder OS (k + 1)
  let N := L + L
  obtain ⟨CL, hCL, hleft⟩ :=
    F.exists_packetLeftVector_norm_sq_bound_uniform_slope_ofOS OS q
  obtain ⟨CR, hCR, hright⟩ :=
    F.exists_packetRightVector_norm_sq_bound_uniform_slope_ofOS OS q
  let A := F.packetConfigurationCoshConstant T hordered q
  let C : ℝ := 1 + CL * A ^ N + CR * A ^ N
  have hA : 0 < A := F.packetConfigurationCoshConstant_pos T hordered q
  have hC : 0 < C := by
    dsimp [C]
    have hAN : 0 ≤ A ^ N := pow_nonneg hA.le _
    nlinarith
  refine ⟨C, hC, fun x z hz => ?_⟩
  let G := SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)
  let E := Real.exp (4 * G)
  have hE : 1 ≤ E := by
    exact Real.one_le_exp
      (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le))
  have hleftConfig :
      1 + ‖F.packetLeftConfiguration T hordered x q‖ ≤ A * E := by
    exact F.one_add_norm_packetLeftConfiguration_le_cosh T hordered x q
  have hrightConfig :
      1 + ‖F.packetRightConfiguration T hordered x q‖ ≤ A * E := by
    exact F.one_add_norm_packetRightConfiguration_le_cosh T hordered x q
  have hleftPow :
      (1 + ‖F.packetLeftConfiguration T hordered x q‖) ^ N ≤
        A ^ N * E ^ (N + N) := by
    calc
      _ ≤ (A * E) ^ N :=
        pow_le_pow_left₀ (by positivity) hleftConfig N
      _ = A ^ N * E ^ N := by rw [mul_pow]
      _ ≤ A ^ N * E ^ (N + N) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hE (Nat.le_add_right N N))
          (pow_nonneg hA.le _)
  have hrightPow :
      (1 + ‖F.packetRightConfiguration T hordered x q‖) ^ N ≤
        A ^ N * E ^ (N + N) := by
    calc
      _ ≤ (A * E) ^ N :=
        pow_le_pow_left₀ (by positivity) hrightConfig N
      _ = A ^ N * E ^ N := by rw [mul_pow]
      _ ≤ A ^ N * E ^ (N + N) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hE (Nat.le_add_right N N))
          (pow_nonneg hA.le _)
  have hleftVector :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 ≤
        CL * A ^ N * E ^ (N + N) := by
    calc
      _ ≤ CL * (1 + ‖F.packetLeftConfiguration T hordered x q‖) ^ N :=
        hleft T hT hordered x
      _ ≤ CL * (A ^ N * E ^ (N + N)) :=
        mul_le_mul_of_nonneg_left hleftPow hCL
      _ = CL * A ^ N * E ^ (N + N) := by ring
  have hrightVector :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 ≤
        CR * A ^ N * E ^ (N + N) := by
    calc
      _ ≤ CR * (1 + ‖F.packetRightConfiguration T hordered x q‖) ^ N :=
        hright T hT hordered x
      _ ≤ CR * (A ^ N * E ^ (N + N)) :=
        mul_le_mul_of_nonneg_left hrightPow hCR
      _ = CR * A ^ N * E ^ (N + N) := by ring
  have hEpow :
      E ^ (N + N) =
        Real.exp (osiiOriginalOSUniformPacketCoshRate OS k * G) := by
    rw [show E = Real.exp (4 * G) by rfl, ← Real.exp_nat_mul]
    congr 1
    dsimp [osiiOriginalOSUniformPacketCoshRate, N, L]
    push_cast
    ring
  calc
    _ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 +
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 :=
      F.norm_compensatedMovingPacket_branchOfOS_le
        OS T hT hordered x q z hz
    _ ≤ (CL * A ^ N + CR * A ^ N) * E ^ (N + N) := by
      nlinarith [hleftVector, hrightVector]
    _ ≤ C * E ^ (N + N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [C]
      linarith
    _ = C * Real.exp
          (osiiOriginalOSUniformPacketCoshRate OS k * G) := by
      rw [hEpow]

/-- Every actual original-OS coordinate chart has the same fixed-arity
growth rate, independent of its selected gap, axis, and packet slope. -/
theorem
    OSIIChronologicalCompactFactors.exists_multiGapFlatCrossOfOS_chart_cosh_bound_uniform_slope_rate
    {k : ℕ} [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
        |w.im| < Real.pi / 2 →
        ‖(F.multiGapFlatCrossOfOS OS T hT hordered).branch x q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
          C * Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiAxisPairMultiGapChartRealPart x q w))) := by
  obtain ⟨C, hC, hbound⟩ :=
    F.exists_compensatedMovingPacket_branchOfOS_cosh_bound_uniform_slope_rate
      OS T hT hordered q
  refine ⟨C, hC, fun x w hw => ?_⟩
  let P := F.multiGapFlatCrossOfOS OS T hT hordered
  let y := osiiAxisPairMultiGapChartRealPart x q w
  have hxy :
      ∀ p : osiiAxisPairMultiGapIndex d k, p ≠ q →
        x p.1 p.2 = y p.1 p.2 := by
    intro p hp
    exact (osiiAxisPairMultiGapChartRealPart_eq_of_ne x q p w hp).symm
  have hbranch : P.branch x q = P.branch y q :=
    P.branch_congr_of_eq_off_selected q hxy
  have hexpRe : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw))
  have hphysical := hbound y (Complex.exp w) hexpRe
  rw [congrFun hbranch
    (osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w)]
  simpa [P, y,
    OSIIChronologicalCompactFactors.multiGapFlatCrossOfOS,
    OSIIAxisPairMultiGapFlatCrossData.ofCompensatedFrozenDependentOfOS,
    osiiAxisPairMultiGapUpdate] using hphysical

/-- The entire original-OS flat cross has one coefficient and a cosh rate
fixed before its packet slope, compact source, or active coordinate. -/
theorem
    OSIIChronologicalCompactFactors.exists_multiGapFlatCrossOfOS_cosh_bounds_uniform_slope_rate
    {k : ℕ} [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        ‖(F.multiGapFlatCrossOfOS OS T hT hordered).realEdge x‖ ≤
          C * Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x))) ∧
      (∀ (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          ‖(F.multiGapFlatCrossOfOS OS T hT hordered).branch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
            C * Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiAxisPairMultiGapChartRealPart x q w)))) := by
  let P := F.multiGapFlatCrossOfOS OS T hT hordered
  choose C hC hchart using fun q : osiiAxisPairMultiGapIndex d k =>
    F.exists_multiGapFlatCrossOfOS_chart_cosh_bound_uniform_slope_rate
      OS T hT hordered q
  let Cstar : ℝ := 1 + ∑ q : osiiAxisPairMultiGapIndex d k, C q
  have hCstar : 0 < Cstar := by
    have hsum : 0 ≤ ∑ q : osiiAxisPairMultiGapIndex d k, C q :=
      Finset.sum_nonneg fun q _ => (hC q).le
    dsimp [Cstar]
    linarith
  have hC_le : ∀ q : osiiAxisPairMultiGapIndex d k, C q ≤ Cstar := by
    intro q
    have hsingle := Finset.single_le_sum
      (fun p _ => (hC p).le) (Finset.mem_univ q)
    dsimp [Cstar]
    linarith
  have hchartStar :
      ∀ (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          ‖P.branch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
            Cstar * Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiAxisPairMultiGapChartRealPart x q w))) := by
    intro q x w hw
    exact (hchart q x w hw).trans
      (mul_le_mul_of_nonneg_right (hC_le q) (Real.exp_pos _).le)
  let q0 : osiiAxisPairMultiGapIndex d k :=
    ((0 : Fin k), ((0 : Fin d), false))
  have hreal :
      ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        ‖P.realEdge x‖ ≤
          Cstar * Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
    intro x
    have hstrip : |((x q0.1 q0.2 : ℂ)).im| < Real.pi / 2 := by
      simp
      positivity
    have hbound := hchartStar q0 x (x q0.1 q0.2 : ℂ) hstrip
    rw [osiiAxisPairMultiGapUpdate_realEmbed_selected x q0,
      P.branch_real_edge x q0,
      osiiAxisPairMultiGapChartRealPart_selected_real x q0] at hbound
    exact hbound
  exact ⟨Cstar, hCstar, hreal, hchartStar⟩

/-- Package the genuine flat cross with the original-E0 rate that is uniform
over the auxiliary packet slope and every source tuple. -/
noncomputable def
    OSIIChronologicalCompactFactors.multiGapFlatCrossOfOS_coshGrowthDataAtUniformSlopeRate
    {k : ℕ} [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    OSIIAxisPairMultiGapFlatCrossCoshGrowthData
      (F.multiGapFlatCrossOfOS OS T hT hordered) := by
  let hexists := F.exists_multiGapFlatCrossOfOS_cosh_bounds_uniform_slope_rate
    OS T hT hordered
  let C : ℝ := Classical.choose hexists
  have hC : 0 < C := (Classical.choose_spec hexists).1
  let P := F.multiGapFlatCrossOfOS OS T hT hordered
  have hreal := (Classical.choose_spec hexists).2.1
  have hchart := (Classical.choose_spec hexists).2.2
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := P.toFlattenedFlatCrossData
  change OSIIAxisPairFlatCrossCoshGrowthData X
  refine {
    rate := osiiOriginalOSUniformPacketCoshRate OS k
    rate_nonneg := osiiOriginalOSUniformPacketCoshRate_nonneg OS k
    realEdgeConstant := C
    realEdgeConstant_nonneg := hC.le
    realEdge_bound := ?_
    chartConstant := C
    chartConstant_pos := hC
    chart_bound := ?_ }
  · intro x
    simpa [X, P, C,
      OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData] using
      hreal (osiiAxisPairMultiGapUnflatten x)
  · intro q x w hw
    rw [X.family.flatTubeBranch_coordinate_line_eq_branch x q hw]
    simp only [X, P,
      OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData]
    let uq := osiiAxisPairMultiGapUnflattenIndex q
    rw [show q = osiiAxisPairMultiGapFlattenIndex uq by simp [uq]]
    have hbase :
        osiiAxisPairLogRealEmbed x =
          osiiAxisPairMultiGapFlatten
            (osiiAxisPairSimultaneousLogRealEmbed
              (osiiAxisPairMultiGapUnflatten x)) := by
      rw [osiiAxisPairMultiGapFlatten_realEmbed,
        osiiAxisPairMultiGapFlatten_unflatten]
    rw [hbase, osiiAxisPairMultiGapUnflatten_update_flatten]
    have hbound := hchart uq (osiiAxisPairMultiGapUnflatten x) w hw
    rw [osiiAxisPairMultiGapFlatten_chartRealPart_unflatten
      x uq w] at hbound
    have hflatbase :
        osiiAxisPairMultiGapFlatten
            (osiiAxisPairSimultaneousLogRealEmbed
              (osiiAxisPairMultiGapUnflatten x)) =
          fun c => (x c : ℂ) := by
      rw [osiiAxisPairMultiGapFlatten_realEmbed,
        osiiAxisPairMultiGapFlatten_unflatten]
      rfl
    rw [hflatbase]
    simpa [osiiAxisPairLogRealEmbed, C] using hbound

/-- Transfer a growth bound along equality of the real edge and the genuine
coordinate-strip branches. Values outside the strips are irrelevant. -/
def OSIIAxisPairMultiGapFlatCrossCoshGrowthData.congr
    {k : ℕ} [NeZero d] [NeZero k]
    {P Q : OSIIAxisPairMultiGapFlatCrossData d k}
    (G : OSIIAxisPairMultiGapFlatCrossCoshGrowthData P)
    (hreal : ∀ x, Q.realEdge x = P.realEdge x)
    (hbranch : ∀ x q, Set.EqOn (Q.branch x q) (P.branch x q)
      (osiiAxisPairMultiGapCoordinateLogStrip q)) :
    OSIIAxisPairMultiGapFlatCrossCoshGrowthData Q := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  refine {
    rate := G.rate
    rate_nonneg := G.rate_nonneg
    realEdgeConstant := G.realEdgeConstant
    realEdgeConstant_nonneg := G.realEdgeConstant_nonneg
    realEdge_bound := ?_
    chartConstant := G.chartConstant
    chartConstant_pos := G.chartConstant_pos
    chart_bound := ?_ }
  · intro x
    change ‖Q.realEdge (osiiAxisPairMultiGapUnflatten x)‖ ≤ _
    rw [hreal]
    exact G.realEdge_bound x
  · intro q x w hw
    have hp := G.chart_bound q x w hw
    rw [P.toFlattenedFlatCrossData.family.flatTubeBranch_coordinate_line_eq_branch
      x q hw] at hp
    rw [Q.toFlattenedFlatCrossData.family.flatTubeBranch_coordinate_line_eq_branch
      x q hw]
    change ‖Q.branch (osiiAxisPairMultiGapUnflatten x)
      (osiiAxisPairMultiGapUnflattenIndex q)
      (osiiAxisPairMultiGapUnflatten
        (Function.update (osiiAxisPairLogRealEmbed x) q w))‖ ≤ _
    rw [hbranch]
    · exact hp
    · change |((Function.update (osiiAxisPairLogRealEmbed x) q w)
        (osiiAxisPairMultiGapFlattenIndex (d := d) (k := k)
          (osiiAxisPairMultiGapUnflattenIndex (d := d) (k := k) q))).im| <
        Real.pi / 2
      rw [osiiAxisPairMultiGapFlattenIndex_unflattenIndex (d := d) (k := k) q,
        Function.update_self]
      exact hw

/-- The growth-indexed compatibility packet has the same genuine branches
as the original-OS packet. Its source-independent, slope-independent bound
therefore needs only ordinary E0. -/
noncomputable def
    OSIIChronologicalCompactFactors.multiGapPacketFamily_coshGrowthDataAtOriginalOSUniformSlopeRate
    {k : ℕ} [NeZero d] [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    OSIIAxisPairMultiGapFlatCrossCoshGrowthData
      ((F.multiGapPacketFamily OS lgc T hT hordered).toFlatCrossData
        (F.continuousOn_multiGapPacketFamily_branch
          OS lgc T hT hordered)) :=
  (F.multiGapFlatCrossOfOS_coshGrowthDataAtUniformSlopeRate
    OS T hT hordered).congr (fun _ => rfl) (by
      intro x q z hz
      exact OSIIAxisPairRotatedSourcePacket.branch_eq_branchOfOS _ OS lgc
        (Complex.exp (z q.1 q.2))
        (osiiAxisPair_exp_apply_mem_rightHalfPlane hz))

end OSReconstruction
