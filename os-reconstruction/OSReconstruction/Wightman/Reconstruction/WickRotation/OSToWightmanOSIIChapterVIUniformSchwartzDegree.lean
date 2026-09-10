/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPositiveSourceSeminorm











noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction

/-- Precomposition by a continuous linear equivalence preserves the two
Schwartz seminorm indices. Only the numerical coefficient changes. -/
theorem schwartzSeminorm_compContinuousLinearEquiv_le
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (g : D ≃L[Real] E)
    (f : SchwartzMap E Complex)
    (p l : Nat) :
    SchwartzMap.seminorm Real p l
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f) <=
      ‖g.symm.toContinuousLinearMap‖ ^ p *
        ‖g.toContinuousLinearMap‖ ^ l *
          SchwartzMap.seminorm Real p l f := by
  let C : Real :=
    ‖g.symm.toContinuousLinearMap‖ ^ p *
      ‖g.toContinuousLinearMap‖ ^ l *
        SchwartzMap.seminorm Real p l f
  refine SchwartzMap.seminorm_le_bound Real p l _ (by positivity) ?_
  intro x
  have hcomp :
      ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f :
          SchwartzMap D Complex) : D -> Complex) =
        fun y => f (g y) := by
    rfl
  have hiter :
      iteratedFDeriv Real l
          ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f :
            SchwartzMap D Complex) : D -> Complex) x =
        ContinuousMultilinearMap.compContinuousLinearMap
          (iteratedFDeriv Real l (f : E -> Complex) (g x))
          (fun _ => g.toContinuousLinearMap) := by
    rw [hcomp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_right
      g.toContinuousLinearMap f.smooth' x (by exact_mod_cast le_top)
  have hx :
      ‖x‖ <= ‖g.symm.toContinuousLinearMap‖ * ‖g x‖ := by
    calc
      ‖x‖ = ‖g.symm (g x)‖ := by rw [g.symm_apply_apply]
      _ <= ‖g.symm.toContinuousLinearMap‖ * ‖g x‖ :=
        g.symm.toContinuousLinearMap.le_opNorm (g x)
  have hderiv :
      ‖iteratedFDeriv Real l
          ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f :
            SchwartzMap D Complex) : D -> Complex) x‖ <=
        ‖iteratedFDeriv Real l (f : E -> Complex) (g x)‖ *
          ‖g.toContinuousLinearMap‖ ^ l := by
    rw [hiter]
    calc
      ‖ContinuousMultilinearMap.compContinuousLinearMap
          (iteratedFDeriv Real l (f : E -> Complex) (g x))
          (fun _ => g.toContinuousLinearMap)‖ <=
        ‖iteratedFDeriv Real l (f : E -> Complex) (g x)‖ *
          ∏ _ : Fin l, ‖g.toContinuousLinearMap‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv Real l (f : E -> Complex) (g x)‖ *
          ‖g.toContinuousLinearMap‖ ^ l := by
        simp
  calc
    ‖x‖ ^ p *
        ‖iteratedFDeriv Real l
          ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f :
            SchwartzMap D Complex) : D -> Complex) x‖ <=
      (‖g.symm.toContinuousLinearMap‖ * ‖g x‖) ^ p *
        (‖iteratedFDeriv Real l (f : E -> Complex) (g x)‖ *
          ‖g.toContinuousLinearMap‖ ^ l) := by
      gcongr
    _ =
      (‖g.symm.toContinuousLinearMap‖ ^ p *
        ‖g.toContinuousLinearMap‖ ^ l) *
        (‖g x‖ ^ p *
          ‖iteratedFDeriv Real l (f : E -> Complex) (g x)‖) := by
      rw [mul_pow]
      ring
    _ <=
      (‖g.symm.toContinuousLinearMap‖ ^ p *
        ‖g.toContinuousLinearMap‖ ^ l) *
          SchwartzMap.seminorm Real p l f := by
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.le_seminorm Real p l f (g x)) (by positivity)
    _ = C := by rfl

/-- One explicit coefficient controlling an index-preserving continuous
linear equivalence on a finite family of Schwartz seminorms. -/
def schwartzCompEquivFinsetFactor
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (g : D ≃L[Real] E)
    (s : Finset (Nat × Nat)) : Real :=
  ∑ j ∈ s,
    ‖g.symm.toContinuousLinearMap‖ ^ j.1 *
      ‖g.toContinuousLinearMap‖ ^ j.2

theorem schwartzCompEquivFinsetFactor_nonneg
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (g : D ≃L[Real] E)
    (s : Finset (Nat × Nat)) :
    0 <= schwartzCompEquivFinsetFactor g s := by
  unfold schwartzCompEquivFinsetFactor
  positivity

/-- If both operator norms of a coordinate equivalence have explicit
majorants, the finite-family Schwartz factor is bounded termwise by those
majorants. -/
theorem schwartzCompEquivFinsetFactor_le_of_norm_le
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (g : D ≃L[Real] E)
    (s : Finset (Nat × Nat))
    (A B : Real)
    (hA0 : 0 <= A)
    (hA : ‖g.symm.toContinuousLinearMap‖ <= A)
    (hB : ‖g.toContinuousLinearMap‖ <= B) :
    schwartzCompEquivFinsetFactor g s <=
      ∑ j ∈ s, A ^ j.1 * B ^ j.2 := by
  unfold schwartzCompEquivFinsetFactor
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) hA _)
    (pow_le_pow_left₀ (norm_nonneg _) hB _)
    (pow_nonneg (norm_nonneg _) _)
    (pow_nonneg hA0 _)

/-- Finite-seminorm form of the index-preserving transport. The source and
target seminorm families are literally the same finite set. -/
theorem finsetSup_compContinuousLinearEquiv_le
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (g : D ≃L[Real] E)
    (s : Finset (Nat × Nat))
    (f : SchwartzMap E Complex) :
    s.sup (schwartzSeminormFamily Real D Complex)
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f) <=
      schwartzCompEquivFinsetFactor g s *
        s.sup (schwartzSeminormFamily Real E Complex) f := by
  let C := schwartzCompEquivFinsetFactor g s
  let Q := s.sup (schwartzSeminormFamily Real E Complex) f
  have hC : 0 <= C := schwartzCompEquivFinsetFactor_nonneg g s
  have hQ : 0 <= Q := apply_nonneg _ _
  apply Seminorm.finset_sup_apply_le (mul_nonneg hC hQ)
  intro j hj
  let c : Real :=
    ‖g.symm.toContinuousLinearMap‖ ^ j.1 *
      ‖g.toContinuousLinearMap‖ ^ j.2
  have hc : 0 <= c := by positivity
  have hcC : c <= C := by
    dsimp [c, C, schwartzCompEquivFinsetFactor]
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (pow_nonneg (norm_nonneg _) _)
        (pow_nonneg (norm_nonneg _) _)) hj
  have hjQ :
      SchwartzMap.seminorm Real j.1 j.2 f <= Q := by
    exact Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real E Complex) hj
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex g f) <=
      c * SchwartzMap.seminorm Real j.1 j.2 f := by
        simpa only [c] using
          schwartzSeminorm_compContinuousLinearEquiv_le g f j.1 j.2
    _ <= C * Q := mul_le_mul hcC hjQ (apply_nonneg _ _) hC



/-- Largest polynomial-weight index in a finite Schwartz seminorm family. -/
def schwartzSeminormWeightOrder (s : Finset (Nat × Nat)) : Nat :=
  s.sup fun j => j.1

/-- Largest derivative index in a finite Schwartz seminorm family. -/
def schwartzSeminormDerivativeOrder (s : Finset (Nat × Nat)) : Nat :=
  s.sup fun j => j.2

/-- The complete finite Schwartz rectangle has exactly its prescribed
polynomial-weight order. -/
theorem schwartzSeminormWeightOrder_Iic (p l : Nat) :
    schwartzSeminormWeightOrder (Finset.Iic (p, l)) = p := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (Finset.mem_Iic.mp hj).1
  · apply Finset.le_sup
      (s := Finset.Iic (p, l))
      (f := fun j : Nat × Nat => j.1)
      (b := (p, l))
    simp

/-- The complete finite Schwartz rectangle has exactly its prescribed
derivative order. -/
theorem schwartzSeminormDerivativeOrder_Iic (p l : Nat) :
    schwartzSeminormDerivativeOrder (Finset.Iic (p, l)) = l := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (Finset.mem_Iic.mp hj).2
  · apply Finset.le_sup
      (s := Finset.Iic (p, l))
      (f := fun j : Nat × Nat => j.2)
      (b := (p, l))
    simp

/-- The rectangular seminorm family containing all Leibniz indices generated
by a requested finite family. -/
def schwartzSeminormRectangle
    (s : Finset (Nat × Nat)) : Finset (Nat × Nat) :=
  (Finset.range (schwartzSeminormWeightOrder s + 1)).product
    (Finset.range (schwartzSeminormDerivativeOrder s + 1))

/-- A complete finite Schwartz rectangle is already closed under every
Leibniz index needed by the radial tensor-product estimate. -/
theorem schwartzSeminormRectangle_Iic (p l : Nat) :
    schwartzSeminormRectangle (Finset.Iic (p, l)) =
      Finset.Iic (p, l) := by
  ext j
  rcases j with ⟨a, b⟩
  simp [schwartzSeminormRectangle,
    schwartzSeminormWeightOrder_Iic,
    schwartzSeminormDerivativeOrder_Iic, Nat.lt_succ_iff]

/-- Explicit coefficient for the finite-family Schwartz tensor-product
estimate. -/
def schwartzTensorProductFinsetFactor
    (s : Finset (Nat × Nat)) : Real :=
  ∑ j ∈ s,
    2 ^ j.1 *
      ∑ i ∈ Finset.range (j.2 + 1),
        (j.2.choose i : Real) * (1 + 1)

theorem schwartzTensorProductFinsetFactor_nonneg
    (s : Finset (Nat × Nat)) :
    0 <= schwartzTensorProductFinsetFactor s := by
  unfold schwartzTensorProductFinsetFactor
  positivity

set_option maxHeartbeats 2000000 in
/-- A finite seminorm family of a Schwartz tensor product is controlled by
the same explicit index rectangle on both factors. -/
theorem finsetSup_tensorProduct_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (n m : Nat)
    (s : Finset (Nat × Nat))
    (f : SchwartzMap (Fin n -> E) Complex)
    (g : SchwartzMap (Fin m -> E) Complex) :
    s.sup
        (schwartzSeminormFamily Real
          (Fin (n + m) -> E) Complex)
        (f.tensorProduct g) <=
      schwartzTensorProductFinsetFactor s *
        (schwartzSeminormRectangle s).sup
          (schwartzSeminormFamily Real
            (Fin n -> E) Complex) f *
        (schwartzSeminormRectangle s).sup
          (schwartzSeminormFamily Real
            (Fin m -> E) Complex) g := by
  let pMax := schwartzSeminormWeightOrder s
  let lMax := schwartzSeminormDerivativeOrder s
  let rect := schwartzSeminormRectangle s
  let C := schwartzTensorProductFinsetFactor s
  let H := rect.sup
    (schwartzSeminormFamily Real (Fin n -> E) Complex) f
  let T := rect.sup
    (schwartzSeminormFamily Real (Fin m -> E) Complex) g
  have hC : 0 <= C := schwartzTensorProductFinsetFactor_nonneg s
  have hH : 0 <= H := apply_nonneg _ _
  have hT : 0 <= T := apply_nonneg _ _
  apply Seminorm.finset_sup_apply_le
    (mul_nonneg (mul_nonneg hC hH) hT)
  intro j hj
  have hjp : j.1 <= pMax :=
    Finset.le_sup (f := fun z => z.1) hj
  have hjl : j.2 <= lMax :=
    Finset.le_sup (f := fun z => z.2) hj
  have hsum :
      ∑ i ∈ Finset.range (j.2 + 1), (j.2.choose i : Real) *
          (SchwartzMap.seminorm Real j.1 i f *
              SchwartzMap.seminorm Real 0 (j.2 - i) g +
            SchwartzMap.seminorm Real 0 i f *
              SchwartzMap.seminorm Real j.1 (j.2 - i) g) <=
        ∑ i ∈ Finset.range (j.2 + 1),
          (j.2.choose i : Real) * (H * T + H * T) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_le : i <= j.2 := by
      simpa [Finset.mem_range] using hi
    have hi_lMax : i <= lMax := hi_le.trans hjl
    have hsub_lMax : j.2 - i <= lMax :=
      (Nat.sub_le j.2 i).trans hjl
    have hfP : (j.1, i) ∈ rect := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjp),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hi_lMax)⟩
    have hf0 : (0, i) ∈ rect := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.zero_lt_succ pMax),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hi_lMax)⟩
    have hg0 : (0, j.2 - i) ∈ rect := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.zero_lt_succ pMax),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hsub_lMax)⟩
    have hgP : (j.1, j.2 - i) ∈ rect := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjp),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hsub_lMax)⟩
    have hfP_le :
        SchwartzMap.seminorm Real j.1 i f <= H := by
      simpa only [H] using
        (Seminorm.le_finset_sup_apply
          (p := schwartzSeminormFamily Real
            (Fin n -> E) Complex) hfP)
    have hf0_le :
        SchwartzMap.seminorm Real 0 i f <= H := by
      simpa only [H] using
        (Seminorm.le_finset_sup_apply
          (p := schwartzSeminormFamily Real
            (Fin n -> E) Complex) hf0)
    have hg0_le :
        SchwartzMap.seminorm Real 0 (j.2 - i) g <= T := by
      simpa only [T] using
        (Seminorm.le_finset_sup_apply
          (p := schwartzSeminormFamily Real
            (Fin m -> E) Complex) hg0)
    have hgP_le :
        SchwartzMap.seminorm Real j.1 (j.2 - i) g <= T := by
      simpa only [T] using
        (Seminorm.le_finset_sup_apply
          (p := schwartzSeminormFamily Real
            (Fin m -> E) Complex) hgP)
    have hchoose : (0 : Real) <= (j.2.choose i : Real) := by
      positivity
    apply mul_le_mul_of_nonneg_left _ hchoose
    exact add_le_add
      (mul_le_mul hfP_le hg0_le (apply_nonneg _ _) hH)
      (mul_le_mul hf0_le hgP_le (apply_nonneg _ _) hH)
  have hsum_eq :
      (∑ i ∈ Finset.range (j.2 + 1),
          (j.2.choose i : Real) * (H * T + H * T)) =
        (∑ i ∈ Finset.range (j.2 + 1),
          (j.2.choose i : Real) * (1 + 1)) * H * T := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hjC :
      2 ^ j.1 *
          (∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (1 + 1)) <= C := by
    dsimp [C, schwartzTensorProductFinsetFactor]
    exact Finset.single_le_sum
      (f := fun q : Nat × Nat =>
        (2 : Real) ^ q.1 *
          ∑ i ∈ Finset.range (q.2 + 1),
            (q.2.choose i : Real) * (1 + 1))
      (fun q _ => by positivity) hj
  calc
    SchwartzMap.seminorm Real j.1 j.2 (f.tensorProduct g) <=
        2 ^ j.1 *
          ∑ i ∈ Finset.range (j.2 + 1), (j.2.choose i : Real) *
            (SchwartzMap.seminorm Real j.1 i f *
                SchwartzMap.seminorm Real 0 (j.2 - i) g +
              SchwartzMap.seminorm Real 0 i f *
                SchwartzMap.seminorm Real j.1 (j.2 - i) g) := by
      simpa using
        SchwartzMap.tensorProduct_seminorm_le j.1 j.2 f g
    _ <= 2 ^ j.1 *
        ∑ i ∈ Finset.range (j.2 + 1),
          (j.2.choose i : Real) * (H * T + H * T) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ =
        (2 ^ j.1 *
          (∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (1 + 1))) * H * T := by
      rw [hsum_eq]
      ring
    _ <= C * H * T := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hjC hH) hT



/-- Reindexing a finite product by an equivalence preserves its sup norm. -/
theorem norm_piCongrLeft_apply_eq
    {ι ι' E : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup E] [NormedSpace Real E]
    (e : ι' ≃ ι)
    (x : ι' -> E) :
    ‖ContinuousLinearEquiv.piCongrLeft Real
        (fun _ : ι => E) e x‖ = ‖x‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have happly :
        ContinuousLinearEquiv.piCongrLeft Real
            (fun _ : ι => E) e x i = x (e.symm i) := by
      change (Equiv.piCongrLeft (fun _ : ι => E) e x) i =
        x (e.symm i)
      simp [Equiv.piCongrLeft_apply]
    rw [happly]
    exact norm_le_pi_norm x _
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have h := norm_le_pi_norm
      (ContinuousLinearEquiv.piCongrLeft Real
        (fun _ : ι => E) e x) (e i)
    simpa [ContinuousLinearEquiv.piCongrLeft] using h

/-- The inverse finite-product reindexing also preserves its sup norm. -/
theorem norm_piCongrLeft_symm_apply_eq
    {ι ι' E : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup E] [NormedSpace Real E]
    (e : ι' ≃ ι)
    (x : ι -> E) :
    ‖(ContinuousLinearEquiv.piCongrLeft Real
        (fun _ : ι => E) e).symm x‖ = ‖x‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have happly :
        (ContinuousLinearEquiv.piCongrLeft Real
            (fun _ : ι => E) e).symm x i = x (e i) := by
      change (Equiv.piCongrLeft (fun _ : ι => E) e).symm x i =
        x (e i)
      simp [Equiv.piCongrLeft_symm_apply]
    rw [happly]
    exact norm_le_pi_norm x _
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have happly :
        (ContinuousLinearEquiv.piCongrLeft Real
            (fun _ : ι => E) e).symm x (e.symm i) = x i := by
      change (Equiv.piCongrLeft (fun _ : ι => E) e).symm x
        (e.symm i) = x i
      simp [Equiv.piCongrLeft_symm_apply]
    rw [← happly]
    exact norm_le_pi_norm _ _

/-- A finite-product reindexing has operator norm at most one. -/
theorem norm_piCongrLeft_toContinuousLinearMap_le_one
    {ι ι' E : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup E] [NormedSpace Real E]
    (e : ι' ≃ ι) :
    ‖(ContinuousLinearEquiv.piCongrLeft Real
        (fun _ : ι => E) e).toContinuousLinearMap‖ <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using (norm_piCongrLeft_apply_eq e x).le

/-- The inverse finite-product reindexing has operator norm at most one. -/
theorem norm_piCongrLeft_symm_toContinuousLinearMap_le_one
    {ι ι' E : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup E] [NormedSpace Real E]
    (e : ι' ≃ ι) :
    ‖(ContinuousLinearEquiv.piCongrLeft Real
        (fun _ : ι => E) e).symm.toContinuousLinearMap‖ <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using (norm_piCongrLeft_symm_apply_eq e x).le

/-- The full real difference-coordinate map has a dimension-free operator
norm bound. Each noninitial coordinate is one adjacent difference. -/
theorem norm_realDiffCoordCLE_le_two
    (n d : Nat) :
    ‖(BHW.realDiffCoordCLE n d).toContinuousLinearMap‖ <= 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro mu
  change ‖BHW.realDiffCoordCLE n d x k mu‖ <= 2 * ‖x‖
  by_cases hk : k.val = 0
  · rw [BHW.realDiffCoordCLE_apply, dif_pos hk]
    calc
      ‖x k mu‖ <= ‖x k‖ := norm_le_pi_norm _ _
      _ <= ‖x‖ := norm_le_pi_norm _ _
      _ <= 2 * ‖x‖ := by nlinarith [norm_nonneg x]
  · rw [BHW.realDiffCoordCLE_apply, dif_neg hk]
    calc
      ‖x k mu - x ⟨k.val - 1, by omega⟩ mu‖ <=
          ‖x k mu‖ + ‖x ⟨k.val - 1, by omega⟩ mu‖ := norm_sub_le _ _
      _ <= ‖x‖ + ‖x‖ := by
        gcongr <;>
          exact (norm_le_pi_norm _ _).trans (norm_le_pi_norm _ _)
      _ = 2 * ‖x‖ := by ring

/-- The inverse real difference-coordinate map is a partial sum, so its
operator norm grows at most linearly with the number of blocks. -/
theorem norm_realDiffCoordCLE_symm_le_arity_add_one
    (n d : Nat) :
    ‖(BHW.realDiffCoordCLE n d).symm.toContinuousLinearMap‖ <=
      (n : Real) + 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro mu
  change
    ‖(BHW.realDiffCoordCLE n d).symm x k mu‖ <=
      ((n : Real) + 1) * ‖x‖
  rw [BHW.realDiffCoordCLE_symm_apply]
  calc
    ‖∑ j : Fin (k.val + 1), x ⟨j.val, by omega⟩ mu‖ <=
        ∑ j : Fin (k.val + 1), ‖x ⟨j.val, by omega⟩ mu‖ :=
      norm_sum_le _ _
    _ <= ∑ _j : Fin (k.val + 1), ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _hj
      exact (norm_le_pi_norm _ _).trans (norm_le_pi_norm _ _)
    _ = ((k.val + 1 : Nat) : Real) * ‖x‖ := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= ((n : Real) + 1) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      norm_cast
      omega

/-- Reindexing contributes no arity growth to the finite-family Schwartz
transport factor. -/
theorem schwartzCompEquivFinsetFactor_piCongrLeft_le_card
    {ι ι' E : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup E] [NormedSpace Real E]
    (e : ι' ≃ ι)
    (s : Finset (Nat × Nat)) :
    schwartzCompEquivFinsetFactor
        (ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : ι => E) e) s <=
      (s.card : Real) := by
  calc
    schwartzCompEquivFinsetFactor
        (ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : ι => E) e) s <=
      ∑ j ∈ s, (1 : Real) ^ j.1 * (1 : Real) ^ j.2 := by
        apply schwartzCompEquivFinsetFactor_le_of_norm_le
        · norm_num
        · exact norm_piCongrLeft_symm_toContinuousLinearMap_le_one e
        · exact norm_piCongrLeft_toContinuousLinearMap_le_one e
    _ = (s.card : Real) := by simp

/-- The only arity-sensitive coordinate cost in the reduced-test lift is
the inverse difference map, and it is polynomial of fixed degree in arity. -/
theorem schwartzCompEquivFinsetFactor_realDiffCoordCLE_le_arityPolynomial
    (d k : Nat) (s : Finset (Nat × Nat)) :
    schwartzCompEquivFinsetFactor (BHW.realDiffCoordCLE (k + 1) d) s <=
      (s.card : Real) * ((k : Real) + 2) ^
          schwartzSeminormWeightOrder s *
        (2 : Real) ^ schwartzSeminormDerivativeOrder s := by
  calc
    schwartzCompEquivFinsetFactor (BHW.realDiffCoordCLE (k + 1) d) s <=
        ∑ j ∈ s, ((k : Real) + 2) ^ j.1 * (2 : Real) ^ j.2 := by
      apply schwartzCompEquivFinsetFactor_le_of_norm_le
      · have hk0 : (0 : Real) <= (k : Real) := by positivity
        linarith
      · calc
          ‖(BHW.realDiffCoordCLE (k + 1) d).symm.toContinuousLinearMap‖ <=
              ((k + 1 : Nat) : Real) + 1 :=
            norm_realDiffCoordCLE_symm_le_arity_add_one (k + 1) d
          _ = (k : Real) + 2 := by push_cast; ring
      · exact norm_realDiffCoordCLE_le_two (k + 1) d
    _ <= ∑ _j ∈ s,
          ((k : Real) + 2) ^ schwartzSeminormWeightOrder s *
            (2 : Real) ^ schwartzSeminormDerivativeOrder s := by
      apply Finset.sum_le_sum
      intro j hj
      have hjp : j.1 <= schwartzSeminormWeightOrder s :=
        Finset.le_sup (f := fun z => z.1) hj
      have hjl : j.2 <= schwartzSeminormDerivativeOrder s :=
        Finset.le_sup (f := fun z => z.2) hj
      have hkbase : (1 : Real) <= (k : Real) + 2 := by
        have hk0 : (0 : Real) <= (k : Real) := by positivity
        linarith
      exact mul_le_mul
        (pow_le_pow_right₀ hkbase hjp)
        (pow_le_pow_right₀ (by norm_num) hjl)
        (pow_nonneg (by positivity) _)
        (pow_nonneg (by positivity) _)
    _ = (s.card : Real) * ((k : Real) + 2) ^
          schwartzSeminormWeightOrder s *
        (2 : Real) ^ schwartzSeminormDerivativeOrder s := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The explicit finite-seminorm coefficient of the reduced-test lift.  The
four factors are, in order, difference coordinates, finite reindexing,
tensor product, and the one-point identification. -/
def reducedTestLiftIndexPreservingFactor
    (d k : Nat) (t : Finset (Nat × Nat)) : Real :=
  let toOnePtEquiv :
      (Fin 1 -> SpacetimeDim d) ≃L[Real] SpacetimeDim d :=
    ContinuousLinearEquiv.funUnique (Fin 1) Real (SpacetimeDim d)
  let castCLE :
      (Fin (k + 1) -> SpacetimeDim d) ≃L[Real]
        (Fin (1 + k) -> SpacetimeDim d) :=
    ContinuousLinearEquiv.piCongrLeft Real
      (fun _ : Fin (1 + k) => SpacetimeDim d)
      (finCongr (Nat.add_comm k 1))
  let diffCLE := BHW.realDiffCoordCLE (k + 1) d
  let rect := schwartzSeminormRectangle t
  schwartzCompEquivFinsetFactor diffCLE t *
    schwartzCompEquivFinsetFactor castCLE t *
      schwartzTensorProductFinsetFactor t *
        schwartzCompEquivFinsetFactor toOnePtEquiv rect

theorem reducedTestLiftIndexPreservingFactor_nonneg
    (d k : Nat) (t : Finset (Nat × Nat)) :
    0 <= reducedTestLiftIndexPreservingFactor d k t := by
  dsimp [reducedTestLiftIndexPreservingFactor]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (schwartzCompEquivFinsetFactor_nonneg _ _)
        (schwartzCompEquivFinsetFactor_nonneg _ _))
      (schwartzTensorProductFinsetFactor_nonneg _))
    (schwartzCompEquivFinsetFactor_nonneg _ _)

set_option maxHeartbeats 1200000 in
/-- The reduced-test lift is controlled by its explicit four-factor
coefficient and one seminorm rectangle determined only by the target
indices. -/
theorem reducedTestLift_indexPreserving_product_bound
    (d k : Nat) (t : Finset (Nat × Nat)) :
    ∀ (chi : SchwartzMap (SpacetimeDim d) Complex)
        (phi : SchwartzNPoint d k),
      t.sup (schwartzSeminormFamily Real
          (NPointDomain d (k + 1)) Complex)
          (BHW.reducedTestLift k d chi phi) <=
        reducedTestLiftIndexPreservingFactor d k t *
          (schwartzSeminormRectangle t).sup
            (schwartzSeminormFamily Real
              (SpacetimeDim d) Complex) chi *
          (schwartzSeminormRectangle t).sup
            (schwartzSeminormFamily Real
              (NPointDomain d k) Complex) phi := by
  let toOnePtEquiv :
      (Fin 1 -> SpacetimeDim d) ≃L[Real] SpacetimeDim d :=
    ContinuousLinearEquiv.funUnique (Fin 1) Real (SpacetimeDim d)
  let castCLE :
      (Fin (k + 1) -> SpacetimeDim d) ≃L[Real]
        (Fin (1 + k) -> SpacetimeDim d) :=
    ContinuousLinearEquiv.piCongrLeft Real
      (fun _ : Fin (1 + k) => SpacetimeDim d)
      (finCongr (Nat.add_comm k 1))
  let diffCLE := BHW.realDiffCoordCLE (k + 1) d
  let rect := schwartzSeminormRectangle t
  let COne := schwartzCompEquivFinsetFactor toOnePtEquiv rect
  let CCast := schwartzCompEquivFinsetFactor castCLE t
  let CDiff := schwartzCompEquivFinsetFactor diffCLE t
  let CTensor := schwartzTensorProductFinsetFactor t
  have hCOne : 0 <= COne :=
    schwartzCompEquivFinsetFactor_nonneg toOnePtEquiv rect
  have hCCast : 0 <= CCast :=
    schwartzCompEquivFinsetFactor_nonneg castCLE t
  have hCDiff : 0 <= CDiff :=
    schwartzCompEquivFinsetFactor_nonneg diffCLE t
  have hCTensor : 0 <= CTensor :=
    schwartzTensorProductFinsetFactor_nonneg t
  intro chi phi
  let one : SchwartzMap (Fin 1 -> SpacetimeDim d) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex toOnePtEquiv chi
  let product : SchwartzMap (Fin (1 + k) -> SpacetimeDim d) Complex :=
    one.tensorProduct phi
  let reindexed :
      SchwartzMap (Fin (k + 1) -> SpacetimeDim d) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex castCLE product
  let lifted : SchwartzNPoint d (k + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex diffCLE reindexed
  let H0 := rect.sup
    (schwartzSeminormFamily Real (SpacetimeDim d) Complex) chi
  let H := rect.sup
    (schwartzSeminormFamily Real
      (Fin 1 -> SpacetimeDim d) Complex) one
  let T := rect.sup
    (schwartzSeminormFamily Real (NPointDomain d k) Complex) phi
  let P := t.sup
    (schwartzSeminormFamily Real
      (Fin (1 + k) -> SpacetimeDim d) Complex) product
  let R := t.sup
    (schwartzSeminormFamily Real
      (Fin (k + 1) -> SpacetimeDim d) Complex) reindexed
  have hH0 : 0 <= H0 := apply_nonneg _ _
  have hH : 0 <= H := apply_nonneg _ _
  have hT : 0 <= T := apply_nonneg _ _
  have hP : 0 <= P := apply_nonneg _ _
  have hR : 0 <= R := apply_nonneg _ _
  have hone : H <= COne * H0 := by
    simpa [H, H0, one, COne, rect] using
      finsetSup_compContinuousLinearEquiv_le toOnePtEquiv rect chi
  have hproduct : P <= CTensor * H * T := by
    simpa [P, CTensor, H, T, product, one, rect] using
      finsetSup_tensorProduct_le 1 k t one phi
  have hreindex : R <= CCast * P := by
    simpa [R, P, CCast, reindexed, product] using
      finsetSup_compContinuousLinearEquiv_le castCLE t product
  have hliftBound :
      t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex) lifted <= CDiff * R := by
    simpa [lifted, R, CDiff] using
      finsetSup_compContinuousLinearEquiv_le diffCLE t reindexed
  have hprepend : reindexed = chi.prependField phi := by
    ext x
    simp only [reindexed, product, one, castCLE, toOnePtEquiv,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.tensorProduct_apply, SchwartzMap.prependField_apply,
      ContinuousLinearEquiv.coe_funUnique, Function.eval, Function.comp,
      splitFirst, ContinuousLinearEquiv.piCongrLeft]
    congr 1
    congr 1
    ext j
    simp [splitLast, Homeomorph.piCongrLeft,
      Equiv.piCongrLeft, Equiv.piCongrLeft']
  have hlift : lifted = BHW.reducedTestLift k d chi phi := by
    change
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex diffCLE) reindexed =
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex diffCLE)
          (chi.prependField phi)
    rw [hprepend]
  calc
    t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex)
        (BHW.reducedTestLift k d chi phi) =
      t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex) lifted := by rw [hlift]
    _ <= CDiff * R := hliftBound
    _ <= CDiff * (CCast * P) :=
      mul_le_mul_of_nonneg_left hreindex hCDiff
    _ <= CDiff * (CCast * (CTensor * H * T)) := by
      gcongr
    _ <= CDiff * (CCast * (CTensor * (COne * H0) * T)) := by
      gcongr
    _ = reducedTestLiftIndexPreservingFactor d k t * H0 * T := by
      dsimp [reducedTestLiftIndexPreservingFactor, CDiff, CCast, CTensor,
        COne, diffCLE, castCLE, toOnePtEquiv, rect]
      ring

end OSReconstruction
