import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import Mathlib.Analysis.Convex.PathConnected

/-!
# Head/tail source indices for rank-deficient normal parameters

The rank-deficient Schur normal form splits the source labels into a selected
head block of size `r` and a tail block of size `n - r`.  This file records
the elementary `Fin` bookkeeping for that split.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The selected head source labels `0, ..., r-1` as labels in `Fin n`. -/
def finSourceHead {r n : ℕ} (hrn : r ≤ n) :
    Fin r → Fin n :=
  Fin.castLE hrn

/-- The tail source labels `r, ..., n-1` as labels in `Fin n`. -/
def finSourceTail {r n : ℕ} (hrn : r ≤ n) :
    Fin (n - r) → Fin n :=
  fun u => Fin.cast (Nat.add_sub_of_le hrn) (Fin.natAdd r u)

@[simp]
theorem finSourceHead_val {r n : ℕ} (hrn : r ≤ n) (a : Fin r) :
    (finSourceHead hrn a).val = a.val := by
  rfl

@[simp]
theorem finSourceTail_val {r n : ℕ} (hrn : r ≤ n) (u : Fin (n - r)) :
    (finSourceTail hrn u).val = r + u.val := by
  simp [finSourceTail]

/-- The head-label inclusion is injective. -/
theorem finSourceHead_injective {r n : ℕ} (hrn : r ≤ n) :
    Function.Injective (finSourceHead hrn) :=
  Fin.castLE_injective hrn

/-- The tail-label inclusion is injective. -/
theorem finSourceTail_injective {r n : ℕ} (hrn : r ≤ n) :
    Function.Injective (finSourceTail hrn) := by
  intro u v huv
  apply Fin.ext
  have hval :
      r + u.val = r + v.val := by
    simpa using congrArg Fin.val huv
  exact Nat.add_left_cancel hval

/-- Head labels and tail labels are disjoint. -/
theorem finSourceHead_ne_finSourceTail {r n : ℕ} (hrn : r ≤ n)
    (a : Fin r) (u : Fin (n - r)) :
    finSourceHead hrn a ≠ finSourceTail hrn u := by
  intro h
  have hval :
      a.val = r + u.val := by
    simpa using congrArg Fin.val h
  omega

/-- Every source label is either in the selected head block or in the tail. -/
theorem finSourceHead_tail_cases {r n : ℕ} (hrn : r ≤ n)
    (i : Fin n) :
    (∃ a : Fin r, i = finSourceHead hrn a) ∨
      (∃ u : Fin (n - r), i = finSourceTail hrn u) := by
  by_cases hi : i.val < r
  · left
    refine ⟨⟨i.val, hi⟩, ?_⟩
    apply Fin.ext
    simp [finSourceHead]
  · right
    have hri : r ≤ i.val := Nat.le_of_not_gt hi
    have htail_lt : i.val - r < n - r := by
      omega
    refine ⟨⟨i.val - r, htail_lt⟩, ?_⟩
    apply Fin.ext
    simp [finSourceTail]
    omega

/-- Finite product coordinates for a rank-deficient source normal form:
an invertible head factor, mixed tail/head coefficients, and residual tail
vectors in the orthogonal complement. -/
structure SourceOrientedRankDeficientNormalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) where
  head : Matrix (Fin r) (Fin r) ℂ
  mixed : Matrix (Fin (n - r)) (Fin r) ℂ
  tail : Fin (n - r) → Fin (d + 1 - r) → ℂ

/-- Product coordinates for the normal-parameter structure. -/
def sourceOrientedNormalParameterCoord
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Matrix (Fin r) (Fin r) ℂ ×
      Matrix (Fin (n - r)) (Fin r) ℂ ×
        (Fin (n - r) → Fin (d + 1 - r) → ℂ) :=
  (p.head, p.mixed, p.tail)

/-- The normal-parameter topology is the topology induced by its finite
product coordinates. -/
instance instTopologicalSpaceSourceOrientedRankDeficientNormalParameter
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    TopologicalSpace
      (SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :=
  TopologicalSpace.induced sourceOrientedNormalParameterCoord inferInstance

/-- The coordinate map from normal parameters to the finite product is
continuous by definition of the induced topology. -/
theorem continuous_sourceOrientedNormalParameterCoord
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (sourceOrientedNormalParameterCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)) :=
  continuous_induced_dom

/-- The normal-parameter record is equivalent to its finite product
coordinates. -/
def sourceOrientedNormalParameterCoordEquiv
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn ≃
      Matrix (Fin r) (Fin r) ℂ ×
        Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ) where
  toFun := sourceOrientedNormalParameterCoord
  invFun := fun x => { head := x.1, mixed := x.2.1, tail := x.2.2 }
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro x
    rcases x with ⟨A, L, q⟩
    rfl

@[simp]
theorem sourceOrientedNormalParameterCoordEquiv_apply
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    sourceOrientedNormalParameterCoordEquiv p =
      sourceOrientedNormalParameterCoord p :=
  rfl

@[simp]
theorem sourceOrientedNormalParameterCoordEquiv_symm_apply
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (x :
      Matrix (Fin r) (Fin r) ℂ ×
        Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ)) :
    (sourceOrientedNormalParameterCoordEquiv
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).symm x =
      { head := x.1, mixed := x.2.1, tail := x.2.2 } :=
  rfl

/-- The induced topology on normal parameters is exactly the finite product
coordinate topology. -/
def sourceOrientedNormalParameterCoordHomeomorph
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn ≃ₜ
      Matrix (Fin r) (Fin r) ℂ ×
        Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ) where
  toEquiv := sourceOrientedNormalParameterCoordEquiv
  continuous_toFun :=
    continuous_sourceOrientedNormalParameterCoord
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_id

/-- The head-factor coordinate is continuous. -/
theorem continuous_sourceOrientedNormalParameter_head
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        p.head) :=
  continuous_fst.comp
    (continuous_sourceOrientedNormalParameterCoord
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))

/-- The determinant-unit condition on the normal head factor is open. -/
theorem isOpen_sourceOrientedNormalParameter_head_det_isUnit
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    IsOpen
      {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
        IsUnit p.head.det} := by
  exact Units.isOpen.preimage
    ((continuous_sourceOrientedNormalParameter_head
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).matrix_det)

/-- The mixed-coordinate matrix is continuous. -/
theorem continuous_sourceOrientedNormalParameter_mixed
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        p.mixed) :=
  continuous_fst.comp
    (continuous_snd.comp
      (continuous_sourceOrientedNormalParameterCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))

/-- The residual-tail coordinate is continuous. -/
theorem continuous_sourceOrientedNormalParameter_tail
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        p.tail) :=
  continuous_snd.comp
    (continuous_snd.comp
      (continuous_sourceOrientedNormalParameterCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))

/-- The center of the normal parameter chart. -/
def sourceOrientedNormalCenterParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn where
  head := 1
  mixed := 0
  tail := 0

@[simp]
theorem sourceOrientedNormalCenterParameter_head_det_isUnit
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    IsUnit (sourceOrientedNormalCenterParameter d n r hrD hrn).head.det := by
  simp [sourceOrientedNormalCenterParameter]

/-- The invertible-head locus is a neighborhood of the normal center. -/
theorem sourceOrientedNormalParameter_head_det_isUnit_mem_nhds_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
      IsUnit p.head.det} ∈
        𝓝 (sourceOrientedNormalCenterParameter d n r hrD hrn) :=
  isOpen_sourceOrientedNormalParameter_head_det_isUnit.mem_nhds
    (sourceOrientedNormalCenterParameter_head_det_isUnit d n r hrD hrn)

/-- A single finite coordinate index for normal parameters: head entries,
mixed entries, and residual-tail vector entries. -/
abbrev SourceOrientedNormalParameterFiniteCoordIndex (d n r : ℕ) :=
  (Fin r × Fin r) ⊕
    ((Fin (n - r) × Fin r) ⊕ (Fin (n - r) × Fin (d + 1 - r)))

/-- Normal parameters encoded as one finite function into `ℂ`.  This is the
metric finite-dimensional coordinate model used for small connected balls. -/
def sourceOrientedNormalParameterFiniteCoord
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ
  | Sum.inl ab => p.head ab.1 ab.2
  | Sum.inr (Sum.inl ua) => p.mixed ua.1 ua.2
  | Sum.inr (Sum.inr uμ) => p.tail uμ.1 uμ.2

/-- The finite-coordinate center corresponding to the normal center parameter. -/
def sourceOrientedNormalParameterFiniteCenterCoord
    (d n r : ℕ) :
    SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ
  | Sum.inl ab => (1 : Matrix (Fin r) (Fin r) ℂ) ab.1 ab.2
  | Sum.inr (Sum.inl _ua) => 0
  | Sum.inr (Sum.inr _uμ) => 0

@[simp]
theorem sourceOrientedNormalParameterFiniteCoord_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterFiniteCoord
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      sourceOrientedNormalParameterFiniteCenterCoord d n r := by
  funext idx
  rcases idx with ab | uaμ
  · rfl
  · rcases uaμ with ua | uμ <;> rfl

/-- The normal-parameter record is equivalent to its single finite-coordinate
function model. -/
def sourceOrientedNormalParameterFiniteCoordEquiv
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn ≃
      (SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ) where
  toFun := sourceOrientedNormalParameterFiniteCoord
  invFun := fun x =>
    { head := fun a b => x (Sum.inl (a, b))
      mixed := fun u a => x (Sum.inr (Sum.inl (u, a)))
      tail := fun u μ => x (Sum.inr (Sum.inr (u, μ))) }
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro x
    funext idx
    rcases idx with ab | uaμ
    · rfl
    · rcases uaμ with ua | uμ <;> rfl

@[simp]
theorem sourceOrientedNormalParameterFiniteCoordEquiv_apply
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    sourceOrientedNormalParameterFiniteCoordEquiv p =
      sourceOrientedNormalParameterFiniteCoord p :=
  rfl

@[simp]
theorem sourceOrientedNormalParameterFiniteCoordEquiv_symm_apply
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (x : SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ) :
    (sourceOrientedNormalParameterFiniteCoordEquiv
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).symm x =
      { head := fun a b => x (Sum.inl (a, b))
        mixed := fun u a => x (Sum.inr (Sum.inl (u, a)))
        tail := fun u μ => x (Sum.inr (Sum.inr (u, μ))) } :=
  rfl

/-- The finite-coordinate encoding is continuous. -/
theorem continuous_sourceOrientedNormalParameterFiniteCoord
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (sourceOrientedNormalParameterFiniteCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)) := by
  apply continuous_pi
  intro idx
  rcases idx with ab | uaμ
  · exact
      (continuous_apply ab.2).comp
        ((continuous_apply ab.1).comp
          (continuous_sourceOrientedNormalParameter_head
            (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))
  · rcases uaμ with ua | uμ
    · exact
        (continuous_apply ua.2).comp
          ((continuous_apply ua.1).comp
            (continuous_sourceOrientedNormalParameter_mixed
              (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))
    · exact
        (continuous_apply uμ.2).comp
          ((continuous_apply uμ.1).comp
            (continuous_sourceOrientedNormalParameter_tail
              (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))

/-- The induced normal-parameter topology is homeomorphic to the single finite
function-coordinate topology. -/
def sourceOrientedNormalParameterFiniteCoordHomeomorph
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn ≃ₜ
      (SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ) where
  toEquiv := sourceOrientedNormalParameterFiniteCoordEquiv
  continuous_toFun := continuous_sourceOrientedNormalParameterFiniteCoord
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous
      (fun x : SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ =>
        ((fun a b => x (Sum.inl (a, b)) : Matrix (Fin r) (Fin r) ℂ),
          (fun u a => x (Sum.inr (Sum.inl (u, a))) :
            Matrix (Fin (n - r)) (Fin r) ℂ),
          (fun u μ => x (Sum.inr (Sum.inr (u, μ))) :
            Fin (n - r) → Fin (d + 1 - r) → ℂ)))
    fun_prop

/-- Metric balls in the single finite-coordinate model around the normal
center. -/
def sourceOrientedNormalParameterFiniteCoordBall
    (d n r : ℕ)
    (ε : ℝ) :
    Set (SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ) :=
  Metric.ball (sourceOrientedNormalParameterFiniteCenterCoord d n r) ε

/-- Finite-coordinate balls are open, connected, and contain the normal
center when their radius is positive. -/
theorem sourceOrientedNormalParameterFiniteCoordBall_open_connected_center
    (d n r : ℕ)
    {ε : ℝ}
    (hε : 0 < ε) :
    IsOpen (sourceOrientedNormalParameterFiniteCoordBall d n r ε) ∧
      IsConnected (sourceOrientedNormalParameterFiniteCoordBall d n r ε) ∧
      sourceOrientedNormalParameterFiniteCenterCoord d n r ∈
        sourceOrientedNormalParameterFiniteCoordBall d n r ε := by
  constructor
  · exact Metric.isOpen_ball
  constructor
  · exact (convex_ball _ _).isConnected ⟨_, Metric.mem_ball_self hε⟩
  · exact Metric.mem_ball_self hε

/-- Embed an orthogonal-tail coordinate vector into the full spacetime
coordinate space by padding the first `r` head coordinates with zero. -/
def sourceTailEmbed
    (d r : ℕ)
    (hrD : r < d + 1)
    (q : Fin (d + 1 - r) → ℂ) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    if h : r ≤ μ.val then
      q ⟨μ.val - r, by omega⟩
    else
      0

@[simp]
theorem sourceTailEmbed_head
    (d r : ℕ)
    (hrD : r < d + 1)
    (q : Fin (d + 1 - r) → ℂ)
    (a : Fin r) :
    sourceTailEmbed d r hrD q
      (finSourceHead (Nat.le_of_lt hrD) a) = 0 := by
  simp [sourceTailEmbed]

@[simp]
theorem sourceTailEmbed_tail
    (d r : ℕ)
    (hrD : r < d + 1)
    (q : Fin (d + 1 - r) → ℂ)
    (u : Fin (d + 1 - r)) :
    sourceTailEmbed d r hrD q
      (finSourceTail (Nat.le_of_lt hrD) u) = q u := by
  simp [sourceTailEmbed]

@[simp]
theorem sourceTailEmbed_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceTailEmbed d r hrD 0 = 0 := by
  ext μ
  by_cases h : r ≤ μ.val <;> simp [sourceTailEmbed, h]

/-- Canonical source tuple for the rank-`r` normal form: the first `r`
source vectors are the first `r` coordinate vectors, and all remaining source
vectors vanish.  The definition is total in `r`; the normal-form route uses it
only under `r < d + 1` and `r ≤ n`. -/
def hwLemma3CanonicalSource
    (d n r : ℕ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i μ =>
    if i.val = μ.val ∧ i.val < r then
      1
    else
      0

@[simp]
theorem hwLemma3CanonicalSource_head_apply
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a : Fin r)
    (μ : Fin (d + 1)) :
    hwLemma3CanonicalSource d n r (finSourceHead hrn a) μ =
      if μ = finSourceHead (Nat.le_of_lt hrD) a then 1 else 0 := by
  by_cases h : μ = finSourceHead (Nat.le_of_lt hrD) a
  · subst μ
    simp [hwLemma3CanonicalSource]
  · have hval : a.val ≠ μ.val := by
      intro hv
      apply h
      apply Fin.ext
      simpa [finSourceHead] using hv.symm
    simp [hwLemma3CanonicalSource, h, hval]

@[simp]
theorem hwLemma3CanonicalSource_head_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a b : Fin r) :
    hwLemma3CanonicalSource d n r (finSourceHead hrn a)
        (finSourceHead (Nat.le_of_lt hrD) b) =
      if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    simp [hwLemma3CanonicalSource]
  · have hval : a.val ≠ b.val := by
      intro hv
      exact h (Fin.ext hv)
    simp [hwLemma3CanonicalSource, h, hval]

@[simp]
theorem hwLemma3CanonicalSource_head_of_tailCoord
    (d n r : ℕ)
    (hrn : r ≤ n)
    (a : Fin r)
    {μ : Fin (d + 1)}
    (hμ : r ≤ μ.val) :
    hwLemma3CanonicalSource d n r (finSourceHead hrn a) μ = 0 := by
  have hval : a.val ≠ μ.val := by
    intro hv
    have : a.val < a.val := by
      calc
        a.val < r := a.isLt
        _ ≤ μ.val := hμ
        _ = a.val := hv.symm
    exact Nat.lt_irrefl a.val this
  simp [hwLemma3CanonicalSource, hval]

@[simp]
theorem hwLemma3CanonicalSource_tail
    (d n r : ℕ)
    (hrn : r ≤ n)
    (u : Fin (n - r)) :
    hwLemma3CanonicalSource d n r (finSourceTail hrn u) = 0 := by
  ext μ
  simp [hwLemma3CanonicalSource]

/-- The canonical head Gram block is the Minkowski-signature diagonal, not the
Euclidean identity block. -/
def sourceHeadMetric
    (d r : ℕ)
    (hrD : r < d + 1) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal fun a =>
    (MinkowskiSpace.metricSignature d
      (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)

@[simp]
theorem sourceHeadMetric_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (a b : Fin r) :
    sourceHeadMetric d r hrD a b =
      if a = b then
        (MinkowskiSpace.metricSignature d
          (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)
      else 0 := by
  by_cases h : a = b <;> simp [sourceHeadMetric, h]

theorem sourceHeadMetric_transpose
    (d r : ℕ)
    (hrD : r < d + 1) :
    (sourceHeadMetric d r hrD)ᵀ = sourceHeadMetric d r hrD := by
  ext a b
  by_cases h : a = b
  · subst b
    simp
  · have hba : b ≠ a := fun hb => h hb.symm
    simp [h, hba]

theorem sourceHeadMetric_det_isUnit
    (d r : ℕ)
    (hrD : r < d + 1) :
    IsUnit (sourceHeadMetric d r hrD).det := by
  rw [sourceHeadMetric]
  simp only [det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro a _ha
  by_cases hzero : finSourceHead (Nat.le_of_lt hrD) a = (0 : Fin (d + 1))
  · simp [MinkowskiSpace.metricSignature, hzero]
  · simp [MinkowskiSpace.metricSignature, hzero]

/-- The residual-tail metric inherited from the ambient source coordinates.
This is the shifted full Minkowski signature, not the standard signature on
`Fin (d + 1 - r)`. -/
def sourceTailMetric
    (d r : ℕ)
    (hrD : r < d + 1) :
    Matrix (Fin (d + 1 - r)) (Fin (d + 1 - r)) ℂ :=
  Matrix.diagonal fun u =>
    (MinkowskiSpace.metricSignature d
      (finSourceTail (Nat.le_of_lt hrD) u) : ℂ)

@[simp]
theorem sourceTailMetric_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (u v : Fin (d + 1 - r)) :
    sourceTailMetric d r hrD u v =
      if u = v then
        (MinkowskiSpace.metricSignature d
          (finSourceTail (Nat.le_of_lt hrD) u) : ℂ)
      else 0 := by
  by_cases h : u = v <;> simp [sourceTailMetric, h]

theorem sourceTailMetric_det_isUnit
    (d r : ℕ)
    (hrD : r < d + 1) :
    IsUnit (sourceTailMetric d r hrD).det := by
  rw [sourceTailMetric]
  simp only [det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro u _hu
  by_cases hzero : finSourceTail (Nat.le_of_lt hrD) u = (0 : Fin (d + 1))
  · simp [MinkowskiSpace.metricSignature, hzero]
  · simp [MinkowskiSpace.metricSignature, hzero]

/-- Coordinate scalar turning the shifted tail metric into the Euclidean dot
product over `ℂ`: use `I` on an inherited time coordinate and `1` otherwise. -/
def sourceTailMetricScale
    (d r : ℕ)
    (hrD : r < d + 1)
    (u : Fin (d + 1 - r)) : ℂ :=
  if finSourceTail (Nat.le_of_lt hrD) u = (0 : Fin (d + 1)) then
    Complex.I
  else
    1

theorem sourceTailMetricScale_ne_zero
    (d r : ℕ)
    (hrD : r < d + 1)
    (u : Fin (d + 1 - r)) :
    sourceTailMetricScale d r hrD u ≠ 0 := by
  unfold sourceTailMetricScale
  by_cases hzero : finSourceTail (Nat.le_of_lt hrD) u = (0 : Fin (d + 1))
  · simp [hzero]
  · simp [hzero]

theorem sourceTailMetricScale_mul_self
    (d r : ℕ)
    (hrD : r < d + 1)
    (u : Fin (d + 1 - r)) :
    sourceTailMetricScale d r hrD u *
        sourceTailMetricScale d r hrD u =
      (MinkowskiSpace.metricSignature d
        (finSourceTail (Nat.le_of_lt hrD) u) : ℂ) := by
  unfold sourceTailMetricScale
  by_cases hzero : finSourceTail (Nat.le_of_lt hrD) u = (0 : Fin (d + 1))
  · simp [MinkowskiSpace.metricSignature, hzero]
  · simp [MinkowskiSpace.metricSignature, hzero]

theorem sourceTailMetricScale_norm
    (d r : ℕ)
    (hrD : r < d + 1)
    (u : Fin (d + 1 - r)) :
    ‖sourceTailMetricScale d r hrD u‖ = 1 := by
  unfold sourceTailMetricScale
  by_cases hzero : finSourceTail (Nat.le_of_lt hrD) u = (0 : Fin (d + 1))
  · simp [hzero]
  · simp [hzero]

/-- Product of the shifted-tail normalizing scalars.  This is the determinant
rescaling factor for full tail-frame determinant coordinates. -/
def sourceTailMetricDetScale
    (d r : ℕ)
    (hrD : r < d + 1) : ℂ :=
  ∏ u : Fin (d + 1 - r), sourceTailMetricScale d r hrD u

theorem sourceTailMetricDetScale_ne_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceTailMetricDetScale d r hrD ≠ 0 := by
  rw [sourceTailMetricDetScale]
  apply Finset.prod_ne_zero_iff.mpr
  intro u _hu
  exact sourceTailMetricScale_ne_zero d r hrD u

theorem sourceTailMetricDetScale_norm
    (d r : ℕ)
    (hrD : r < d + 1) :
    ‖sourceTailMetricDetScale d r hrD‖ = 1 := by
  rw [sourceTailMetricDetScale, norm_prod]
  simp [sourceTailMetricScale_norm]

/-- Full-frame source embedding that takes the selected head labels first and
then an ordered tail frame. -/
def sourceFullFrameEmbeddingOfHeadTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    Fin (d + 1) ↪ Fin n where
  toFun k :=
    if h : k.val < r then
      finSourceHead hrn ⟨k.val, h⟩
    else
      finSourceTail hrn (lam ⟨k.val - r, by omega⟩)
  inj' := by
    intro i j hij
    by_cases hi : i.val < r
    · by_cases hj : j.val < r
      · apply Fin.ext
        simpa [hi, hj] using congrArg Fin.val hij
      · have hval := congrArg Fin.val hij
        simp [hi, hj] at hval
        omega
    · by_cases hj : j.val < r
      · have hval := congrArg Fin.val hij
        simp [hi, hj] at hval
        omega
      · have hval := congrArg Fin.val hij
        simp [hi, hj] at hval
        have h_lam :
            lam ⟨i.val - r, by omega⟩ =
              lam ⟨j.val - r, by omega⟩ := by
          apply Fin.ext
          exact hval
        have htail :
            (⟨i.val - r, by omega⟩ : Fin (d + 1 - r)) =
              ⟨j.val - r, by omega⟩ :=
          lam.injective h_lam
        apply Fin.ext
        have hsub : i.val - r = j.val - r := congrArg Fin.val htail
        have hir : r ≤ i.val := Nat.le_of_not_gt hi
        have hjr : r ≤ j.val := Nat.le_of_not_gt hj
        omega

@[simp]
theorem sourceFullFrameEmbeddingOfHeadTail_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r))
    (a : Fin r) :
    sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam
        (finSourceHead (Nat.le_of_lt hrD) a) =
      finSourceHead hrn a := by
  apply Fin.ext
  simp [sourceFullFrameEmbeddingOfHeadTail]

@[simp]
theorem sourceFullFrameEmbeddingOfHeadTail_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r))
    (u : Fin (d + 1 - r)) :
    sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam
        (finSourceTail (Nat.le_of_lt hrD) u) =
  finSourceTail hrn (lam u) := by
  apply Fin.ext
  simp [sourceFullFrameEmbeddingOfHeadTail]

/-- The complex Minkowski bilinear form on two source vectors. -/
def sourceVectorMinkowskiInner
    (d : ℕ)
    (x y : Fin (d + 1) → ℂ) : ℂ :=
  ∑ μ : Fin (d + 1),
    (MinkowskiSpace.metricSignature d μ : ℂ) * x μ * y μ

/-- Shifted-tail Gram coordinates induced by `sourceTailEmbed`.  This
definition deliberately uses the ambient Minkowski form after embedding, so it
keeps the correct shifted-signature convention by construction. -/
def sourceShiftedTailGram
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun u v =>
    sourceVectorMinkowskiInner d
      (sourceTailEmbed d r hrD (q u))
      (sourceTailEmbed d r hrD (q v))

@[simp]
theorem sourceShiftedTailGram_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (u v : Fin m) :
    sourceShiftedTailGram d r hrD m q u v =
      sourceVectorMinkowskiInner d
        (sourceTailEmbed d r hrD (q u))
        (sourceTailEmbed d r hrD (q v)) := by
  rfl

theorem sourceVectorMinkowskiInner_add_right
    (d : ℕ)
    (x y z : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d x (fun μ => y μ + z μ) =
      sourceVectorMinkowskiInner d x y +
        sourceVectorMinkowskiInner d x z := by
  simp only [sourceVectorMinkowskiInner]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _hμ
  ring

theorem sourceVectorMinkowskiInner_add_left
    (d : ℕ)
    (x y z : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d (fun μ => x μ + y μ) z =
      sourceVectorMinkowskiInner d x z +
        sourceVectorMinkowskiInner d y z := by
  simp only [sourceVectorMinkowskiInner]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _hμ
  ring

theorem sourceVectorMinkowskiInner_sum_right
    {ι : Type*} [Fintype ι]
    (d : ℕ)
    (x : Fin (d + 1) → ℂ)
    (f : ι → Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d x (fun μ => ∑ i, f i μ) =
      ∑ i, sourceVectorMinkowskiInner d x (f i) := by
  simp only [sourceVectorMinkowskiInner, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem sourceVectorMinkowskiInner_sum_left
    {ι : Type*} [Fintype ι]
    (d : ℕ)
    (f : ι → Fin (d + 1) → ℂ)
    (y : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d (fun μ => ∑ i, f i μ) y =
      ∑ i, sourceVectorMinkowskiInner d (f i) y := by
  simp only [sourceVectorMinkowskiInner, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sourceVectorMinkowskiInner_smul_right
    (d : ℕ)
    (x y : Fin (d + 1) → ℂ)
    (c : ℂ) :
    sourceVectorMinkowskiInner d x (fun μ => c * y μ) =
      c * sourceVectorMinkowskiInner d x y := by
  simp [sourceVectorMinkowskiInner, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm]

theorem sourceVectorMinkowskiInner_smul_left
    (d : ℕ)
    (x y : Fin (d + 1) → ℂ)
    (c : ℂ) :
    sourceVectorMinkowskiInner d (fun μ => c * x μ) y =
      c * sourceVectorMinkowskiInner d x y := by
  simp [sourceVectorMinkowskiInner, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm]

theorem sourceMinkowskiGram_hwLemma3CanonicalSource_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a b : Fin r) :
    sourceMinkowskiGram d n (hwLemma3CanonicalSource d n r)
        (finSourceHead hrn a) (finSourceHead hrn b) =
      sourceHeadMetric d r hrD a b := by
  classical
  by_cases hab : a = b
  · subst b
    rw [sourceHeadMetric_apply]
    simp only [if_true]
    rw [sourceMinkowskiGram]
    rw [Finset.sum_eq_single (finSourceHead (Nat.le_of_lt hrD) a)]
    · have hone :
          hwLemma3CanonicalSource d n r (finSourceHead hrn a)
            (finSourceHead (Nat.le_of_lt hrD) a) = 1 := by
        rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
        simp
      simp [hone]
    · intro μ _hμ hne
      have hz :
          hwLemma3CanonicalSource d n r (finSourceHead hrn a) μ = 0 := by
        rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
        simp [hne]
      simp [hz]
    · intro hnot
      simp at hnot
  · rw [sourceHeadMetric_apply]
    simp only [hab, if_false]
    rw [sourceMinkowskiGram]
    rw [Finset.sum_eq_zero]
    intro μ _hμ
    by_cases hμa : μ = finSourceHead (Nat.le_of_lt hrD) a
    · subst μ
      have hne :
          finSourceHead (Nat.le_of_lt hrD) a ≠
            finSourceHead (Nat.le_of_lt hrD) b := by
        intro hEq
        exact hab ((finSourceHead_injective (Nat.le_of_lt hrD)) hEq)
      have hz :
          hwLemma3CanonicalSource d n r (finSourceHead hrn b)
            (finSourceHead (Nat.le_of_lt hrD) a) = 0 := by
        rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
        simp [hne]
      simp [hz]
    · have hz :
          hwLemma3CanonicalSource d n r (finSourceHead hrn a) μ = 0 := by
        rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
        simp [hμa]
      simp [hz]

theorem hwLemma3CanonicalSource_head_unit
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    IsUnit
      (Matrix.det
        (fun a b : Fin r =>
          sourceMinkowskiGram d n (hwLemma3CanonicalSource d n r)
            (finSourceHead hrn a) (finSourceHead hrn b))) := by
  have hmat :
      (fun a b : Fin r =>
        sourceMinkowskiGram d n (hwLemma3CanonicalSource d n r)
          (finSourceHead hrn a) (finSourceHead hrn b)) =
        sourceHeadMetric d r hrD := by
    ext a b
    exact sourceMinkowskiGram_hwLemma3CanonicalSource_head d n r hrD hrn a b
  rw [hmat]
  exact sourceHeadMetric_det_isUnit d r hrD

@[simp]
theorem sourceVectorMinkowskiInner_hwLemma3CanonicalSource_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a b : Fin r) :
    sourceVectorMinkowskiInner d
        (hwLemma3CanonicalSource d n r (finSourceHead hrn a))
        (hwLemma3CanonicalSource d n r (finSourceHead hrn b)) =
      sourceHeadMetric d r hrD a b :=
  sourceMinkowskiGram_hwLemma3CanonicalSource_head d n r hrD hrn a b

/-- Head vectors after applying the head-factor coordinate. -/
def sourceOrientedNormalHeadVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    ∑ b : Fin r,
      p.head a b * hwLemma3CanonicalSource d n r (finSourceHead hrn b) μ

/-- At the center parameter, each normal head vector is the corresponding
canonical head source vector. -/
theorem sourceOrientedNormalHeadVector_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a : Fin r) :
    sourceOrientedNormalHeadVector d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) a =
      hwLemma3CanonicalSource d n r (finSourceHead hrn a) := by
  ext μ
  classical
  rw [sourceOrientedNormalHeadVector, sourceOrientedNormalCenterParameter]
  rw [Finset.sum_eq_single a]
  · simp [hwLemma3CanonicalSource]
  · intro b _ hb
    have hab : a ≠ b := fun h => hb h.symm
    simp [hab]
  · intro ha
    simp at ha

/-- The normal head-vector map is continuous in the finite head-factor
coordinate. -/
theorem continuous_sourceOrientedNormalHeadVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a : Fin r) :
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        sourceOrientedNormalHeadVector d n r hrD hrn p a) := by
  apply continuous_pi
  intro μ
  change
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        ∑ b : Fin r,
          p.head a b *
            hwLemma3CanonicalSource d n r (finSourceHead hrn b) μ)
  refine continuous_finset_sum _ ?_
  intro b _hb
  have hhead_ab :
      Continuous
        (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
          p.head a b) :=
    (continuous_apply b).comp
      ((continuous_apply a).comp
        (continuous_sourceOrientedNormalParameter_head
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))
  exact hhead_ab.mul continuous_const

theorem sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a b : Fin r) :
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn p a)
        (sourceOrientedNormalHeadVector d n r hrD hrn p b) =
      (p.head * sourceHeadMetric d r hrD * p.headᵀ) a b := by
  simp only [sourceVectorMinkowskiInner, sourceOrientedNormalHeadVector,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hwLemma3CanonicalSource_head_apply
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)]
  simp [sourceHeadMetric_apply,
    (finSourceHead_injective (Nat.le_of_lt hrD)).eq_iff,
    mul_assoc, mul_left_comm, mul_comm]

theorem sourceNormalHeadGram_transpose
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    (p.head * sourceHeadMetric d r hrD * p.headᵀ)ᵀ =
      p.head * sourceHeadMetric d r hrD * p.headᵀ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.transpose_apply, sourceHeadMetric_apply,
    mul_assoc, mul_comm]

theorem sourceVectorMinkowskiInner_headVector_sourceTailEmbed
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r)
    (q : Fin (d + 1 - r) → ℂ) :
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn p a)
        (sourceTailEmbed d r hrD q) = 0 := by
  rw [sourceVectorMinkowskiInner]
  apply Finset.sum_eq_zero
  intro μ _hμ
  unfold sourceTailEmbed
  by_cases hμtail : r ≤ μ.val
  · simp [hμtail, sourceOrientedNormalHeadVector]
  · simp [hμtail]

theorem sourceVectorMinkowskiInner_sourceTailEmbed_headVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r)
    (q : Fin (d + 1 - r) → ℂ) :
    sourceVectorMinkowskiInner d
        (sourceTailEmbed d r hrD q)
        (sourceOrientedNormalHeadVector d n r hrD hrn p a) = 0 := by
  rw [sourceVectorMinkowskiInner]
  apply Finset.sum_eq_zero
  intro μ _hμ
  unfold sourceTailEmbed
  by_cases hμtail : r ≤ μ.val
  · simp [hμtail, sourceOrientedNormalHeadVector]
  · simp [hμtail]

/-- Source tuple associated to a normal-form parameter.  Head source labels use
the head-factor vectors; tail labels are a mixed head combination plus an
embedded orthogonal-tail vector. -/
def sourceOrientedNormalParameterVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i =>
    if hi : i.val < r then
      sourceOrientedNormalHeadVector d n r hrD hrn p ⟨i.val, hi⟩
    else
      let u : Fin (n - r) := ⟨i.val - r, by omega⟩
      fun μ =>
        (∑ a : Fin r,
          p.mixed u a *
            sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
        sourceTailEmbed d r hrD (p.tail u) μ

theorem sourceOrientedNormalParameterVector_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r) :
    sourceOrientedNormalParameterVector d n r hrD hrn p
        (finSourceHead hrn a) =
      sourceOrientedNormalHeadVector d n r hrD hrn p a := by
  ext μ
  simp [sourceOrientedNormalParameterVector]

theorem sourceOrientedNormalParameterVector_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (u : Fin (n - r)) :
    sourceOrientedNormalParameterVector d n r hrD hrn p
        (finSourceTail hrn u) =
      fun μ =>
        (∑ a : Fin r,
          p.mixed u a *
            sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
        sourceTailEmbed d r hrD (p.tail u) μ := by
  ext μ
  simp [sourceOrientedNormalParameterVector]

theorem sourceVectorMinkowskiInner_head_tailParameterVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r)
    (u : Fin (n - r)) :
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn p a)
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u)) =
      ((p.head * sourceHeadMetric d r hrD * p.headᵀ) *
        p.mixedᵀ) a u := by
  rw [sourceOrientedNormalParameterVector_tail]
  rw [sourceVectorMinkowskiInner_add_right]
  rw [sourceVectorMinkowskiInner_headVector_sourceTailEmbed]
  simp only [add_zero]
  rw [sourceVectorMinkowskiInner_sum_right]
  simp_rw [sourceVectorMinkowskiInner_smul_right]
  simp [sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector,
    Matrix.mul_apply, Matrix.transpose_apply, mul_assoc, mul_left_comm,
    mul_comm]

theorem sourceVectorMinkowskiInner_tailParameterVector_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (u : Fin (n - r))
    (a : Fin r) :
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u))
        (sourceOrientedNormalHeadVector d n r hrD hrn p a) =
      (p.mixed *
        (p.head * sourceHeadMetric d r hrD * p.headᵀ)) u a := by
  rw [sourceOrientedNormalParameterVector_tail]
  rw [sourceVectorMinkowskiInner_add_left]
  rw [sourceVectorMinkowskiInner_sourceTailEmbed_headVector]
  simp only [add_zero]
  rw [sourceVectorMinkowskiInner_sum_left]
  simp_rw [sourceVectorMinkowskiInner_smul_left]
  simp [sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector,
    Matrix.mul_apply, Matrix.transpose_apply, mul_assoc, mul_left_comm,
    mul_comm]

theorem sourceVectorMinkowskiInner_mixedHeadPart_sourceTailEmbed
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (u : Fin (n - r))
    (q : Fin (d + 1 - r) → ℂ) :
    sourceVectorMinkowskiInner d
        (fun μ =>
          ∑ a : Fin r,
            p.mixed u a *
              sourceOrientedNormalHeadVector d n r hrD hrn p a μ)
        (sourceTailEmbed d r hrD q) = 0 := by
  rw [sourceVectorMinkowskiInner_sum_left]
  simp_rw [sourceVectorMinkowskiInner_smul_left]
  simp [sourceVectorMinkowskiInner_headVector_sourceTailEmbed]

theorem sourceVectorMinkowskiInner_sourceTailEmbed_mixedHeadPart
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (q : Fin (d + 1 - r) → ℂ)
    (v : Fin (n - r)) :
    sourceVectorMinkowskiInner d
        (sourceTailEmbed d r hrD q)
        (fun μ =>
          ∑ b : Fin r,
            p.mixed v b *
              sourceOrientedNormalHeadVector d n r hrD hrn p b μ) = 0 := by
  rw [sourceVectorMinkowskiInner_sum_right]
  simp_rw [sourceVectorMinkowskiInner_smul_right]
  simp [sourceVectorMinkowskiInner_sourceTailEmbed_headVector]

theorem sourceVectorMinkowskiInner_mixedHeadPart_mixedHeadPart
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (u v : Fin (n - r)) :
    sourceVectorMinkowskiInner d
        (fun μ =>
          ∑ a : Fin r,
            p.mixed u a *
              sourceOrientedNormalHeadVector d n r hrD hrn p a μ)
        (fun μ =>
          ∑ b : Fin r,
            p.mixed v b *
              sourceOrientedNormalHeadVector d n r hrD hrn p b μ) =
      (p.mixed *
        (p.head * sourceHeadMetric d r hrD * p.headᵀ) *
          p.mixedᵀ) u v := by
  let S : Matrix (Fin r) (Fin r) ℂ :=
    p.head * sourceHeadMetric d r hrD * p.headᵀ
  have hleft :
      sourceVectorMinkowskiInner d
          (fun μ =>
            ∑ a : Fin r,
              p.mixed u a *
                sourceOrientedNormalHeadVector d n r hrD hrn p a μ)
          (fun μ =>
            ∑ b : Fin r,
              p.mixed v b *
                sourceOrientedNormalHeadVector d n r hrD hrn p b μ) =
        ∑ a : Fin r, ∑ b : Fin r,
          p.mixed u a * p.mixed v b * S a b := by
    rw [sourceVectorMinkowskiInner_sum_left]
    simp_rw [sourceVectorMinkowskiInner_smul_left]
    simp_rw [sourceVectorMinkowskiInner_sum_right]
    simp_rw [sourceVectorMinkowskiInner_smul_right]
    simp_rw [sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]
    change
      (∑ a : Fin r, p.mixed u a * ∑ b : Fin r, p.mixed v b * S a b) =
        ∑ a : Fin r, ∑ b : Fin r,
          p.mixed u a * p.mixed v b * S a b
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  have hright :
      (p.mixed * S * p.mixedᵀ) u v =
        ∑ a : Fin r, ∑ b : Fin r,
          p.mixed u a * p.mixed v b * S a b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  exact hleft.trans hright.symm

theorem sourceVectorMinkowskiInner_tailParameterVector_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (u v : Fin (n - r)) :
    sourceVectorMinkowskiInner d
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u))
        (sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn v)) =
      (p.mixed *
          (p.head * sourceHeadMetric d r hrD * p.headᵀ) *
            p.mixedᵀ +
        sourceShiftedTailGram d r hrD (n - r) p.tail) u v := by
  rw [sourceOrientedNormalParameterVector_tail]
  rw [sourceOrientedNormalParameterVector_tail]
  simp [sourceVectorMinkowskiInner_add_left,
    sourceVectorMinkowskiInner_add_right,
    sourceVectorMinkowskiInner_mixedHeadPart_sourceTailEmbed,
    sourceVectorMinkowskiInner_sourceTailEmbed_mixedHeadPart,
    sourceVectorMinkowskiInner_mixedHeadPart_mixedHeadPart,
    sourceShiftedTailGram]

/-- The normal-parameter source tuple is continuous in the finite product
coordinates. -/
theorem continuous_sourceOrientedNormalParameterVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedNormalParameterVector d n r hrD hrn) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  by_cases hi : i.val < r
  · simpa [sourceOrientedNormalParameterVector, hi] using
      (continuous_apply μ).comp
        (continuous_sourceOrientedNormalHeadVector d n r hrD hrn
          ⟨i.val, hi⟩)
  · let u : Fin (n - r) := ⟨i.val - r, by omega⟩
    have hmixed :
        ∀ a : Fin r,
          Continuous
            (fun p :
                SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
              p.mixed u a) := by
      intro a
      exact
        (continuous_apply a).comp
          ((continuous_apply u).comp
            (continuous_sourceOrientedNormalParameter_mixed
              (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))
    have hhead :
        ∀ a : Fin r,
          Continuous
            (fun p :
                SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
              sourceOrientedNormalHeadVector d n r hrD hrn p a μ) := by
      intro a
      exact
        (continuous_apply μ).comp
          (continuous_sourceOrientedNormalHeadVector d n r hrD hrn a)
    have hsum :
        Continuous
          (fun p :
              SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
            ∑ a : Fin r,
              p.mixed u a *
                sourceOrientedNormalHeadVector d n r hrD hrn p a μ) := by
      refine continuous_finset_sum _ ?_
      intro a _ha
      exact (hmixed a).mul (hhead a)
    have htail :
        Continuous
          (fun p :
              SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
            sourceTailEmbed d r hrD (p.tail u) μ) := by
      unfold sourceTailEmbed
      by_cases hμ : r ≤ μ.val
      · simp [hμ]
        exact
          (continuous_apply ⟨μ.val - r, by omega⟩).comp
            ((continuous_apply u).comp
              (continuous_sourceOrientedNormalParameter_tail
                (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))
      · simp [hμ]
        exact continuous_const
    simpa [sourceOrientedNormalParameterVector, hi, u] using hsum.add htail

/-- At the center parameter, the normal-parameter vector is the canonical
rank-`r` source. -/
theorem sourceOrientedNormalParameterVector_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterVector d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      hwLemma3CanonicalSource d n r := by
  ext i μ
  by_cases hi : i.val < r
  · simp [sourceOrientedNormalParameterVector, hi,
      sourceOrientedNormalHeadVector_center, hwLemma3CanonicalSource]
  · have hcanon : hwLemma3CanonicalSource d n r i μ = 0 := by
      simp [hwLemma3CanonicalSource, hi]
    simp [sourceOrientedNormalParameterVector, hi,
      sourceOrientedNormalHeadVector, sourceOrientedNormalCenterParameter,
      hcanon]

end BHW
