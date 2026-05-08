import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailWindow

/-!
# Sliced rank-deficient source Schur parameters

The constructible head gauge is defined on the transverse slice
`SourceHeadGaugeSlice`, while the older Schur parameter window used an ambient
matrix head coordinate.  This file introduces the corresponding sliced normal
parameter type and the basic topology/membership bridges back to the existing
normal-parameter API.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Rank-deficient normal parameters whose head coordinate is a point of the
transverse head-gauge slice. -/
structure SourceOrientedRankDeficientSlicedNormalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) where
  head : SourceHeadGaugeSlice d r hrD
  mixed : Matrix (Fin (n - r)) (Fin r) ℂ
  tail : Fin (n - r) → Fin (d + 1 - r) → ℂ

/-- Product coordinates for the sliced normal-parameter structure. -/
def sourceOrientedSlicedNormalParameterCoord
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn) :
    SourceHeadGaugeSlice d r hrD ×
      Matrix (Fin (n - r)) (Fin r) ℂ ×
        (Fin (n - r) → Fin (d + 1 - r) → ℂ) :=
  (p.head, p.mixed, p.tail)

/-- The sliced normal-parameter topology is the topology induced by its finite
product coordinates, including the inherited topology on the head slice. -/
instance instTopologicalSpaceSourceOrientedRankDeficientSlicedNormalParameter
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    TopologicalSpace
      (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn) :=
  TopologicalSpace.induced sourceOrientedSlicedNormalParameterCoord inferInstance

/-- The sliced coordinate map is continuous by definition of the induced
topology. -/
theorem continuous_sourceOrientedSlicedNormalParameterCoord
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (sourceOrientedSlicedNormalParameterCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)) :=
  continuous_induced_dom

/-- The sliced normal-parameter record is equivalent to its product
coordinates. -/
def sourceOrientedSlicedNormalParameterCoordEquiv
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn ≃
      SourceHeadGaugeSlice d r hrD ×
        Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ) where
  toFun := sourceOrientedSlicedNormalParameterCoord
  invFun := fun x => { head := x.1, mixed := x.2.1, tail := x.2.2 }
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro x
    rcases x with ⟨H, L, q⟩
    rfl

/-- The induced topology on sliced normal parameters is exactly the product
coordinate topology. -/
def sourceOrientedSlicedNormalParameterCoordHomeomorph
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn ≃ₜ
      SourceHeadGaugeSlice d r hrD ×
        Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ) where
  toEquiv := sourceOrientedSlicedNormalParameterCoordEquiv
  continuous_toFun :=
    continuous_sourceOrientedSlicedNormalParameterCoord
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_id

/-- The sliced head-coordinate projection is continuous. -/
theorem continuous_sourceOrientedSlicedNormalParameter_head
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn =>
        p.head) :=
  continuous_fst.comp
    (continuous_sourceOrientedSlicedNormalParameterCoord
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))

/-- The sliced mixed-coordinate projection is continuous. -/
theorem continuous_sourceOrientedSlicedNormalParameter_mixed
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn =>
        p.mixed) :=
  continuous_fst.comp
    (continuous_snd.comp
      (continuous_sourceOrientedSlicedNormalParameterCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))

/-- The sliced tail-coordinate projection is continuous. -/
theorem continuous_sourceOrientedSlicedNormalParameter_tail
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn =>
        p.tail) :=
  continuous_snd.comp
    (continuous_snd.comp
      (continuous_sourceOrientedSlicedNormalParameterCoord
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))

/-- Forget the slice proof on the head coordinate, producing the old normal
parameter record. -/
def SourceOrientedRankDeficientSlicedNormalParameter.toNormalParameter
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn) :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn where
  head := p.head.1
  mixed := p.mixed
  tail := p.tail

/-- Forgetting the slice proof is continuous. -/
theorem continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn =>
        p.toNormalParameter) := by
  rw [continuous_induced_rng]
  exact
    (continuous_subtype_val.comp
        (continuous_sourceOrientedSlicedNormalParameter_head
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))).prodMk
      ((continuous_sourceOrientedSlicedNormalParameter_mixed
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).prodMk
        (continuous_sourceOrientedSlicedNormalParameter_tail
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)))

/-- The canonical source-variety point associated to a sliced normal
parameter, obtained by forgetting the slice proof and using the existing
normal-parameter image map. -/
def sourceOrientedSlicedNormalParameterVarietyPoint
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn) :
    SourceOrientedVariety d n :=
  sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p.toNormalParameter

/-- The sliced normal-parameter variety map is continuous. -/
theorem continuous_sourceOrientedSlicedNormalParameterVarietyPoint
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedSlicedNormalParameterVarietyPoint d n r hrD hrn) :=
  (continuous_sourceOrientedNormalParameterVarietyPoint d n r hrD hrn).comp
    (continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))

/-- The center of the sliced normal-parameter chart. -/
def sourceOrientedSlicedNormalCenterParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn where
  head := sourceHeadGaugeSliceCenter d r hrD
  mixed := 0
  tail := 0

@[simp]
theorem sourceOrientedSlicedNormalCenterParameter_toNormalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    (sourceOrientedSlicedNormalCenterParameter d n r hrD hrn).toNormalParameter =
      sourceOrientedNormalCenterParameter d n r hrD hrn := by
  rfl

/-- The sliced Schur parameter window: the head lies in a slice-coordinate
window, the mixed coordinate is small, and the tail satisfies the existing
target-shaped shifted-tail bounds. -/
def sourceOrientedRankDeficientSlicedSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn) :=
  {p |
    p.head ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD headRadius ∧
    p.mixed ∈ sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
    p.toNormalParameter ∈
      sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail}

/-- The sliced Schur parameter window is open in the sliced parameter
topology. -/
theorem isOpen_sourceOrientedRankDeficientSlicedSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen
      (sourceOrientedRankDeficientSlicedSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) := by
  let P := SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn
  have hhead_open :
      IsOpen {p : P |
        p.head ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD headRadius} := by
    exact
      IsOpen.preimage
        (continuous_sourceOrientedSlicedNormalParameter_head
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))
        (isOpen_sourceHeadGaugeSliceCoordinateWindow d r hrD headRadius)
  have hmixed_open :
      IsOpen {p : P |
        p.mixed ∈ sourceOrientedMixedCoordinateWindow n r mixedRadius} := by
    exact
      IsOpen.preimage
        (continuous_sourceOrientedSlicedNormalParameter_mixed
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))
        (isOpen_sourceOrientedMixedCoordinateWindow n r mixedRadius)
  have htail_open :
      IsOpen {p : P |
        p.toNormalParameter ∈
          sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail} := by
    exact
      IsOpen.preimage
        (continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))
        (isOpen_sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail)
  simpa [sourceOrientedRankDeficientSlicedSchurParameterWindow, Set.setOf_and] using
    hhead_open.inter (hmixed_open.inter htail_open)

/-- The sliced center lies in every positive sliced Schur parameter window. -/
theorem sourceOrientedSlicedNormalCenterParameter_mem_slicedSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    sourceOrientedSlicedNormalCenterParameter d n r hrD hrn ∈
      sourceOrientedRankDeficientSlicedSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail := by
  refine ⟨?_, ?_, ?_⟩
  · exact sourceHeadGaugeSliceCenter_mem_coordinateWindow d r hrD hheadRadius
  · intro u a
    simpa [sourceOrientedSlicedNormalCenterParameter] using hmixedRadius
  · simpa using
      sourceOrientedNormalCenterParameter_mem_tailWindow d n r hrD hrn Tail

/-- A sliced Schur-window point forgets to a point of the old ambient
normal-parameter Schur window. -/
theorem sourceOrientedSlicedSchurParameterWindow_toNormalParameter_mem
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {headRadius mixedRadius : ℝ}
    {Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn}
    {p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn}
    (hp :
      p ∈ sourceOrientedRankDeficientSlicedSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) :
    p.toNormalParameter ∈
      sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail := by
  refine ⟨?_, hp.2.1, hp.2.2⟩
  intro a b
  exact hp.1 a b

/-- The straight real affine segment between two head-slice points stays in
the head slice. -/
def sourceHeadGaugeSliceSegment
    (d r : ℕ)
    (hrD : r < d + 1)
    (H K : SourceHeadGaugeSlice d r hrD)
    (t : ℝ) :
    SourceHeadGaugeSlice d r hrD :=
  ⟨(1 - t) • H.1 + t • K.1, by
    rw [Matrix.add_mul, smul_mul_assoc, smul_mul_assoc]
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
    rw [← H.2, ← K.2]⟩

/-- Any two points of a positive slice-coordinate head window are joined
inside that window by the straight real affine segment. -/
theorem sourceHeadGaugeSliceCoordinateWindow_joined
    (d r : ℕ)
    (hrD : r < d + 1)
    {ρ : ℝ}
    {H K : SourceHeadGaugeSlice d r hrD}
    (hH : H ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD ρ)
    (hK : K ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD ρ) :
    JoinedIn (sourceHeadGaugeSliceCoordinateWindow d r hrD ρ) H K := by
  let f : ℝ → SourceHeadGaugeSlice d r hrD :=
    sourceHeadGaugeSliceSegment d r hrD H K
  refine JoinedIn.ofLine (f := f) ?_ ?_ ?_ ?_
  · have hcont_val :
        Continuous fun t : ℝ =>
          ((sourceHeadGaugeSliceSegment d r hrD H K t).1 :
            Matrix (Fin r) (Fin r) ℂ) := by
        change Continuous fun t : ℝ =>
          ((sourceHeadGaugeSliceSegment d r hrD H K t).1 :
            Matrix (Fin r) (Fin r) ℂ)
        simp [sourceHeadGaugeSliceSegment]
        fun_prop
    exact
      (hcont_val.subtype_mk
        (fun t => (sourceHeadGaugeSliceSegment d r hrD H K t).2)).continuousOn
  · apply Subtype.ext
    ext a b
    simp [f, sourceHeadGaugeSliceSegment]
  · apply Subtype.ext
    ext a b
    simp [f, sourceHeadGaugeSliceSegment]
  · rintro X ⟨t, ht, rfl⟩
    change t ∈ Set.Icc (0 : ℝ) 1 at ht
    have hH' :
        H.1 ∈ sourceMatrixCoordinateWindow
          (1 : Matrix (Fin r) (Fin r) ℂ) ρ := by
      simpa [sourceHeadGaugeSliceCoordinateWindow,
        sourceHeadFactorCoordinateWindow, sourceMatrixCoordinateWindow] using hH
    have hK' :
        K.1 ∈ sourceMatrixCoordinateWindow
          (1 : Matrix (Fin r) (Fin r) ℂ) ρ := by
      simpa [sourceHeadGaugeSliceCoordinateWindow,
        sourceHeadFactorCoordinateWindow, sourceMatrixCoordinateWindow] using hK
    have hseg :
        ((1 - t) • H.1 + t • K.1) ∈
          sourceMatrixCoordinateWindow
            (1 : Matrix (Fin r) (Fin r) ℂ) ρ := by
      have hconv :=
        convex_sourceMatrixCoordinateWindow
          (1 : Matrix (Fin r) (Fin r) ℂ) ρ
      have hsum : (1 - t) + t = (1 : ℝ) := by ring
      exact hconv hH' hK' (sub_nonneg.mpr ht.2) ht.1 hsum
    intro a b
    simpa [f, sourceHeadGaugeSliceSegment,
      sourceHeadGaugeSliceCoordinateWindow, sourceHeadFactorCoordinateWindow,
      sourceMatrixCoordinateWindow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      using hseg a b

/-- Positive slice-coordinate head windows are path-connected. -/
theorem isPathConnected_sourceHeadGaugeSliceCoordinateWindow
    (d r : ℕ)
    (hrD : r < d + 1)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsPathConnected (sourceHeadGaugeSliceCoordinateWindow d r hrD ρ) := by
  rw [isPathConnected_iff]
  constructor
  · exact
      ⟨sourceHeadGaugeSliceCenter d r hrD,
        sourceHeadGaugeSliceCenter_mem_coordinateWindow d r hrD hρ⟩
  · intro H hH K hK
    exact sourceHeadGaugeSliceCoordinateWindow_joined d r hrD hH hK

/-- Positive slice-coordinate head windows are connected. -/
theorem isConnected_sourceHeadGaugeSliceCoordinateWindow
    (d r : ℕ)
    (hrD : r < d + 1)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsConnected (sourceHeadGaugeSliceCoordinateWindow d r hrD ρ) :=
  (isPathConnected_sourceHeadGaugeSliceCoordinateWindow d r hrD hρ).isConnected

/-- The sliced Schur parameter window is connected for positive head and
mixed radii. -/
theorem isConnected_sourceOrientedRankDeficientSlicedSchurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsConnected
      (sourceOrientedRankDeficientSlicedSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) := by
  let S : Set (SourceHeadGaugeSlice d r hrD ×
      Matrix (Fin (n - r)) (Fin r) ℂ ×
        (Fin (n - r) → Fin (d + 1 - r) → ℂ)) :=
    sourceHeadGaugeSliceCoordinateWindow d r hrD headRadius ×ˢ
      (sourceOrientedMixedCoordinateWindow n r mixedRadius ×ˢ
        sourceShiftedTailTupleWindow d n r hrD hrn Tail)
  have hhead_conn :
      IsConnected (sourceHeadGaugeSliceCoordinateWindow d r hrD headRadius) :=
    isConnected_sourceHeadGaugeSliceCoordinateWindow d r hrD hheadRadius
  have hmixed_conn :
      IsConnected (sourceOrientedMixedCoordinateWindow n r mixedRadius) :=
    isConnected_sourceOrientedMixedCoordinateWindow n r hmixedRadius
  have htail_conn :
      IsConnected (sourceShiftedTailTupleWindow d n r hrD hrn Tail) :=
    isConnected_sourceShiftedTailTupleWindow d n r hrD hrn Tail
  have hS : IsConnected S := by
    dsimp [S]
    exact hhead_conn.prod (hmixed_conn.prod htail_conn)
  let e :=
    sourceOrientedSlicedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have himage : e.symm '' S = e ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨e p, hp, by simp [e]⟩
  have hpre : IsConnected (e ⁻¹' S) := by
    rw [← himage]
    exact hS.image e.symm e.symm.continuous.continuousOn
  have heq :
      sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail =
        e ⁻¹' S := by
    ext p
    simp [sourceOrientedRankDeficientSlicedSchurParameterWindow, S, e,
      sourceOrientedRankDeficientTailWindow, sourceShiftedTailTupleWindow,
      sourceOrientedSlicedNormalParameterCoordHomeomorph,
      sourceOrientedSlicedNormalParameterCoordEquiv,
      sourceOrientedSlicedNormalParameterCoord,
      SourceOrientedRankDeficientSlicedNormalParameter.toNormalParameter]
  rw [heq]
  exact hpre

/-- Connectedness of the sliced Schur-parameter window restricted to the
residual-tail exact-rank slice reduces to the corresponding tail-coordinate
connectedness theorem. -/
theorem isConnected_sourceOrientedRankDeficientSlicedSchurParameterWindow_tailRank
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    (htailRank_conn :
      IsConnected (sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
        {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
          (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r})) :
    IsConnected
      (sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail ∩
        {p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn |
          (sourceOrientedNormalParameterSchurTail d n r hrD hrn
            p.toNormalParameter).rank = d + 1 - r}) := by
  let H : Set (SourceHeadGaugeSlice d r hrD) :=
    sourceHeadGaugeSliceCoordinateWindow d r hrD headRadius
  let M : Set (Matrix (Fin (n - r)) (Fin r) ℂ) :=
    sourceOrientedMixedCoordinateWindow n r mixedRadius
  let T : Set (Fin (n - r) → Fin (d + 1 - r) → ℂ) :=
    sourceShiftedTailTupleWindow d n r hrD hrn Tail ∩
      {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        (sourceShiftedTailGram d r hrD (n - r) q).rank = d + 1 - r}
  let S : Set (SourceHeadGaugeSlice d r hrD ×
      Matrix (Fin (n - r)) (Fin r) ℂ ×
        (Fin (n - r) → Fin (d + 1 - r) → ℂ)) :=
    H ×ˢ (M ×ˢ T)
  have hhead_conn : IsConnected H :=
    isConnected_sourceHeadGaugeSliceCoordinateWindow d r hrD hheadRadius
  have hmixed_conn : IsConnected M :=
    isConnected_sourceOrientedMixedCoordinateWindow n r hmixedRadius
  have htail_conn : IsConnected T := by
    dsimp [T]
    exact htailRank_conn
  have hS : IsConnected S := by
    dsimp [S]
    exact hhead_conn.prod (hmixed_conn.prod htail_conn)
  let e :=
    sourceOrientedSlicedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have himage : e.symm '' S = e ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨e p, hp, by simp [e]⟩
  have hpre : IsConnected (e ⁻¹' S) := by
    rw [← himage]
    exact hS.image e.symm e.symm.continuous.continuousOn
  have heq :
      sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n r hrD hrn headRadius mixedRadius Tail ∩
          {p : SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn |
            (sourceOrientedNormalParameterSchurTail d n r hrD hrn
              p.toNormalParameter).rank = d + 1 - r} =
        e ⁻¹' S := by
    ext p
    simp [sourceOrientedRankDeficientSlicedSchurParameterWindow, S, H, M, T, e,
      sourceOrientedRankDeficientTailWindow, sourceShiftedTailTupleWindow,
      sourceOrientedNormalParameterSchurTail,
      sourceOrientedSlicedNormalParameterCoordHomeomorph,
      sourceOrientedSlicedNormalParameterCoordEquiv,
      sourceOrientedSlicedNormalParameterCoord,
      SourceOrientedRankDeficientSlicedNormalParameter.toNormalParameter]
    tauto
  rw [heq]
  exact hpre

/-- The sliced Schur parameter window is an open connected neighborhood of the
sliced normal center. -/
theorem sourceOrientedRankDeficientSlicedSchurParameterWindow_open_connected
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen
        (sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail) ∧
      IsConnected
        (sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail) ∧
      sourceOrientedSlicedNormalCenterParameter d n r hrD hrn ∈
        sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail := by
  exact
    ⟨isOpen_sourceOrientedRankDeficientSlicedSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail,
      isConnected_sourceOrientedRankDeficientSlicedSchurParameterWindow
        d n r hrD hrn hheadRadius hmixedRadius Tail,
      sourceOrientedSlicedNormalCenterParameter_mem_slicedSchurParameterWindow
        d n r hrD hrn hheadRadius hmixedRadius Tail⟩

end BHW
