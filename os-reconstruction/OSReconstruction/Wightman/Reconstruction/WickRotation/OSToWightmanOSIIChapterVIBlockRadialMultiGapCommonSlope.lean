/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapSemigroupPacket











noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

variable {d n : Nat} [NeZero d]

/-- A set which is ordered-positive in every signed axis-pair frame stays
ordered-positive when the common time slope is increased. -/
theorem subset_all_orientedPositive_mono
    (K : Set (NPointDomain d n))
    {T T' : Real}
    (hT : 0 < T) (hTT' : T <= T')
    (hK : forall a : osiiAxisPairIndex d,
      K <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix) :
    forall a : osiiAxisPairIndex d,
      K <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T' a).matrix := by
  intro a x hx i
  have ha := hK a hx i
  have hop := hK (osiiAxisPairOpposite a) hx i
  have hbase :
      0 < T * x i 0 +
        if a.2 then x i (Fin.succ a.1) else -x i (Fin.succ a.1) := by
    have ha0 := ha.1
    change 0 < ((osiiAxisPairRotationData T a).matrix.mulVec (x i)) 0 at ha0
    rw [(osiiAxisPairRotationData T a).mulVec_time] at ha0
    exact (mul_pos_iff_of_pos_left
      (inv_pos.mpr (osiiAxisPairRadius_pos T))).mp ha0
  have hopbase :
      0 < T * x i 0 +
        if (osiiAxisPairOpposite a).2
          then x i (Fin.succ (osiiAxisPairOpposite a).1)
          else -x i (Fin.succ (osiiAxisPairOpposite a).1) := by
    have hop0 := hop.1
    change 0 < ((osiiAxisPairRotationData T
      (osiiAxisPairOpposite a)).matrix.mulVec (x i)) 0 at hop0
    rw [(osiiAxisPairRotationData T
      (osiiAxisPairOpposite a)).mulVec_time] at hop0
    exact (mul_pos_iff_of_pos_left
      (inv_pos.mpr (osiiAxisPairRadius_pos T))).mp hop0
  have htime : 0 < x i 0 := by
    rcases a with ⟨a, s⟩
    cases s <;>
      simp [osiiAxisPairOpposite] at hbase hopbase ⊢ <;>
      nlinarith
  change
    0 < ((osiiAxisPairRotationData T' a).matrix.mulVec (x i)) 0 ∧
      forall j : Fin n, i < j ->
        ((osiiAxisPairRotationData T' a).matrix.mulVec (x i)) 0 <
          ((osiiAxisPairRotationData T' a).matrix.mulVec (x j)) 0
  constructor
  · rw [(osiiAxisPairRotationData T' a).mulVec_time]
    apply (mul_pos_iff_of_pos_left
      (inv_pos.mpr (osiiAxisPairRadius_pos T'))).2
    rcases a with ⟨a, s⟩
    cases s <;>
      simp at hbase ⊢ <;>
      nlinarith
  · intro j hij
    have hagap := ha.2 j hij
    have hopgap := hop.2 j hij
    change
      ((osiiAxisPairRotationData T a).matrix.mulVec (x i)) 0 <
        ((osiiAxisPairRotationData T a).matrix.mulVec (x j)) 0 at hagap
    change
      ((osiiAxisPairRotationData T
          (osiiAxisPairOpposite a)).matrix.mulVec (x i)) 0 <
        ((osiiAxisPairRotationData T
          (osiiAxisPairOpposite a)).matrix.mulVec (x j)) 0 at hopgap
    rw [(osiiAxisPairRotationData T a).mulVec_time,
      (osiiAxisPairRotationData T a).mulVec_time,
      mul_lt_mul_iff_right₀
        (inv_pos.mpr (osiiAxisPairRadius_pos T))] at hagap
    rw [(osiiAxisPairRotationData T
        (osiiAxisPairOpposite a)).mulVec_time,
      (osiiAxisPairRotationData T
        (osiiAxisPairOpposite a)).mulVec_time,
      mul_lt_mul_iff_right₀
        (inv_pos.mpr (osiiAxisPairRadius_pos T))] at hopgap
    have htimegap : x i 0 < x j 0 := by
      rcases a with ⟨a, s⟩
      cases s <;>
        simp [osiiAxisPairOpposite] at hagap hopgap ⊢ <;>
        nlinarith
    rw [(osiiAxisPairRotationData T' a).mulVec_time,
      (osiiAxisPairRotationData T' a).mulVec_time,
      mul_lt_mul_iff_right₀
        (inv_pos.mpr (osiiAxisPairRadius_pos T'))]
    rcases a with ⟨a, s⟩
    cases s <;>
      simp at hagap ⊢ <;>
      nlinarith

private theorem exists_pos_le_on_compact_of_forall_pos
    {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K)
    {g : E -> Real} (hg : Continuous g)
    (hpos : forall x, x ∈ K -> 0 < g x) :
    exists delta : Real, 0 < delta ∧ forall x, x ∈ K -> delta <= g x := by
  by_cases hK_nonempty : K.Nonempty
  · obtain ⟨x0, hx0, hx0_min⟩ :=
      hK.exists_isMinOn hK_nonempty hg.continuousOn
    refine ⟨g x0 / 2, div_pos (hpos x0 hx0) (by norm_num), ?_⟩
    intro x hx
    have hmin : g x0 <= g x := isMinOn_iff.mp hx0_min x hx
    linarith [hpos x0 hx0]
  · exact ⟨1, by positivity, fun x hx => False.elim (hK_nonempty ⟨x, hx⟩)⟩

/-- A compact subset of the ordered positive-time region has one uniform
distance from every positivity and chronology wall.  Unlike the older
support theorem, this formulation can be applied once to a common carrier
for an entire source family. -/
theorem exists_orderedPositiveTimeRegion_margin_of_compact_subset
    (d n : Nat)
    (K : Set (NPointDomain d n))
    (hK_compact : IsCompact K)
    (hK_ordered : K ⊆ OrderedPositiveTimeRegion d n) :
    exists delta : Real, 0 < delta ∧
      K ⊆ {x |
        (forall i : Fin n, delta <= x i 0) ∧
        forall i j : Fin n, i < j -> delta <= x j 0 - x i 0} := by
  let I : Type :=
    ULift Unit ⊕ (Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2})
  have hI_nonempty : (Finset.univ : Finset I).Nonempty :=
    ⟨Sum.inl (ULift.up ()), Finset.mem_univ _⟩
  let lower : I -> NPointDomain d n -> Real := fun a =>
    match a with
    | Sum.inl _ => fun _ => 1
    | Sum.inr (Sum.inl i) => fun x => x i 0
    | Sum.inr (Sum.inr p) => fun x => x p.1.2 0 - x p.1.1 0
  have hbounds : forall a : I,
      exists epsilon : Real, 0 < epsilon ∧
        forall x, x ∈ K -> epsilon <= lower a x := by
    intro a
    cases a with
    | inl _ =>
        exact ⟨1, by positivity, by simp [lower]⟩
    | inr b =>
        cases b with
        | inl i =>
            apply exists_pos_le_on_compact_of_forall_pos hK_compact
            · exact (continuous_apply (0 : Fin (d + 1))).comp
                (continuous_apply i)
            · intro x hx
              exact (hK_ordered hx i).1
        | inr p =>
            apply exists_pos_le_on_compact_of_forall_pos hK_compact
            · exact
                (((continuous_apply (0 : Fin (d + 1))).comp
                    (continuous_apply p.1.2)).sub
                  ((continuous_apply (0 : Fin (d + 1))).comp
                    (continuous_apply p.1.1)))
            · intro x hx
              exact sub_pos.mpr ((hK_ordered hx p.1.1).2 p.1.2 p.2)
  let epsilon : I -> Real := fun a => Classical.choose (hbounds a)
  have hepsilon_pos : forall a : I, 0 < epsilon a :=
    fun a => (Classical.choose_spec (hbounds a)).1
  have hepsilon_le : forall a : I, forall x, x ∈ K -> epsilon a <= lower a x :=
    fun a => (Classical.choose_spec (hbounds a)).2
  let delta : Real := (Finset.univ : Finset I).inf' hI_nonempty epsilon
  have hdelta_pos : 0 < delta := by
    exact (Finset.lt_inf'_iff hI_nonempty).2
      (fun a _ha => hepsilon_pos a)
  refine ⟨delta, hdelta_pos, ?_⟩
  intro x hx
  constructor
  · intro i
    exact
      (Finset.inf'_le (s := (Finset.univ : Finset I)) (f := epsilon)
        (b := (Sum.inr (Sum.inl i) : I)) (Finset.mem_univ _)).trans
      (by simpa [lower] using
        hepsilon_le (Sum.inr (Sum.inl i) : I) x hx)
  · intro i j hij
    let a : I := Sum.inr (Sum.inr ⟨(i, j), hij⟩)
    exact
      (Finset.inf'_le (s := (Finset.univ : Finset I)) (f := epsilon)
        (b := a) (Finset.mem_univ _)).trans
      (by simpa [a, lower] using hepsilon_le a x hx)

/-- One sufficiently steep axis-pair slope works on every point of a compact
ordered-positive carrier.  This is the quantifier-order form needed for a
continuous family of physical radial sources. -/
theorem exists_axisPairSlope_compact_subset_all_orientedPositive
    (d n : Nat) [NeZero d]
    (K : Set (NPointDomain d n))
    (hK_compact : IsCompact K)
    (hK_ordered : K ⊆ OrderedPositiveTimeRegion d n) :
    exists T : Real, 1 < T ∧
      forall a : osiiAxisPairIndex d,
        K ⊆ osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix := by
  obtain ⟨delta, hdelta, hmargin⟩ :=
    exists_orderedPositiveTimeRegion_margin_of_compact_subset
      d n K hK_compact hK_ordered
  obtain ⟨C0, hC0⟩ :=
    hK_compact.bddAbove_image continuous_norm.continuousOn
  let C : Real := max C0 0
  have hC : 0 <= C := le_max_right _ _
  have hnorm : forall x, x ∈ K -> ‖x‖ <= C := by
    intro x hx
    exact (hC0 (Set.mem_image_of_mem norm hx)).trans (le_max_left _ _)
  let T : Real := max 2 (2 * C / delta + 1)
  have hT : 1 < T := by
    linarith [le_max_left (2 : Real) (2 * C / delta + 1)]
  have hratio : 2 * C / delta < T := by
    linarith [le_max_right (2 : Real) (2 * C / delta + 1)]
  refine ⟨T, hT, ?_⟩
  intro a x hx
  exact
    (osiiAxisPairRotationData T a).mem_orderedPositive_of_margin_norm
      hdelta hC hratio x (hmargin hx).1 (hmargin hx).2 (hnorm x hx)

/-- A finite dependent family of compact ordered-positive carriers admits one
axis-pair slope. -/
theorem exists_common_axisPairSlope_compactCarriers
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (arity : iota -> Nat)
    (K : (i : iota) -> Set (NPointDomain d (arity i)))
    (hcompact : forall i, IsCompact (K i))
    (hordered : forall i, K i ⊆ OrderedPositiveTimeRegion d (arity i)) :
    exists T : Real, 1 < T ∧
      forall i a,
        K i ⊆ osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := arity i)
          (osiiAxisPairRotationData T a).matrix := by
  let hSlope (i : iota) :=
    exists_axisPairSlope_compact_subset_all_orientedPositive
      d (arity i) (K i) (hcompact i) (hordered i)
  let slope : iota -> Real := fun i => Classical.choose (hSlope i)
  let T : Real := max 2
    (Finset.univ.sup' Finset.univ_nonempty slope)
  have hT : 1 < T := by
    have htwo : (2 : Real) <= T := le_max_left _ _
    linarith
  refine ⟨T, hT, ?_⟩
  intro i a
  have hslope : slope i <= T :=
    (Finset.le_sup' slope (Finset.mem_univ i)).trans
      (le_max_right _ _)
  have hslope_pos : 0 < slope i := by
    have hone : 1 < slope i := (Classical.choose_spec (hSlope i)).1
    linarith
  exact subset_all_orientedPositive_mono
    (K i) hslope_pos hslope (Classical.choose_spec (hSlope i)).2 a

/-- Two finite dependent carrier families admit one shared axis-pair slope. -/
theorem exists_common_axisPairSlope_twoCompactCarrierFamilies
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (leftArity rightArity : iota -> Nat)
    (left : (i : iota) -> Set (NPointDomain d (leftArity i)))
    (right : (i : iota) -> Set (NPointDomain d (rightArity i)))
    (hleftCompact : forall i, IsCompact (left i))
    (hrightCompact : forall i, IsCompact (right i))
    (hleftOrdered : forall i,
      left i ⊆ OrderedPositiveTimeRegion d (leftArity i))
    (hrightOrdered : forall i,
      right i ⊆ OrderedPositiveTimeRegion d (rightArity i)) :
    exists T : Real, 1 < T ∧
      (forall i a,
        left i ⊆ osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := leftArity i)
          (osiiAxisPairRotationData T a).matrix) ∧
      forall i a,
        right i ⊆ osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := rightArity i)
          (osiiAxisPairRotationData T a).matrix := by
  obtain ⟨TL, hTL, hleft⟩ :=
    exists_common_axisPairSlope_compactCarriers
      leftArity left hleftCompact hleftOrdered
  obtain ⟨TR, hTR, hright⟩ :=
    exists_common_axisPairSlope_compactCarriers
      rightArity right hrightCompact hrightOrdered
  let T := max TL TR
  have hT : 1 < T := hTL.trans_le (le_max_left _ _)
  refine ⟨T, hT, ?_, ?_⟩
  · intro i a
    exact subset_all_orientedPositive_mono
      (left i) (by linarith) (le_max_left _ _) (hleft i) a
  · intro i a
    exact subset_all_orientedPositive_mono
      (right i) (by linarith) (le_max_right _ _) (hright i) a

/-- Build the ordinary compact common-source package at an already chosen
slope.  This lets the radial chart estimate be reused after the finite
common-slope construction. -/
def OSIIAxisPairCompactCommonSourcePackage.ofCommonSlope
    (leftPositive : SchwartzNPoint d n)
    (right : SchwartzNPoint d m)
    (T : Real) (hT : 1 < T)
    (hleftCompact :
      HasCompactSupport (leftPositive : NPointDomain d n -> Complex))
    (hrightCompact :
      HasCompactSupport (right : NPointDomain d m -> Complex))
    (hleft : forall a,
      tsupport (leftPositive : NPointDomain d n -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (hright : forall a,
      tsupport (right : NPointDomain d m -> Complex) <=
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    OSIIAxisPairCompactCommonSourcePackage leftPositive right where
  T := T
  hT := hT
  left_compact := hleftCompact
  right_compact := hrightCompact
  data := {
    left := leftPositive.timeReflect
    left_support :=
      SchwartzNPoint.timeReflect_tsupport_subset_all_orientedNegative
        leftPositive hleft
    right := right
    right_support := hright }
  left_eq := rfl
  right_eq := rfl

end OSReconstruction
