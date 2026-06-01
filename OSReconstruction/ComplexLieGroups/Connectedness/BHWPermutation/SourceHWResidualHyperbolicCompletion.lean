import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWResidualFrameExtension

/-!
# Hyperbolic completion data for residual isotropic subspaces

This file supplies the finite basis frame plus isotropic dual frame needed by
the remaining residual hyperbolic block construction.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- A complex-spacetime submodule whose finrank is not strictly below the
ambient finrank is the whole ambient subspace. -/
theorem complexMinkowski_submodule_eq_top_of_not_finrank_lt_spacetime
    {d : ℕ}
    {L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hnot : ¬ Module.finrank ℂ L < d + 1) :
    L = ⊤ := by
  by_contra hne
  have hlt :
      Module.finrank ℂ L <
        Module.finrank ℂ (Fin (d + 1) → ℂ) :=
    Submodule.finrank_lt hne
  have hamb : Module.finrank ℂ (Fin (d + 1) → ℂ) = d + 1 := by
    simp
  exact hnot (by simpa [hamb] using hlt)

/-- If a subspace is linearly equivalent to a full complex-spacetime subspace,
then it is full as well. -/
theorem complexMinkowski_submodule_eq_top_of_linearEquiv_full
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (T : K ≃ₗ[ℂ] L)
    (hLtop : L = ⊤) :
    K = ⊤ := by
  apply complexMinkowski_submodule_eq_top_of_not_finrank_lt_spacetime
    (d := d) (L := K)
  intro hKproper
  have hfinKL : Module.finrank ℂ K = Module.finrank ℂ L :=
    T.finrank_eq
  have hfinL : Module.finrank ℂ L = d + 1 := by
    rw [hLtop]
    simp
  have hfinK : Module.finrank ℂ K = d + 1 := by
    rw [hfinKL, hfinL]
  omega

/-- Apply independent linear equivalences between two pairs of complementary
summands inside their respective suprema. -/
noncomputable def directSum_congr_sup_equiv_between
    {d : ℕ}
    {A B C D : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hAB : Disjoint A B)
    (hCD : Disjoint C D)
    (EA : A ≃ₗ[ℂ] C) (EB : B ≃ₗ[ℂ] D) :
    ↥(A ⊔ B) ≃ₗ[ℂ] ↥(C ⊔ D) := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) := A ⊔ B
  let T : Submodule ℂ (Fin (d + 1) → ℂ) := C ⊔ D
  let As : Submodule ℂ S := A.comap S.subtype
  let Bs : Submodule ℂ S := B.comap S.subtype
  let Cs : Submodule ℂ T := C.comap T.subtype
  let Ds : Submodule ℂ T := D.comap T.subtype
  have hABcompl : IsCompl As Bs := by
    simpa [S, As, Bs] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := A) (R := B) hAB
  have hCDcompl : IsCompl Cs Ds := by
    simpa [T, Cs, Ds] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := C) (R := D) hCD
  let eA : As ≃ₗ[ℂ] A :=
    Submodule.comapSubtypeEquivOfLe (show A ≤ S from le_sup_left)
  let eB : Bs ≃ₗ[ℂ] B :=
    Submodule.comapSubtypeEquivOfLe (show B ≤ S from le_sup_right)
  let eC : Cs ≃ₗ[ℂ] C :=
    Submodule.comapSubtypeEquivOfLe (show C ≤ T from le_sup_left)
  let eD : Ds ≃ₗ[ℂ] D :=
    Submodule.comapSubtypeEquivOfLe (show D ≤ T from le_sup_right)
  let EA' : As ≃ₗ[ℂ] Cs := eA.trans (EA.trans eC.symm)
  let EB' : Bs ≃ₗ[ℂ] Ds := eB.trans (EB.trans eD.symm)
  exact (Submodule.prodEquivOfIsCompl As Bs hABcompl).symm.trans
    ((EA'.prodCongr EB').trans
      (Submodule.prodEquivOfIsCompl Cs Ds hCDcompl))

/-- If `x = a + b`, the between-supremum direct-sum congruence sends `x` to
`EA a + EB b`. -/
theorem directSum_congr_sup_equiv_between_apply_of_eq_add
    {d : ℕ}
    {A B C D : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hAB : Disjoint A B)
    (hCD : Disjoint C D)
    (EA : A ≃ₗ[ℂ] C) (EB : B ≃ₗ[ℂ] D)
    {x : ↥(A ⊔ B)} {a : A} {b : B}
    (hx : (a : Fin (d + 1) → ℂ) + (b : Fin (d + 1) → ℂ) =
      (x : Fin (d + 1) → ℂ)) :
    ((directSum_congr_sup_equiv_between (d := d) (A := A) (B := B)
        (C := C) (D := D) hAB hCD EA EB x : ↥(C ⊔ D)) :
        Fin (d + 1) → ℂ) =
      (EA a : Fin (d + 1) → ℂ) + (EB b : Fin (d + 1) → ℂ) := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) := A ⊔ B
  let T : Submodule ℂ (Fin (d + 1) → ℂ) := C ⊔ D
  let As : Submodule ℂ S := A.comap S.subtype
  let Bs : Submodule ℂ S := B.comap S.subtype
  let Cs : Submodule ℂ T := C.comap T.subtype
  let Ds : Submodule ℂ T := D.comap T.subtype
  have hABcompl : IsCompl As Bs := by
    simpa [S, As, Bs] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := A) (R := B) hAB
  have hCDcompl : IsCompl Cs Ds := by
    simpa [T, Cs, Ds] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := C) (R := D) hCD
  let eA : As ≃ₗ[ℂ] A :=
    Submodule.comapSubtypeEquivOfLe (show A ≤ S from le_sup_left)
  let eB : Bs ≃ₗ[ℂ] B :=
    Submodule.comapSubtypeEquivOfLe (show B ≤ S from le_sup_right)
  let eC : Cs ≃ₗ[ℂ] C :=
    Submodule.comapSubtypeEquivOfLe (show C ≤ T from le_sup_left)
  let eD : Ds ≃ₗ[ℂ] D :=
    Submodule.comapSubtypeEquivOfLe (show D ≤ T from le_sup_right)
  let EA' : As ≃ₗ[ℂ] Cs := eA.trans (EA.trans eC.symm)
  let EB' : Bs ≃ₗ[ℂ] Ds := eB.trans (EB.trans eD.symm)
  let Esrc : (As × Bs) ≃ₗ[ℂ] S :=
    Submodule.prodEquivOfIsCompl As Bs hABcompl
  let Etgt : (Cs × Ds) ≃ₗ[ℂ] T :=
    Submodule.prodEquivOfIsCompl Cs Ds hCDcompl
  let Tsum : S ≃ₗ[ℂ] T :=
    Esrc.symm.trans ((EA'.prodCongr EB').trans Etgt)
  have hTdef :
      directSum_congr_sup_equiv_between (d := d) (A := A) (B := B)
        (C := C) (D := D) hAB hCD EA EB = Tsum := by
    rfl
  rw [hTdef]
  let y : S := x
  let xA : ↥(A ⊔ B) :=
    ⟨(a : Fin (d + 1) → ℂ), Submodule.mem_sup_left a.2⟩
  let xB : ↥(A ⊔ B) :=
    ⟨(b : Fin (d + 1) → ℂ), Submodule.mem_sup_right b.2⟩
  let xa : As := ⟨xA, a.2⟩
  let xb : Bs := ⟨xB, b.2⟩
  have hsymm : Esrc.symm y = (xa, xb) := by
    refine Esrc.symm_apply_eq.2 ?_
    apply Subtype.ext
    simpa [Esrc, y, xa, xb, xA, xB] using hx.symm
  calc
    ((Tsum y : T) : Fin (d + 1) → ℂ)
        = ((EA' xa : Cs) : T) + ((EB' xb : Ds) : T) := by
            change ((((Submodule.prodEquivOfIsCompl As Bs hABcompl).symm.trans
              (((EA'.prodCongr EB').trans
                (Submodule.prodEquivOfIsCompl Cs Ds hCDcompl)))) y : T) :
                Fin (d + 1) → ℂ) =
              ((EA' xa : Cs) : T) + ((EB' xb : Ds) : T)
            rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hsymm]
            rfl
    _ = (EA a : Fin (d + 1) → ℂ) +
          (EB b : Fin (d + 1) → ℂ) := by
            change ((EA a : C) : Fin (d + 1) → ℂ) +
                ((EB b : D) : Fin (d + 1) → ℂ) =
              (EA a : Fin (d + 1) → ℂ) +
                (EB b : Fin (d + 1) → ℂ)
            rfl

/-- Canonical equivalence between the spans of two linearly independent
families with the same index type, obtained by transporting through coefficient
Finsupps. -/
noncomputable def linearEquiv_spanOfLinearIndependentFrames
    {ι V : Type*}
    [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    {v w : ι → V}
    (hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w) :
    Submodule.span ℂ (Set.range v) ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range w) :=
  hv.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv

/-- The canonical span equivalence sends each source frame vector to the
matching target frame vector. -/
theorem linearEquiv_spanOfLinearIndependentFrames_apply
    {ι V : Type*}
    [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    {v w : ι → V}
    (hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w)
    (i : ι) :
    ((linearEquiv_spanOfLinearIndependentFrames hv hw
      ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ :
        Submodule.span ℂ (Set.range w)) : V) = w i := by
  let x : Submodule.span ℂ (Set.range v) :=
    ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hx : hv.repr x = Finsupp.single i 1 := hv.repr_eq_single i x rfl
  change ((hw.linearCombinationEquiv (hv.repr x) :
    Submodule.span ℂ (Set.range w)) : V) = w i
  rw [hx]
  simp [LinearIndependent.linearCombinationEquiv_apply_coe,
    Finsupp.linearCombination_single]

/-- On totally isotropic source and target frame spans, the canonical span
equivalence preserves the complex Minkowski pairing. -/
theorem linearEquiv_spanOfLinearIndependentFrames_preserves_isotropic
    {d s : ℕ}
    {v w : Fin s → Fin (d + 1) → ℂ}
    (hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w)
    (hv_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (v c) (v c') = 0)
    (hw_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (w c) (w c') = 0) :
    let E := linearEquiv_spanOfLinearIndependentFrames hv hw
    ∀ x y : Submodule.span ℂ (Set.range v),
      sourceComplexMinkowskiInner d
        ((E x : Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ)
        ((E y : Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro E x y
  have hv_iso :
      ComplexMinkowskiTotallyIsotropicSubspace d
        (Submodule.span ℂ (Set.range v)) :=
    complexMinkowskiTotallyIsotropic_span_range d s v hv_pair_zero
  have hw_iso :
      ComplexMinkowskiTotallyIsotropicSubspace d
        (Submodule.span ℂ (Set.range w)) :=
    complexMinkowskiTotallyIsotropic_span_range d s w hw_pair_zero
  rw [hw_iso (E x) (E y), hv_iso x y]

/-- The canonical span equivalences for two dual frame pairs preserve the
cross pairing between the frame span and the dual-frame span. -/
theorem linearEquiv_spanOfLinearIndependentFrames_preserves_dual_pairing
    {d s : ℕ}
    {v vDual w wDual : Fin s → Fin (d + 1) → ℂ}
    (hv : LinearIndependent ℂ v)
    (hvDual : LinearIndependent ℂ vDual)
    (hw : LinearIndependent ℂ w)
    (hwDual : LinearIndependent ℂ wDual)
    (hdual_v :
      ∀ c c',
        sourceComplexMinkowskiInner d (v c) (vDual c') =
          if c = c' then (1 : ℂ) else 0)
    (hdual_w :
      ∀ c c',
        sourceComplexMinkowskiInner d (w c) (wDual c') =
          if c = c' then (1 : ℂ) else 0) :
    let E := linearEquiv_spanOfLinearIndependentFrames hv hw
    let EDual := linearEquiv_spanOfLinearIndependentFrames hvDual hwDual
    ∀ x : Submodule.span ℂ (Set.range v),
    ∀ y : Submodule.span ℂ (Set.range vDual),
      sourceComplexMinkowskiInner d
        ((E x : Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ)
        ((EDual y : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro E EDual x y
  let p : (a : Fin (d + 1) → ℂ) → (b : Fin (d + 1) → ℂ) →
      a ∈ Submodule.span ℂ (Set.range v) →
      b ∈ Submodule.span ℂ (Set.range vDual) → Prop :=
    fun a b ha hb =>
      sourceComplexMinkowskiInner d
        ((E ⟨a, ha⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ)
        ((EDual ⟨b, hb⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d a b
  change p (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) x.2 y.2
  apply Submodule.span_induction₂
    (R := ℂ) (s := Set.range v) (t := Set.range vDual) (p := p)
  · intro a b ha hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    dsimp [p]
    rw [linearEquiv_spanOfLinearIndependentFrames_apply hv hw i,
      linearEquiv_spanOfLinearIndependentFrames_apply hvDual hwDual j,
      hdual_w, hdual_v]
  · intro b hb
    dsimp [p]
    have hE_zero :
        ((E ⟨0, Submodule.zero_mem _⟩ :
          Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) = 0 := by
      simp
    rw [hE_zero]
    simp [sourceComplexMinkowskiInner]
  · intro a ha
    dsimp [p]
    have hEDual_zero :
        ((EDual ⟨0, Submodule.zero_mem _⟩ :
          Submodule.span ℂ (Set.range wDual)) : Fin (d + 1) → ℂ) = 0 := by
      simp
    rw [hEDual_zero]
    simp [sourceComplexMinkowskiInner]
  · intro a b c ha hb hc hpa hpb
    dsimp [p] at hpa hpb ⊢
    have hE_add :
        ((E ⟨a + b, Submodule.add_mem _ ha hb⟩ :
          Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) =
        ((E ⟨a, ha⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ) +
        ((E ⟨b, hb⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range w) =>
          (z : Fin (d + 1) → ℂ))
        (map_add E ⟨a, ha⟩ ⟨b, hb⟩)
      simpa using h
    rw [hE_add, sourceComplexMinkowskiInner_add_left,
      sourceComplexMinkowskiInner_add_left]
    rw [hpa, hpb]
  · intro a b c ha hb hc hpab hpac
    dsimp [p] at hpab hpac ⊢
    have hEDual_add :
        ((EDual ⟨b + c, Submodule.add_mem _ hb hc⟩ :
          Submodule.span ℂ (Set.range wDual)) : Fin (d + 1) → ℂ) =
        ((EDual ⟨b, hb⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) +
        ((EDual ⟨c, hc⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range wDual) =>
          (z : Fin (d + 1) → ℂ))
        (map_add EDual ⟨b, hb⟩ ⟨c, hc⟩)
      simpa using h
    rw [hEDual_add, sourceComplexMinkowskiInner_add_right,
      sourceComplexMinkowskiInner_add_right]
    rw [hpab, hpac]
  · intro r a b ha hb hp
    dsimp [p] at hp ⊢
    have hE_smul :
        ((E ⟨r • a, Submodule.smul_mem _ r ha⟩ :
          Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) =
        r • ((E ⟨a, ha⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range w) =>
          (z : Fin (d + 1) → ℂ))
        (map_smul E r ⟨a, ha⟩)
      simpa using h
    rw [hE_smul, sourceComplexMinkowskiInner_smul_left,
      sourceComplexMinkowskiInner_smul_left]
    rw [hp]
  · intro r a b ha hb hp
    dsimp [p] at hp ⊢
    have hEDual_smul :
        ((EDual ⟨r • b, Submodule.smul_mem _ r hb⟩ :
          Submodule.span ℂ (Set.range wDual)) : Fin (d + 1) → ℂ) =
        r • ((EDual ⟨b, hb⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range wDual) =>
          (z : Fin (d + 1) → ℂ))
        (map_smul EDual r ⟨b, hb⟩)
      simpa using h
    rw [hEDual_smul, sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_smul_right]
    rw [hp]

/-- The canonical equivalence between two hyperbolic frame spans, sending each
frame vector and each dual-frame vector to its target counterpart. -/
noncomputable def complexMinkowski_hyperbolicFrameSpanEquiv_between
    {d s : ℕ}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    ↥(Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)) ≃ₗ[ℂ]
    ↥(Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual)) := by
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  let P : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p)
  let Pd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range pDual)
  have hQdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hq_dual
  have hPdisj : Disjoint P Pd := by
    simpa [P, Pd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := p) (qDual := pDual)
        hpDual_pair_zero hp_dual
  let Eq : Q ≃ₗ[ℂ] P :=
    linearEquiv_spanOfLinearIndependentFrames
      (complexMinkowski_dualPair_linearIndependent_left
        (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
      (complexMinkowski_dualPair_linearIndependent_left
        (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
  let Eqd : Qd ≃ₗ[ℂ] Pd :=
    linearEquiv_spanOfLinearIndependentFrames
      (complexMinkowski_dualPair_linearIndependent_right
        (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
      (complexMinkowski_dualPair_linearIndependent_right
        (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
  exact directSum_congr_sup_equiv_between
    (d := d) (A := Q) (B := Qd) (C := P) (D := Pd)
    hQdisj hPdisj Eq Eqd

/-- The hyperbolic-span equivalence preserves the full Minkowski pairing. -/
theorem complexMinkowski_hyperbolicFrameSpanEquiv_between_preserves
    {d s : ℕ}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hp_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (p c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    let E := complexMinkowski_hyperbolicFrameSpanEquiv_between
      (d := d) (s := s) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
    ∀ x y : ↥(Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)),
      sourceComplexMinkowskiInner d
        ((E x : ↥(Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual))) : Fin (d + 1) → ℂ)
        ((E y : ↥(Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual))) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro E x y
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  let P : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p)
  let Pd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range pDual)
  have hQdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hq_dual
  have hPdisj : Disjoint P Pd := by
    simpa [P, Pd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := p) (qDual := pDual)
        hpDual_pair_zero hp_dual
  let Eq : Q ≃ₗ[ℂ] P :=
    linearEquiv_spanOfLinearIndependentFrames
      (complexMinkowski_dualPair_linearIndependent_left
        (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
      (complexMinkowski_dualPair_linearIndependent_left
        (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
  let Eqd : Qd ≃ₗ[ℂ] Pd :=
    linearEquiv_spanOfLinearIndependentFrames
      (complexMinkowski_dualPair_linearIndependent_right
        (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
      (complexMinkowski_dualPair_linearIndependent_right
        (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
  have hE_def :
      E = directSum_congr_sup_equiv_between
        (d := d) (A := Q) (B := Qd) (C := P) (D := Pd)
        hQdisj hPdisj Eq Eqd := by
    rfl
  rcases Submodule.mem_sup.mp x.2 with ⟨qx, hqx, qdx, hqdx, hxsum⟩
  rcases Submodule.mem_sup.mp y.2 with ⟨qy, hqy, qdy, hqdy, hysum⟩
  let qxQ : Q := ⟨qx, by simpa [Q] using hqx⟩
  let qdxQd : Qd := ⟨qdx, by simpa [Qd] using hqdx⟩
  let qyQ : Q := ⟨qy, by simpa [Q] using hqy⟩
  let qdyQd : Qd := ⟨qdy, by simpa [Qd] using hqdy⟩
  have hEx :
      ((E x : ↥(Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual))) : Fin (d + 1) → ℂ) =
        (Eq qxQ : Fin (d + 1) → ℂ) +
          (Eqd qdxQd : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    simpa [Q, Qd, P, Pd, qxQ, qdxQd] using
      directSum_congr_sup_equiv_between_apply_of_eq_add
        (d := d) (A := Q) (B := Qd) (C := P) (D := Pd)
        hQdisj hPdisj Eq Eqd (x := x) (a := qxQ) (b := qdxQd)
        (by simpa [qxQ, qdxQd] using hxsum)
  have hEy :
      ((E y : ↥(Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual))) : Fin (d + 1) → ℂ) =
        (Eq qyQ : Fin (d + 1) → ℂ) +
          (Eqd qdyQd : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    simpa [Q, Qd, P, Pd, qyQ, qdyQd] using
      directSum_congr_sup_equiv_between_apply_of_eq_add
        (d := d) (A := Q) (B := Qd) (C := P) (D := Pd)
        hQdisj hPdisj Eq Eqd (x := y) (a := qyQ) (b := qdyQd)
        (by simpa [qyQ, qdyQd] using hysum)
  have hQQ :
      sourceComplexMinkowskiInner d
        (Eq qxQ : Fin (d + 1) → ℂ)
        (Eq qyQ : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d qx qy := by
    simpa [Q, P, Eq, qxQ, qyQ] using
      linearEquiv_spanOfLinearIndependentFrames_preserves_isotropic
        (d := d) (s := s)
        (v := q) (w := p)
        (complexMinkowski_dualPair_linearIndependent_left
          (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
        (complexMinkowski_dualPair_linearIndependent_left
          (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
        hq_pair_zero hp_pair_zero qxQ qyQ
  have hQdQd :
      sourceComplexMinkowskiInner d
        (Eqd qdxQd : Fin (d + 1) → ℂ)
        (Eqd qdyQd : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d qdx qdy := by
    simpa [Qd, Pd, Eqd, qdxQd, qdyQd] using
      linearEquiv_spanOfLinearIndependentFrames_preserves_isotropic
        (d := d) (s := s)
        (v := qDual) (w := pDual)
        (complexMinkowski_dualPair_linearIndependent_right
          (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
        (complexMinkowski_dualPair_linearIndependent_right
          (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
        hqDual_pair_zero hpDual_pair_zero qdxQd qdyQd
  have hQQd :
      sourceComplexMinkowskiInner d
        (Eq qxQ : Fin (d + 1) → ℂ)
        (Eqd qdyQd : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d qx qdy := by
    simpa [Q, Qd, P, Pd, Eq, Eqd, qxQ, qdyQd] using
      linearEquiv_spanOfLinearIndependentFrames_preserves_dual_pairing
        (d := d) (s := s)
        (v := q) (vDual := qDual) (w := p) (wDual := pDual)
        (complexMinkowski_dualPair_linearIndependent_left
          (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
        (complexMinkowski_dualPair_linearIndependent_right
          (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
        (complexMinkowski_dualPair_linearIndependent_left
          (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
        (complexMinkowski_dualPair_linearIndependent_right
          (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
        hq_dual hp_dual qxQ qdyQd
  have hQdQ :
      sourceComplexMinkowskiInner d
        (Eqd qdxQd : Fin (d + 1) → ℂ)
        (Eq qyQ : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d qdx qy := by
    rw [sourceComplexMinkowskiInner_comm d
      (Eqd qdxQd : Fin (d + 1) → ℂ)
      (Eq qyQ : Fin (d + 1) → ℂ)]
    rw [sourceComplexMinkowskiInner_comm d qdx qy]
    simpa [Q, Qd, P, Pd, Eq, Eqd, qyQ, qdxQd] using
      linearEquiv_spanOfLinearIndependentFrames_preserves_dual_pairing
        (d := d) (s := s)
        (v := q) (vDual := qDual) (w := p) (wDual := pDual)
        (complexMinkowski_dualPair_linearIndependent_left
          (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
        (complexMinkowski_dualPair_linearIndependent_right
          (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
        (complexMinkowski_dualPair_linearIndependent_left
          (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
        (complexMinkowski_dualPair_linearIndependent_right
          (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
        hq_dual hp_dual qyQ qdxQd
  rw [hEx, hEy,
    show (x : Fin (d + 1) → ℂ) = qx + qdx from hxsum.symm,
    show (y : Fin (d + 1) → ℂ) = qy + qdy from hysum.symm]
  simp [sourceComplexMinkowskiInner_add_left,
    sourceComplexMinkowskiInner_add_right,
    hQQ, hQdQd, hQQd, hQdQ]

/-- The hyperbolic-span equivalence sends the source frame span into the target
frame span. -/
theorem complexMinkowski_hyperbolicFrameSpanEquiv_between_maps_left_span
    {d s : ℕ}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    let E := complexMinkowski_hyperbolicFrameSpanEquiv_between
      (d := d) (s := s) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
    ∀ x : Submodule.span ℂ (Set.range q),
      ((E ⟨(x : Fin (d + 1) → ℂ),
          Submodule.mem_sup_left x.2⟩ :
        ↥(Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual))) :
          Fin (d + 1) → ℂ) ∈
      Submodule.span ℂ (Set.range p) := by
  intro E x
  let Q : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q)
  let Qd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range qDual)
  let P : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p)
  let Pd : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range pDual)
  have hQdisj : Disjoint Q Qd := by
    simpa [Q, Qd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := q) (qDual := qDual)
        hqDual_pair_zero hq_dual
  have hPdisj : Disjoint P Pd := by
    simpa [P, Pd] using
      complexMinkowski_span_frame_disjoint_dualFrame
        (d := d) (s := s) (q := p) (qDual := pDual)
        hpDual_pair_zero hp_dual
  let Eq : Q ≃ₗ[ℂ] P :=
    linearEquiv_spanOfLinearIndependentFrames
      (complexMinkowski_dualPair_linearIndependent_left
        (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
      (complexMinkowski_dualPair_linearIndependent_left
        (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
  let Eqd : Qd ≃ₗ[ℂ] Pd :=
    linearEquiv_spanOfLinearIndependentFrames
      (complexMinkowski_dualPair_linearIndependent_right
        (d := d) (s := s) (q := q) (qDual := qDual) hq_dual)
      (complexMinkowski_dualPair_linearIndependent_right
        (d := d) (s := s) (q := p) (qDual := pDual) hp_dual)
  have hE_def :
      E = directSum_congr_sup_equiv_between
        (d := d) (A := Q) (B := Qd) (C := P) (D := Pd)
        hQdisj hPdisj Eq Eqd := by
    rfl
  let xQ : Q := ⟨(x : Fin (d + 1) → ℂ), by simp [Q, x.2]⟩
  let z : ↥(Q ⊔ Qd) :=
    ⟨(x : Fin (d + 1) → ℂ), Submodule.mem_sup_left xQ.2⟩
  have hz :
      ((E z : ↥(Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual))) : Fin (d + 1) → ℂ) =
        (Eq xQ : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    have h := directSum_congr_sup_equiv_between_apply_of_eq_add
      (d := d) (A := Q) (B := Qd) (C := P) (D := Pd)
      hQdisj hPdisj Eq Eqd (x := z) (a := xQ)
      (b := (0 : Qd)) (by simp [z, xQ])
    simpa [P, Pd, z, xQ] using h
  have htarget : (Eq xQ : Fin (d + 1) → ℂ) ∈
      Submodule.span ℂ (Set.range p) := by
    simp [P, (Eq xQ).2]
  simpa [Q, Qd, P, Pd, xQ, z] using hz.symm ▸ htarget

/-- The selected-block identity combined with the hyperbolic frame-span
equivalence between source and target residual completions. -/
noncomputable def complexMinkowski_selectedHyperbolicBlockEquiv_between
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hq_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (qDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hp_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (p c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hpDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (pDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    ↥(M ⊔ (Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual))) ≃ₗ[ℂ]
    ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual))) := by
  let Hq : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)
  let Hp : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual)
  have hM_Hq : Disjoint M Hq := by
    simpa [Hq] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
        hM hq_orth_M hqDual_orth_M
  have hM_Hp : Disjoint M Hp := by
    simpa [Hp] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
        hM hp_orth_M hpDual_orth_M
  let EH : Hq ≃ₗ[ℂ] Hp :=
    complexMinkowski_hyperbolicFrameSpanEquiv_between
      (d := d) (s := s) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
  exact directSum_congr_sup_equiv_between
    (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
    hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH

/-- The selected-hyperbolic block equivalence preserves the full Minkowski
pairing. -/
theorem complexMinkowski_selectedHyperbolicBlockEquiv_between_preserves
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hq_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (qDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hp_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (p c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hpDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (pDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hp_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (p c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    let E := complexMinkowski_selectedHyperbolicBlockEquiv_between
      (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual) hM hq_orth_M hqDual_orth_M
      hp_orth_M hpDual_orth_M hqDual_pair_zero hpDual_pair_zero
      hq_dual hp_dual
    ∀ x y : ↥(M ⊔ (Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual))),
      sourceComplexMinkowskiInner d
        ((E x : ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual)))) : Fin (d + 1) → ℂ)
        ((E y : ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual)))) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro E x y
  let Hq : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)
  let Hp : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual)
  have hM_Hq : Disjoint M Hq := by
    simpa [Hq] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
        hM hq_orth_M hqDual_orth_M
  have hM_Hp : Disjoint M Hp := by
    simpa [Hp] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
        hM hp_orth_M hpDual_orth_M
  let EH : Hq ≃ₗ[ℂ] Hp :=
    complexMinkowski_hyperbolicFrameSpanEquiv_between
      (d := d) (s := s) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
  have hE_def :
      E = directSum_congr_sup_equiv_between
        (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
        hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH := by
    rfl
  rcases Submodule.mem_sup.mp x.2 with ⟨mx, hmx, hxH, hhxH, hxsum⟩
  rcases Submodule.mem_sup.mp y.2 with ⟨my, hmy, hyH, hhyH, hysum⟩
  let mxM : M := ⟨mx, hmx⟩
  let myM : M := ⟨my, hmy⟩
  let hxHq : Hq := ⟨hxH, by simpa [Hq] using hhxH⟩
  let hyHq : Hq := ⟨hyH, by simpa [Hq] using hhyH⟩
  have hEx :
      ((E x : ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual)))) : Fin (d + 1) → ℂ) =
        (mxM : Fin (d + 1) → ℂ) + (EH hxHq : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    simpa [Hq, Hp, mxM, hxHq] using
      directSum_congr_sup_equiv_between_apply_of_eq_add
        (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
        hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH
        (x := x) (a := mxM) (b := hxHq)
        (by simpa [mxM, hxHq] using hxsum)
  have hEy :
      ((E y : ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual)))) : Fin (d + 1) → ℂ) =
        (myM : Fin (d + 1) → ℂ) + (EH hyHq : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    simpa [Hq, Hp, myM, hyHq] using
      directSum_congr_sup_equiv_between_apply_of_eq_add
        (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
        hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH
        (x := y) (a := myM) (b := hyHq)
        (by simpa [myM, hyHq] using hysum)
  have hHH :
      sourceComplexMinkowskiInner d
        (EH hxHq : Fin (d + 1) → ℂ)
        (EH hyHq : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d hxH hyH := by
    simpa [Hq, Hp, EH, hxHq, hyHq] using
      complexMinkowski_hyperbolicFrameSpanEquiv_between_preserves
        (d := d) (s := s) (q := q) (qDual := qDual)
        (p := p) (pDual := pDual) hq_pair_zero hqDual_pair_zero
        hp_pair_zero hpDual_pair_zero hq_dual hp_dual hxHq hyHq
  have hHx_My :
      sourceComplexMinkowskiInner d hxH (myM : Fin (d + 1) → ℂ) = 0 := by
    exact complexMinkowski_hyperbolicFrameSpan_orthogonal_selected
      (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
      hq_orth_M hqDual_orth_M hxHq myM
  have hHy_Mx :
      sourceComplexMinkowskiInner d hyH (mxM : Fin (d + 1) → ℂ) = 0 := by
    exact complexMinkowski_hyperbolicFrameSpan_orthogonal_selected
      (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
      hq_orth_M hqDual_orth_M hyHq mxM
  have hEHx_My :
      sourceComplexMinkowskiInner d
        (EH hxHq : Fin (d + 1) → ℂ) (myM : Fin (d + 1) → ℂ) = 0 := by
    exact complexMinkowski_hyperbolicFrameSpan_orthogonal_selected
      (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
      hp_orth_M hpDual_orth_M (EH hxHq) myM
  have hEHy_Mx :
      sourceComplexMinkowskiInner d
        (EH hyHq : Fin (d + 1) → ℂ) (mxM : Fin (d + 1) → ℂ) = 0 := by
    exact complexMinkowski_hyperbolicFrameSpan_orthogonal_selected
      (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
      hp_orth_M hpDual_orth_M (EH hyHq) mxM
  rw [hEx, hEy,
    show (x : Fin (d + 1) → ℂ) = mx + hxH from hxsum.symm,
    show (y : Fin (d + 1) → ℂ) = my + hyH from hysum.symm]
  have hHx_my : sourceComplexMinkowskiInner d hxH my = 0 := by
    simpa [myM] using hHx_My
  have hHy_mx : sourceComplexMinkowskiInner d hyH mx = 0 := by
    simpa [mxM] using hHy_Mx
  simp [sourceComplexMinkowskiInner_add_left,
    sourceComplexMinkowskiInner_add_right,
    sourceComplexMinkowskiInner_comm d (mxM : Fin (d + 1) → ℂ)
      (EH hyHq : Fin (d + 1) → ℂ),
    sourceComplexMinkowskiInner_comm d mx hyH,
    hHH, hHx_my, hHy_mx, hEHx_My, hEHy_Mx, mxM, myM]

/-- The selected-hyperbolic block equivalence fixes the selected block. -/
theorem complexMinkowski_selectedHyperbolicBlockEquiv_between_maps_M
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hq_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (qDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hp_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (p c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hpDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (pDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    let E := complexMinkowski_selectedHyperbolicBlockEquiv_between
      (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual) hM hq_orth_M hqDual_orth_M
      hp_orth_M hpDual_orth_M hqDual_pair_zero hpDual_pair_zero
      hq_dual hp_dual
    ∀ m : M,
      ((E ⟨(m : Fin (d + 1) → ℂ), Submodule.mem_sup_left m.2⟩ :
        ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual)))) :
          Fin (d + 1) → ℂ) =
      (m : Fin (d + 1) → ℂ) := by
  intro E m
  let Hq : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)
  let Hp : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual)
  have hM_Hq : Disjoint M Hq := by
    simpa [Hq] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
        hM hq_orth_M hqDual_orth_M
  have hM_Hp : Disjoint M Hp := by
    simpa [Hp] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
        hM hp_orth_M hpDual_orth_M
  let EH : Hq ≃ₗ[ℂ] Hp :=
    complexMinkowski_hyperbolicFrameSpanEquiv_between
      (d := d) (s := s) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
  have hE_def :
      E = directSum_congr_sup_equiv_between
        (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
        hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH := by
    rfl
  let z : ↥(M ⊔ Hq) :=
    ⟨(m : Fin (d + 1) → ℂ), Submodule.mem_sup_left m.2⟩
  have hz :
      ((E z : ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual)))) : Fin (d + 1) → ℂ) =
        (m : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    have h := directSum_congr_sup_equiv_between_apply_of_eq_add
      (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
      hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH
      (x := z) (a := m) (b := (0 : Hq)) (by simp [z])
    simpa [Hq, Hp, z] using h
  simpa [Hq, z] using hz

/-- The selected-hyperbolic block equivalence sends the source residual frame
span into the target residual frame span. -/
theorem complexMinkowski_selectedHyperbolicBlockEquiv_between_maps_left_span
    {d s : ℕ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hq_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (qDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hp_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (p c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hpDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (pDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0) :
    let E := complexMinkowski_selectedHyperbolicBlockEquiv_between
      (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual) hM hq_orth_M hqDual_orth_M
      hp_orth_M hpDual_orth_M hqDual_pair_zero hpDual_pair_zero
      hq_dual hp_dual
    ∀ x : Submodule.span ℂ (Set.range q),
      ((E ⟨(x : Fin (d + 1) → ℂ),
          Submodule.mem_sup_right (Submodule.mem_sup_left x.2)⟩ :
        ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual)))) :
          Fin (d + 1) → ℂ) ∈
      Submodule.span ℂ (Set.range p) := by
  intro E x
  let Hq : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual)
  let Hp : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual)
  have hM_Hq : Disjoint M Hq := by
    simpa [Hq] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
        hM hq_orth_M hqDual_orth_M
  have hM_Hp : Disjoint M Hp := by
    simpa [Hp] using
      complexMinkowski_selected_disjoint_hyperbolicFrameSpan
        (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
        hM hp_orth_M hpDual_orth_M
  let EH : Hq ≃ₗ[ℂ] Hp :=
    complexMinkowski_hyperbolicFrameSpanEquiv_between
      (d := d) (s := s) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
  have hE_def :
      E = directSum_congr_sup_equiv_between
        (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
        hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH := by
    rfl
  let xH : Hq :=
    ⟨(x : Fin (d + 1) → ℂ), by
      exact Submodule.mem_sup_left (by simp [x.2])⟩
  let z : ↥(M ⊔ Hq) :=
    ⟨(x : Fin (d + 1) → ℂ), Submodule.mem_sup_right xH.2⟩
  have hEH_left :
      (EH xH : Fin (d + 1) → ℂ) ∈ Submodule.span ℂ (Set.range p) := by
    simpa [Hq, Hp, EH, xH] using
      complexMinkowski_hyperbolicFrameSpanEquiv_between_maps_left_span
        (d := d) (s := s) (q := q) (qDual := qDual)
        (p := p) (pDual := pDual)
        hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual x
  have hz :
      ((E z : ↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
        Submodule.span ℂ (Set.range pDual)))) : Fin (d + 1) → ℂ) =
        (EH xH : Fin (d + 1) → ℂ) := by
    rw [hE_def]
    have h := directSum_congr_sup_equiv_between_apply_of_eq_add
      (d := d) (A := M) (B := Hq) (C := M) (D := Hp)
      hM_Hq hM_Hp (LinearEquiv.refl ℂ M) EH
      (x := z) (a := (0 : M)) (b := xH) (by simp [z, xH])
    simpa [Hq, Hp, z, xH] using h
  simpa [Hq, z] using hz.symm ▸ hEH_left

/-- Generic constructor for the proper residual hyperbolic block data from
compatible source and target hyperbolic frames.  The final target frame `qOut`
may be larger than the actual target image frame `p`; only `span p ≤ span qOut`
is needed for the residual-frame consumer. -/
noncomputable def
    hw_selectedResidualHyperbolicBlockExtensionData_of_hyperbolicFrames
    {d s t : ℕ}
    {M Rleft : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q qDual p pDual : Fin s → Fin (d + 1) → ℂ}
    {qOut : Fin t → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hRleft_le_q :
      Rleft ≤ Submodule.span ℂ (Set.range q))
    (hLproper :
      Module.finrank ℂ
        (↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual)))) < d + 1)
    (hq_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hqDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (qDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hp_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (p c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hpDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (pDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0)
    (hp_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (p c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hq_dual :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_span_qOut :
      Submodule.span ℂ (Set.range p) ≤
        Submodule.span ℂ (Set.range qOut)) :
    HWSelectedResidualHyperbolicBlockExtensionData
      (d := d) (M := M) (Rleft := Rleft) qOut :=
  let K : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (Submodule.span ℂ (Set.range q) ⊔
      Submodule.span ℂ (Set.range qDual))
  let L : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (Submodule.span ℂ (Set.range p) ⊔
      Submodule.span ℂ (Set.range pDual))
  let Tblock : K ≃ₗ[ℂ] L :=
    complexMinkowski_selectedHyperbolicBlockEquiv_between
      (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
      (p := p) (pDual := pDual)
      hM hq_orth_M hqDual_orth_M hp_orth_M hpDual_orth_M
      hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual
  { K := K
    L := L
    K_nondeg := by
      simpa [K] using
        complexMinkowski_selected_sup_hyperbolicFrameSpan_nondegenerate
          (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
          hM hq_orth_M hqDual_orth_M hq_pair_zero
          hqDual_pair_zero hq_dual
    L_nondeg := by
      simpa [L] using
        complexMinkowski_selected_sup_hyperbolicFrameSpan_nondegenerate
          (d := d) (s := s) (M := M) (q := p) (qDual := pDual)
          hM hp_orth_M hpDual_orth_M hp_pair_zero
          hpDual_pair_zero hp_dual
    L_proper := by
      simpa [L] using hLproper
    K_M := by
      intro m hm
      exact Submodule.mem_sup_left hm
    K_left := by
      intro x hx
      exact Submodule.mem_sup_right (Submodule.mem_sup_left (hRleft_le_q hx))
    Tblock := Tblock
    Tblock_preserves := by
      intro x y
      simpa [K, L, Tblock] using
        complexMinkowski_selectedHyperbolicBlockEquiv_between_preserves
          (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
          (p := p) (pDual := pDual)
          hM hq_orth_M hqDual_orth_M hp_orth_M hpDual_orth_M
          hq_pair_zero hqDual_pair_zero hp_pair_zero hpDual_pair_zero
          hq_dual hp_dual x y
    Tblock_M := by
      intro m
      simpa [K, L, Tblock] using
        complexMinkowski_selectedHyperbolicBlockEquiv_between_maps_M
          (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
          (p := p) (pDual := pDual)
          hM hq_orth_M hqDual_orth_M hp_orth_M hpDual_orth_M
          hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual m
    Tblock_left_span := by
      intro x
      let xq : Submodule.span ℂ (Set.range q) :=
        ⟨(x : Fin (d + 1) → ℂ), hRleft_le_q x.2⟩
      have hmap :
          ((Tblock ⟨(xq : Fin (d + 1) → ℂ),
            Submodule.mem_sup_right (Submodule.mem_sup_left xq.2)⟩ :
            L) : Fin (d + 1) → ℂ) ∈
            Submodule.span ℂ (Set.range p) := by
        simpa [K, L, Tblock, xq] using
          complexMinkowski_selectedHyperbolicBlockEquiv_between_maps_left_span
            (d := d) (s := s) (M := M) (q := q) (qDual := qDual)
            (p := p) (pDual := pDual)
            hM hq_orth_M hqDual_orth_M hp_orth_M hpDual_orth_M
            hqDual_pair_zero hpDual_pair_zero hq_dual hp_dual xq
      have hsame :
          (Tblock ⟨(x : Fin (d + 1) → ℂ),
            Submodule.mem_sup_right
              (Submodule.mem_sup_left (hRleft_le_q x.2))⟩ :
            L) =
          Tblock ⟨(xq : Fin (d + 1) → ℂ),
            Submodule.mem_sup_right (Submodule.mem_sup_left xq.2)⟩ := by
        apply Subtype.ext
        rfl
      exact hp_span_qOut (by simpa [xq, hsame] using hmap) }

/-- A finite basis frame for a totally isotropic subspace, together with an
isotropic dual frame in a chosen nondegenerate ambient subspace. -/
structure ComplexMinkowskiIsotropicSubspaceBasisDualFrameData
    (d : ℕ)
    (N R : Submodule ℂ (Fin (d + 1) → ℂ)) where
  k : ℕ
  frame : Fin k → Fin (d + 1) → ℂ
  dual : Fin k → Fin (d + 1) → ℂ
  k_eq : k = Module.finrank ℂ R
  frame_mem_R : ∀ c, frame c ∈ R
  frame_span_eq : Submodule.span ℂ (Set.range frame) = R
  frame_mem_N : ∀ c, frame c ∈ N
  dual_mem_N : ∀ c, dual c ∈ N
  frame_independent : LinearIndependent ℂ frame
  frame_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (frame c) (frame c') = 0
  dual_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (dual c) (dual c') = 0
  frame_dual :
    ∀ c c',
      sourceComplexMinkowskiInner d (frame c) (dual c') =
        if c = c' then (1 : ℂ) else 0

/-- A totally isotropic subspace inside a nondegenerate ambient subspace admits
a finite basis frame and an isotropic dual frame in that same ambient subspace.

This is the source/target hyperbolic-basis supply used before constructing the
completed residual block equivalence. -/
noncomputable def complexMinkowski_isotropicSubspace_basisDualFrameData
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hN : ComplexMinkowskiNondegenerateSubspace d N)
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R := by
  let k := Module.finrank ℂ R
  let b := Module.finBasis ℂ R
  let frame : Fin k → Fin (d + 1) → ℂ := fun c => (b c : R)
  have hframe_mem_R : ∀ c, frame c ∈ R := by
    intro c
    exact (b c).2
  have hframe_mem_N : ∀ c, frame c ∈ N := by
    intro c
    exact hR_le (hframe_mem_R c)
  have hframe_independent : LinearIndependent ℂ frame := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum c
    have hsum_R : (∑ i : Fin k, a i • b i) = 0 := by
      apply Subtype.ext
      simpa [frame] using hsum
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent a hsum_R) c
  have hframe_span_eq :
      Submodule.span ℂ (Set.range frame) = R := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by
        rintro x ⟨c, rfl⟩
        exact hframe_mem_R c)
    · intro x hx
      let xr : R := ⟨x, hx⟩
      have hx_repr :
          x = ∑ c : Fin k, b.repr xr c • frame c := by
        calc
          x = (xr : Fin (d + 1) → ℂ) := rfl
          _ = ((∑ c : Fin k, b.repr xr c • b c : R) :
                Fin (d + 1) → ℂ) := by
                exact congrArg
                  (fun y : R => (y : Fin (d + 1) → ℂ))
                  (b.sum_repr xr).symm
          _ = ∑ c : Fin k, ((b.repr xr c • b c : R) :
                Fin (d + 1) → ℂ) := by
                change R.subtype
                    (∑ c : Fin k, b.repr xr c • b c) =
                  ∑ c : Fin k, R.subtype (b.repr xr c • b c)
                rw [map_sum]
          _ = ∑ c : Fin k, b.repr xr c • frame c := by
                rfl
      rw [hx_repr]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ (b.repr xr c)
          (Submodule.subset_span ⟨c, rfl⟩)
  have hframe_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (frame c) (frame c') = 0 := by
    intro c c'
    exact hR_iso ⟨frame c, hframe_mem_R c⟩ ⟨frame c', hframe_mem_R c'⟩
  let hdual_exists :=
    complexMinkowski_isotropicFrame_dualFrameIn
      (d := d) (s := k) (N := N) (q := frame)
      hN hframe_mem_N hframe_independent hframe_pair_zero
  let dual : Fin k → Fin (d + 1) → ℂ := Classical.choose hdual_exists
  have hdual_mem_N : ∀ c, dual c ∈ N :=
    (Classical.choose_spec hdual_exists).1
  have hdual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (dual c) (dual c') = 0 :=
    (Classical.choose_spec hdual_exists).2.1
  have hframe_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (frame c) (dual c') =
          if c = c' then (1 : ℂ) else 0 :=
    (Classical.choose_spec hdual_exists).2.2
  exact
    { k := k
      frame := frame
      dual := dual
      k_eq := rfl
      frame_mem_R := hframe_mem_R
      frame_span_eq := hframe_span_eq
      frame_mem_N := hframe_mem_N
      dual_mem_N := hdual_mem_N
      frame_independent := hframe_independent
      frame_pair_zero := hframe_pair_zero
      dual_pair_zero := hdual_pair_zero
      frame_dual := hframe_dual }

namespace ComplexMinkowskiIsotropicSubspaceBasisDualFrameData

/-- If the ambient subspace of a hyperbolic completion lies in the orthogonal
complement of `M`, then the basis half is orthogonal to `M`. -/
theorem frame_orthogonal_to_subspace
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M) :
    ∀ c (m : M),
      sourceComplexMinkowskiInner d (D.frame c)
        (m : Fin (d + 1) → ℂ) = 0 := by
  intro c m
  exact
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M (D.frame c)).1
      (hN_le_orth (D.frame_mem_N c)) m

/-- If the ambient subspace of a hyperbolic completion lies in the orthogonal
complement of `M`, then the dual half is orthogonal to `M`. -/
theorem dual_orthogonal_to_subspace
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M) :
    ∀ c (m : M),
      sourceComplexMinkowskiInner d (D.dual c)
        (m : Fin (d + 1) → ℂ) = 0 := by
  intro c m
  exact
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M (D.dual c)).1
      (hN_le_orth (D.dual_mem_N c)) m

/-- A selected nondegenerate block plus the hyperbolic completion supplied by
`ComplexMinkowskiIsotropicSubspaceBasisDualFrameData` is nondegenerate. -/
theorem selected_sup_hyperbolic_nondegenerate
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R)
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M) :
    ComplexMinkowskiNondegenerateSubspace d
      (M ⊔ (Submodule.span ℂ (Set.range D.frame) ⊔
        Submodule.span ℂ (Set.range D.dual))) :=
  complexMinkowski_selected_sup_hyperbolicFrameSpan_nondegenerate
    (d := d) (s := D.k) (M := M) (q := D.frame) (qDual := D.dual)
    hM (D.frame_orthogonal_to_subspace hN_le_orth)
    (D.dual_orthogonal_to_subspace hN_le_orth)
    D.frame_pair_zero D.dual_pair_zero D.frame_dual

/-- An injective pairing-preserving embedding of the residual subspace sends
the source basis half of a hyperbolic completion to an independent isotropic
target frame, and that target frame admits an isotropic dual frame in the
target nondegenerate subspace. -/
theorem imageFrame_dualFrameIn
    {d : ℕ}
    {Nsrc Ntgt R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d Nsrc R)
    (hNtgt : ComplexMinkowskiNondegenerateSubspace d Ntgt)
    (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hE_inj : Function.Injective E)
    (hE_mem : ∀ x : R, E x ∈ Ntgt)
    (hE_preserves :
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ)) :
    let targetFrame : Fin D.k → Fin (d + 1) → ℂ :=
      fun c => E ⟨D.frame c, D.frame_mem_R c⟩
    ∃ targetDual : Fin D.k → Fin (d + 1) → ℂ,
      (∀ c, targetFrame c ∈ Ntgt) ∧
      LinearIndependent ℂ targetFrame ∧
      (∀ c c',
        sourceComplexMinkowskiInner d (targetFrame c) (targetFrame c') = 0) ∧
      (∀ c, targetDual c ∈ Ntgt) ∧
      (∀ c c',
        sourceComplexMinkowskiInner d (targetDual c) (targetDual c') = 0) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (targetFrame c) (targetDual c') =
          if c = c' then (1 : ℂ) else 0 := by
  intro targetFrame
  have htarget_mem : ∀ c, targetFrame c ∈ Ntgt := by
    intro c
    exact hE_mem ⟨D.frame c, D.frame_mem_R c⟩
  have htarget_pair_zero :
      ∀ c c',
        sourceComplexMinkowskiInner d (targetFrame c) (targetFrame c') = 0 := by
    intro c c'
    calc
      sourceComplexMinkowskiInner d (targetFrame c) (targetFrame c') =
          sourceComplexMinkowskiInner d
            (D.frame c) (D.frame c') := by
            exact hE_preserves
              ⟨D.frame c, D.frame_mem_R c⟩
              ⟨D.frame c', D.frame_mem_R c'⟩
      _ = 0 := D.frame_pair_zero c c'
  have htarget_independent : LinearIndependent ℂ targetFrame := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum c
    let rFrame : Fin D.k → R := fun i => ⟨D.frame i, D.frame_mem_R i⟩
    have hE_sum :
        E (∑ i : Fin D.k, a i • rFrame i) = 0 := by
      calc
        E (∑ i : Fin D.k, a i • rFrame i) =
            ∑ i : Fin D.k, a i • E (rFrame i) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [map_smul]
        _ = ∑ i : Fin D.k, a i • targetFrame i := rfl
        _ = 0 := hsum
    have hsum_R : (∑ i : Fin D.k, a i • rFrame i) = 0 :=
      hE_inj (by simpa using hE_sum)
    have hsum_V :
        ∑ i : Fin D.k, a i • D.frame i = 0 := by
      have h := congrArg
        (fun x : R => (x : Fin (d + 1) → ℂ)) hsum_R
      simpa [rFrame] using h
    exact
      (Fintype.linearIndependent_iff.mp D.frame_independent a hsum_V) c
  rcases complexMinkowski_isotropicFrame_dualFrameIn
      (d := d) (s := D.k) (N := Ntgt) (q := targetFrame)
      hNtgt htarget_mem htarget_independent htarget_pair_zero with
    ⟨targetDual, htargetDual_mem, htargetDual_pair_zero, htarget_dual⟩
  exact ⟨targetDual, htarget_mem, htarget_independent,
    htarget_pair_zero, htargetDual_mem, htargetDual_pair_zero, htarget_dual⟩

/-- Specialize the generic hyperbolic-frame block-data constructor to the
source basis-dual packet.  The target frame and target dual frame are supplied
explicitly; a later producer obtains them from a residual embedding into a
maximal target frame. -/
noncomputable def selectedResidualHyperbolicBlockExtensionData
    {d t : ℕ}
    {M N Rleft : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N Rleft)
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M)
    {p pDual : Fin D.k → Fin (d + 1) → ℂ}
    {qOut : Fin t → Fin (d + 1) → ℂ}
    (hp_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (p c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hpDual_orth_M :
      ∀ c (m : M), sourceComplexMinkowskiInner d (pDual c)
        (m : Fin (d + 1) → ℂ) = 0)
    (hp_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (p c') = 0)
    (hpDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (pDual c) (pDual c') = 0)
    (hp_dual :
      ∀ c c', sourceComplexMinkowskiInner d (p c) (pDual c') =
        if c = c' then (1 : ℂ) else 0)
    (hp_span_qOut :
      Submodule.span ℂ (Set.range p) ≤
        Submodule.span ℂ (Set.range qOut))
    (hLproper :
      Module.finrank ℂ
        (↥(M ⊔ (Submodule.span ℂ (Set.range p) ⊔
          Submodule.span ℂ (Set.range pDual)))) < d + 1) :
    HWSelectedResidualHyperbolicBlockExtensionData
      (d := d) (M := M) (Rleft := Rleft) qOut :=
  hw_selectedResidualHyperbolicBlockExtensionData_of_hyperbolicFrames
    (d := d) (s := D.k) (t := t) (M := M) (Rleft := Rleft)
    (q := D.frame) (qDual := D.dual) (p := p) (pDual := pDual)
    (qOut := qOut)
    hM
    (by
      intro x hx
      simpa [D.frame_span_eq] using hx)
    hLproper
    (D.frame_orthogonal_to_subspace hN_le_orth)
    (D.dual_orthogonal_to_subspace hN_le_orth)
    hp_orth_M hpDual_orth_M
    D.frame_pair_zero D.dual_pair_zero hp_pair_zero hpDual_pair_zero
    D.frame_dual hp_dual hp_span_qOut

end ComplexMinkowskiIsotropicSubspaceBasisDualFrameData

end BHW
