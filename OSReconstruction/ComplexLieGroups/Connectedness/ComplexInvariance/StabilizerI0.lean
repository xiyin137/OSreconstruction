import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetBasic
import OSReconstruction.ComplexLieGroups.Connectedness.ForwardTubeDomain
import OSReconstruction.ComplexLieGroups.Complexification
import OSReconstruction.ComplexLieGroups.SOConnected
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

open Complex Topology Matrix LorentzLieGroup

namespace BHW

variable {m : ℕ}

/-- Canonical one-point configuration `i e₀` in dimension `m+2`. -/
def wI0 : Fin 1 → Fin (m + 2) → ℂ :=
  fun _ μ => if μ = 0 then Complex.I else 0

/-- One-point configuration `c e₀` in dimension `m+2`. -/
def wScalarE0 (c : ℂ) : Fin 1 → Fin (m + 2) → ℂ :=
  fun _ μ => if μ = 0 then c else 0

/-- Forward-tube characterization for one-point configurations. -/
private lemma forwardTube_one_iff_inOpenForwardCone
    (w : Fin 1 → Fin (m + 2) → ℂ) :
    w ∈ ForwardTube (m + 1) 1 ↔
      InOpenForwardCone (m + 1) (fun μ => (w 0 μ).im) := by
  constructor
  · intro hw
    simpa [ForwardTube] using hw 0
  · intro hw k
    fin_cases k
    simpa [ForwardTube] using hw

/-- Closed form of the one-point action on `wScalarE0 c`. -/
theorem complexLorentzAction_wScalarE0
    (Λ : ComplexLorentzGroup (m + 1)) (c : ℂ) :
    complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c) =
      (fun _ μ => c * Λ.val μ 0) := by
  ext k μ
  fin_cases k
  simp [wScalarE0, complexLorentzAction, complexLorentzVectorAction, mul_comm]

/-- Orbit-set membership for `wScalarE0 c` is a first-column forward-cone condition. -/
theorem mem_orbitSet_wScalarE0_iff
    (Λ : ComplexLorentzGroup (m + 1)) (c : ℂ) :
    Λ ∈ orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) ↔
      InOpenForwardCone (m + 1) (fun μ => (c * Λ.val μ 0).im) := by
  constructor
  · intro hΛ
    have hFT :
        complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c) ∈
          ForwardTube (m + 1) 1 := hΛ
    have hcone :=
      (forwardTube_one_iff_inOpenForwardCone (m := m)
        (complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c))).1 hFT
    rw [complexLorentzAction_wScalarE0 (m := m) Λ c] at hcone
    simpa using hcone
  · intro hcone
    exact
      (forwardTube_one_iff_inOpenForwardCone (m := m)
        (complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c))).2
        (by
          rw [complexLorentzAction_wScalarE0 (m := m) Λ c]
          simpa using hcone)

/-- First-column map on `SO⁺(1,m+1;ℂ)`. -/
def firstColCLG : ComplexLorentzGroup (m + 1) → (Fin (m + 2) → ℂ) :=
  fun Λ k => Λ.val k 0

theorem continuous_firstColCLG : Continuous (firstColCLG (m := m)) := by
  apply continuous_pi
  intro k
  exact (continuous_apply 0).comp ((continuous_apply k).comp ComplexLorentzGroup.continuous_val)

/-- Orbit-set membership for `wScalarE0 c` depends only on first-column data. -/
theorem mem_orbitSet_wScalarE0_iff_firstCol
    (c : ℂ) (Λ : ComplexLorentzGroup (m + 1)) :
    Λ ∈ orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) ↔
      InOpenForwardCone (m + 1) (fun μ => (c * firstColCLG (m := m) Λ μ).im) := by
  simpa [firstColCLG] using (mem_orbitSet_wScalarE0_iff (m := m) Λ c)

/-- The one-point orbit set of `wScalarE0 c` as a first-column preimage. -/
theorem orbitSet_wScalarE0_eq_preimage_firstCol
    (c : ℂ) :
    orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)
      = (firstColCLG (m := m)) ⁻¹'
          {v : Fin (m + 2) → ℂ | InOpenForwardCone (m + 1) (fun μ => (c * v μ).im)} := by
  ext Λ
  constructor
  · intro hΛ
    exact (mem_orbitSet_wScalarE0_iff_firstCol (m := m) c Λ).1 hΛ
  · intro hΛ
    exact (mem_orbitSet_wScalarE0_iff_firstCol (m := m) c Λ).2 hΛ

private lemma minkowskiComplex_decomp
    (v : Fin (m + 2) → ℂ) :
    (∑ μ : Fin (m + 2), (minkowskiSignature (m + 1) μ : ℂ) * v μ ^ 2) =
      -(v 0) ^ 2 + ∑ i : Fin (m + 1), v i.succ ^ 2 := by
  rw [Fin.sum_univ_succ]
  congr 1
  · simp [minkowskiSignature]
  · congr 1
    ext i
    simp [minkowskiSignature, Fin.succ_ne_zero]

/-- Any one-point forward-tube configuration is a complex-Lorentz image of
`wScalarE0 c` for a nonzero scalar `c`. -/
theorem exists_action_wScalarE0_of_forwardTube_one
    (w : Fin 1 → Fin (m + 2) → ℂ)
    (hw : w ∈ ForwardTube (m + 1) 1) :
    ∃ (Γ : ComplexLorentzGroup (m + 1)) (c : ℂ), c ≠ 0 ∧
      w = complexLorentzAction (d := m + 1) (n := 1) Γ (wScalarE0 (m := m) c) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let q : ℂ :=
    ∑ μ : Fin (m + 2), (minkowskiSignature (m + 1) μ : ℂ) * (w 0 μ) ^ 2
  have hq_ne : q ≠ 0 := by
    simpa [q] using
      (forwardTube_one_complexQuadratic_ne_zero (d := m + 1) w hw)
  obtain ⟨c, hc_mul⟩ : ∃ z : ℂ, -q = z * z :=
    IsAlgClosed.exists_eq_mul_self (-q)
  have hcsq : c ^ 2 = -q := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hc_mul.symm
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hq_ne
    have hminus_q : -q = 0 := by
      calc
        -q = c ^ 2 := hcsq.symm
        _ = 0 := by simp [hc0]
    simpa using neg_eq_zero.mp hminus_q
  let v : Fin (m + 2) → ℂ := fun μ => w 0 μ / c
  let u : Fin (m + 2) → ℂ :=
    fun μ => Fin.cases (v 0) (fun i => v i.succ * Complex.I) μ
  have hu_norm : ∑ k : Fin (m + 2), u k ^ 2 = 1 := by
    have hdiv_sq : ∀ z : ℂ, (z / c) ^ 2 = z ^ 2 / c ^ 2 := by
      intro z
      field_simp [pow_two]
    have hq_decomp :
        q = -(w 0 0) ^ 2 + ∑ i : Fin (m + 1), (w 0 i.succ) ^ 2 := by
      simpa [q] using minkowskiComplex_decomp (m := m) (fun μ => w 0 μ)
    have hneg_q_decomp :
        -q = (w 0 0) ^ 2 - ∑ i : Fin (m + 1), (w 0 i.succ) ^ 2 := by
      rw [hq_decomp]
      ring
    calc
      ∑ k : Fin (m + 2), u k ^ 2
          = (v 0) ^ 2 + ∑ i : Fin (m + 1), (v i.succ * Complex.I) ^ 2 := by
              rw [Fin.sum_univ_succ]
              simp [u]
      _ = (v 0) ^ 2 + ∑ i : Fin (m + 1), (-(v i.succ ^ 2)) := by
            refine congrArg (fun t => (v 0) ^ 2 + t) ?_
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (v i.succ * Complex.I) ^ 2 = v i.succ ^ 2 * Complex.I ^ 2 := by ring
              _ = v i.succ ^ 2 * (-1) := by simp [Complex.I_sq]
              _ = -(v i.succ ^ 2) := by ring
      _ = (v 0) ^ 2 - ∑ i : Fin (m + 1), (v i.succ) ^ 2 := by
            simp [sub_eq_add_neg]
      _ = (w 0 0) ^ 2 / c ^ 2 - (∑ i : Fin (m + 1), (w 0 i.succ) ^ 2) / c ^ 2 := by
            simp [v, hdiv_sq, Finset.sum_div]
      _ = ((w 0 0) ^ 2 - ∑ i : Fin (m + 1), (w 0 i.succ) ^ 2) / c ^ 2 := by
            field_simp
      _ = (-q) / c ^ 2 := by rw [hneg_q_decomp]
      _ = 1 := by
            rw [hcsq]
            field_simp [hq_ne]
  obtain ⟨A, hAcol⟩ := SOComplex.exists_so_with_firstCol (m := m) u hu_norm
  let Γ : ComplexLorentzGroup (m + 1) := ComplexLorentzGroup.fromSOComplex (d := m + 1) A
  have hto : ComplexLorentzGroup.toSOComplex (d := m + 1) Γ = A := by
    simpa [Γ] using
      (ComplexLorentzGroup.toSOComplex_fromSOComplex (d := m + 1) A)
  have hΓcol : ∀ k : Fin (m + 2), Γ.val k 0 = v k := by
    intro k
    refine Fin.cases ?_ ?_ k
    · calc
        Γ.val 0 0 = (ComplexLorentzGroup.toSOComplex (d := m + 1) Γ).val 0 0 := by
                      simpa using (ComplexLorentzGroup.toSOComplex_entry_00
                        (d := m + 1) Γ).symm
        _ = A.val 0 0 := by simp [hto]
        _ = u 0 := hAcol 0
        _ = v 0 := by simp [u]
    · intro i
      have hmul :
          Γ.val i.succ 0 * Complex.I = v i.succ * Complex.I := by
        calc
          Γ.val i.succ 0 * Complex.I
              = (ComplexLorentzGroup.toSOComplex (d := m + 1) Γ).val i.succ 0 := by
                    simpa using (ComplexLorentzGroup.toSOComplex_entry_succ0
                      (d := m + 1) Γ i).symm
          _ = A.val i.succ 0 := by simp [hto]
          _ = u i.succ := hAcol i.succ
          _ = v i.succ * Complex.I := by simp [u]
      have hmul' := congrArg (fun z : ℂ => z * (-Complex.I)) hmul
      simpa [mul_assoc] using hmul'
  have hact : complexLorentzAction (d := m + 1) (n := 1) Γ (wScalarE0 (m := m) c) =
      (fun _ μ => c * Γ.val μ 0) :=
    complexLorentzAction_wScalarE0 (m := m) Γ c
  refine ⟨Γ, c, hc_ne, ?_⟩
  ext k μ
  fin_cases k
  have hcw : c * v μ = w 0 μ := by
    unfold v
    field_simp [hc_ne]
  calc
    w 0 μ = c * v μ := hcw.symm
    _ = c * Γ.val μ 0 := by simp [hΓcol μ]
    _ = (complexLorentzAction (d := m + 1) (n := 1) Γ (wScalarE0 (m := m) c)) 0 μ := by
          simpa using (congr_fun (congr_fun hact 0) μ).symm

/-- Stabilizer of `wI0` under the one-point complex Lorentz action. -/
def stabilizerI0 : Set (ComplexLorentzGroup (m + 1)) :=
  {Λ | complexLorentzAction (d := m + 1) (n := 1) Λ (wI0 (m := m)) = wI0 (m := m)}

/-- First-column fiber in `SO⁺(1,m+1;ℂ)`. -/
def firstColEqVecCLG (v : Fin (m + 2) → ℂ) : Set (ComplexLorentzGroup (m + 1)) :=
  {Λ | ∀ k : Fin (m + 2), Λ.val k 0 = v k}

theorem mem_stabilizerI0_iff_firstColEqE0 (Λ : ComplexLorentzGroup (m + 1)) :
    Λ ∈ stabilizerI0 (m := m) ↔
      (∀ k : Fin (m + 2), Λ.val k 0 = if k = 0 then 1 else 0) := by
  constructor
  · intro hΛ k
    have hEq : complexLorentzAction (d := m + 1) (n := 1) Λ (wI0 (m := m)) = wI0 (m := m) := by
      simpa [stabilizerI0] using hΛ
    refine Fin.cases ?_ ?_ k
    · have hk0 : Λ.val 0 0 * Complex.I = Complex.I := by
        simpa [wI0, complexLorentzAction, complexLorentzVectorAction] using
          congr_fun (congr_fun hEq 0) 0
      have hmul := congrArg (fun z : ℂ => z * (-Complex.I)) hk0
      simpa [mul_assoc] using hmul
    · intro i
      have hmul : Λ.val i.succ 0 * Complex.I = 0 := by
        simpa [wI0, complexLorentzAction, complexLorentzVectorAction, Fin.succ_ne_zero] using
          congr_fun (congr_fun hEq 0) i.succ
      have hzero : Λ.val i.succ 0 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
      simpa [Fin.succ_ne_zero] using hzero
  · intro hcol
    refine Set.mem_setOf.mpr ?_
    ext _ μ
    refine Fin.cases ?_ ?_ μ
    · simpa [wI0, complexLorentzAction, complexLorentzVectorAction] using hcol 0
    · intro i
      have hzero : Λ.val i.succ 0 = 0 := by
        simpa [Fin.succ_ne_zero] using hcol i.succ
      simp [wI0, complexLorentzAction, complexLorentzVectorAction,
        Fin.succ_ne_zero, hzero]

theorem mem_stabilizer_wScalarE0_iff_firstColEqE0
    (c : ℂ) (hc : c ≠ 0) (Λ : ComplexLorentzGroup (m + 1)) :
    Λ ∈ stabilizer (d := m + 1) (n := 1) (wScalarE0 (m := m) c) ↔
      (∀ k : Fin (m + 2), Λ.val k 0 = if k = 0 then 1 else 0) := by
  constructor
  · intro hΛ k
    have hEq :
        complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c) =
          wScalarE0 (m := m) c := by
      simpa [stabilizer] using hΛ
    refine Fin.cases ?_ ?_ k
    · have hk0 : Λ.val 0 0 * c = c := by
        simpa [wScalarE0, complexLorentzAction, complexLorentzVectorAction] using
          congr_fun (congr_fun hEq 0) 0
      have hmul := congrArg (fun z : ℂ => z * c⁻¹) hk0
      have hc' : c * c⁻¹ = (1 : ℂ) := by exact mul_inv_cancel₀ hc
      simpa [mul_assoc, hc'] using hmul
    · intro i
      have hmul : Λ.val i.succ 0 * c = 0 := by
        simpa [wScalarE0, complexLorentzAction, complexLorentzVectorAction,
          Fin.succ_ne_zero] using
          congr_fun (congr_fun hEq 0) i.succ
      have hzero : Λ.val i.succ 0 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hc
      simpa [Fin.succ_ne_zero] using hzero
  · intro hcol
    refine Set.mem_setOf.mpr ?_
    ext _ μ
    refine Fin.cases ?_ ?_ μ
    · simp [wScalarE0, complexLorentzAction, complexLorentzVectorAction, hcol 0]
    · intro i
      have hzero : Λ.val i.succ 0 = 0 := by
        simpa [Fin.succ_ne_zero] using hcol i.succ
      simp [wScalarE0, complexLorentzAction, complexLorentzVectorAction,
        Fin.succ_ne_zero, hzero]

theorem stabilizerI0_eq_fromSO_image_firstCol :
    stabilizerI0 (m := m) =
      (ComplexLorentzGroup.fromSOComplex (d := m + 1)) ''
        {A : SOComplex (m + 2) | SOComplex.firstColEqE0 A} := by
  ext Λ
  constructor
  · intro hΛ
    have hcolΛ : ∀ k : Fin (m + 2), Λ.val k 0 = if k = 0 then 1 else 0 :=
      (mem_stabilizerI0_iff_firstColEqE0 (m := m) Λ).mp hΛ
    have hto :
        ∀ k : Fin (m + 2),
          (ComplexLorentzGroup.toSOComplex (d := m + 1) Λ).val k 0 = if k = 0 then 1 else 0 :=
      (ComplexLorentzGroup.toSOComplex_firstColEqE0_iff (d := m + 1) Λ).2 hcolΛ
    refine ⟨ComplexLorentzGroup.toSOComplex (d := m + 1) Λ, hto, ?_⟩
    simpa using (ComplexLorentzGroup.fromSOComplex_toSOComplex (d := m + 1) Λ)
  · rintro ⟨A, hA, rfl⟩
    have hto :
        ∀ k : Fin (m + 2),
          (ComplexLorentzGroup.toSOComplex (d := m + 1)
            (ComplexLorentzGroup.fromSOComplex (d := m + 1) A)).val k 0 =
            if k = 0 then 1 else 0 := by
      intro k
      simpa [ComplexLorentzGroup.toSOComplex_fromSOComplex (d := m + 1) A] using hA k
    have hcol :
        ∀ k : Fin (m + 2),
          (ComplexLorentzGroup.fromSOComplex (d := m + 1) A).val k 0 =
            if k = 0 then 1 else 0 :=
      (ComplexLorentzGroup.toSOComplex_firstColEqE0_iff (d := m + 1)
        (ComplexLorentzGroup.fromSOComplex (d := m + 1) A)).1 hto
    exact (mem_stabilizerI0_iff_firstColEqE0 (m := m)
      (ComplexLorentzGroup.fromSOComplex (d := m + 1) A)).2 hcol

/-- For `c ≠ 0`, the stabilizer of `c e₀` equals the canonical stabilizer
`Stab(i e₀)`. -/
theorem stabilizer_wScalarE0_eq_stabilizerI0
    (c : ℂ) (hc : c ≠ 0) :
    stabilizer (d := m + 1) (n := 1) (wScalarE0 (m := m) c) =
      stabilizerI0 (m := m) := by
  ext Λ
  rw [mem_stabilizer_wScalarE0_iff_firstColEqE0 (m := m) c hc Λ,
      mem_stabilizerI0_iff_firstColEqE0 (m := m) Λ]

/-- Connectedness of the `i e₀` stabilizer in `SO⁺(1,m+1;ℂ)`. -/
theorem isConnected_stabilizerI0 : IsConnected (stabilizerI0 (m := m)) := by
  have hSO : IsConnected {A : SOComplex (m + 2) | SOComplex.firstColEqE0 A} :=
    SOComplex.isConnected_firstColEqE0_set (m := m)
  have hIm :
      IsConnected
        ((ComplexLorentzGroup.fromSOComplex (d := m + 1)) ''
          {A : SOComplex (m + 2) | SOComplex.firstColEqE0 A}) :=
    hSO.image _ (ComplexLorentzGroup.continuous_fromSOComplex (d := m + 1)).continuousOn
  simpa [stabilizerI0_eq_fromSO_image_firstCol (m := m)] using hIm

/-- Any nonempty first-column fiber in `SO⁺(1,m+1;ℂ)` is connected. -/
theorem isConnected_firstColEqVecCLG_of_nonempty
    (v : Fin (m + 2) → ℂ)
    (hnonempty : (firstColEqVecCLG (m := m) v).Nonempty) :
    IsConnected (firstColEqVecCLG (m := m) v) := by
  rcases hnonempty with ⟨Λ0, hΛ0col⟩
  let S0 : Set (ComplexLorentzGroup (m + 1)) := stabilizerI0 (m := m)
  let Sv : Set (ComplexLorentzGroup (m + 1)) := firstColEqVecCLG (m := m) v
  have hS0_conn : IsConnected S0 := by
    simpa [S0] using (isConnected_stabilizerI0 (m := m))
  let φ : ComplexLorentzGroup (m + 1) → ComplexLorentzGroup (m + 1) :=
    fun g => Λ0 * g
  have hφ_cont : Continuous φ := continuous_const.mul continuous_id
  have hφ_map : φ '' S0 = Sv := by
    ext Λ
    constructor
    · rintro ⟨g, hg, rfl⟩
      intro k
      have hg0 : ∀ t : Fin (m + 2), g.val t 0 = if t = 0 then 1 else 0 :=
        (mem_stabilizerI0_iff_firstColEqE0 (m := m) g).1 hg
      calc
        (Λ0 * g).val k 0 = ∑ j : Fin (m + 2), Λ0.val k j * g.val j 0 := by
            change ((Λ0.val * g.val) k 0) = _
            rw [Matrix.mul_apply]
        _ = Λ0.val k 0 := by
            rw [Finset.sum_eq_single 0]
            · simp [hg0]
            · intro j _ hj
              simp [hg0, hj]
            · simp [hg0]
        _ = v k := hΛ0col k
    · intro hΛ
      refine ⟨Λ0⁻¹ * Λ, ?_, ?_⟩
      · refine (mem_stabilizerI0_iff_firstColEqE0 (m := m) (Λ0⁻¹ * Λ)).2 ?_
        intro k
        have hmulM : (Λ0⁻¹ * Λ0).val = (1 : ComplexLorentzGroup (m + 1)).val := by
          exact congrArg ComplexLorentzGroup.val (inv_mul_cancel Λ0)
        have hmulk :
            ((Λ0⁻¹).val * Λ0.val) k 0 = ((1 : ComplexLorentzGroup (m + 1)).val) k 0 := by
          exact congrArg (fun M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ => M k 0) hmulM
        calc
          (Λ0⁻¹ * Λ).val k 0 = ∑ j : Fin (m + 2), (Λ0⁻¹).val k j * Λ.val j 0 := by
              change (((Λ0⁻¹).val * Λ.val) k 0) = _
              rw [Matrix.mul_apply]
          _ = ∑ j : Fin (m + 2), (Λ0⁻¹).val k j * Λ0.val j 0 := by
              apply Finset.sum_congr rfl
              intro j _
              simp [hΛ j, hΛ0col j]
          _ = ((Λ0⁻¹).val * Λ0.val) k 0 := by
              rw [Matrix.mul_apply]
          _ = ((1 : ComplexLorentzGroup (m + 1)).val) k 0 := hmulk
          _ = if k = 0 then 1 else 0 := by
              change ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) k 0) = _
              simp [Matrix.one_apply]
      · calc
          Λ0 * (Λ0⁻¹ * Λ) = (Λ0 * Λ0⁻¹) * Λ := by exact (mul_assoc Λ0 Λ0⁻¹ Λ).symm
          _ = Λ := by simp
  have hSv_conn : IsConnected Sv := by
    have hIm_conn : IsConnected (φ '' S0) := hS0_conn.image φ hφ_cont.continuousOn
    simpa [hφ_map] using hIm_conn
  simpa [Sv] using hSv_conn

/-- Fiber of `firstColCLG` inside the one-point orbit set of `wScalarE0 c`. -/
def orbitFirstColFiber_wScalarE0 (c : ℂ) (v : Fin (m + 2) → ℂ) :
    Set (ComplexLorentzGroup (m + 1)) :=
  {Λ | Λ ∈ orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)
    ∧ firstColCLG (m := m) Λ = v}

/-- Any nonempty first-column fiber in `orbitSet(wScalarE0 c)` is connected. -/
theorem isConnected_orbitFirstColFiber_wScalarE0_of_nonempty
    (c : ℂ) (v : Fin (m + 2) → ℂ)
    (hnonempty : (orbitFirstColFiber_wScalarE0 (m := m) c v).Nonempty) :
    IsConnected (orbitFirstColFiber_wScalarE0 (m := m) c v) := by
  rcases hnonempty with ⟨Λ0, hΛ0_orbit, hΛ0col⟩
  have hcol_nonempty : (firstColEqVecCLG (m := m) v).Nonempty := ⟨Λ0, by
    intro k
    simpa [firstColCLG] using congrArg (fun f => f k) hΛ0col⟩
  have hcol_conn : IsConnected (firstColEqVecCLG (m := m) v) :=
    isConnected_firstColEqVecCLG_of_nonempty (m := m) v hcol_nonempty
  have hsub_eq : orbitFirstColFiber_wScalarE0 (m := m) c v = firstColEqVecCLG (m := m) v := by
    ext Λ
    constructor
    · intro h k
      simpa [firstColCLG] using congrArg (fun f => f k) h.2
    · intro h
      have hΛ_orbit :
          Λ ∈ orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) := by
        have hcol0 : firstColCLG (m := m) Λ0 = v := by
          simpa [firstColCLG] using hΛ0col
        have hcol : firstColCLG (m := m) Λ = firstColCLG (m := m) Λ0 := by
          calc
            firstColCLG (m := m) Λ = v := by
              ext k
              simpa [firstColCLG] using h k
            _ = firstColCLG (m := m) Λ0 := hcol0.symm
        have hcone0 :
            InOpenForwardCone (m + 1)
              (fun μ => (c * firstColCLG (m := m) Λ0 μ).im) :=
          (mem_orbitSet_wScalarE0_iff_firstCol (m := m) c Λ0).1 hΛ0_orbit
        have hcone :
            InOpenForwardCone (m + 1)
              (fun μ => (c * firstColCLG (m := m) Λ μ).im) := by
          simpa [hcol] using hcone0
        exact (mem_orbitSet_wScalarE0_iff_firstCol (m := m) c Λ).2 hcone
      exact ⟨hΛ_orbit, by
        ext k
        simpa [firstColCLG] using h k⟩
  simpa [hsub_eq] using hcol_conn

/-- Connectedness of the stabilizer of `c e₀` for `c ≠ 0`. -/
theorem isConnected_stabilizer_wScalarE0
    (c : ℂ) (hc : c ≠ 0) :
    IsConnected (stabilizer (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) := by
  rw [stabilizer_wScalarE0_eq_stabilizerI0 (m := m) c hc]
  exact isConnected_stabilizerI0 (m := m)

/-- Connectedness transport from `Stab(i e₀)` to any conjugate point. -/
theorem isConnected_stabilizer_of_eq_action_wI0
    {w : Fin 1 → Fin (m + 2) → ℂ}
    (Γ : ComplexLorentzGroup (m + 1))
    (hEq : w = complexLorentzAction Γ (wI0 (m := m))) :
    IsConnected (stabilizer (d := m + 1) (n := 1) w) := by
  rw [hEq]
  simpa [stabilizer, wI0, stabilizerI0] using
    (isConnected_stabilizer_of_conj (d := m + 1) (n := 1)
      (w := wI0 (m := m)) Γ (isConnected_stabilizerI0 (m := m)))

/-- Connectedness transport from `Stab(c e₀)` (`c ≠ 0`) to any conjugate point. -/
theorem isConnected_stabilizer_of_eq_action_wScalarE0
    {w : Fin 1 → Fin (m + 2) → ℂ}
    (Γ : ComplexLorentzGroup (m + 1))
    (c : ℂ) (hc : c ≠ 0)
    (hEq : w = complexLorentzAction Γ (wScalarE0 (m := m) c)) :
    IsConnected (stabilizer (d := m + 1) (n := 1) w) := by
  rw [hEq]
  exact isConnected_stabilizer_of_conj (d := m + 1) (n := 1)
    (w := wScalarE0 (m := m) c) Γ (isConnected_stabilizer_wScalarE0 (m := m) c hc)

/-- Connectedness of the one-point stabilizer at any forward-tube configuration. -/
theorem isConnected_stabilizer_of_forwardTube_one
    (w : Fin 1 → Fin (m + 2) → ℂ)
    (hw : w ∈ ForwardTube (m + 1) 1) :
    IsConnected (stabilizer (d := m + 1) (n := 1) w) := by
  obtain ⟨Γ, c, hc, hEq⟩ :=
    exists_action_wScalarE0_of_forwardTube_one (m := m) w hw
  exact isConnected_stabilizer_of_eq_action_wScalarE0 (m := m) Γ c hc hEq

end BHW
