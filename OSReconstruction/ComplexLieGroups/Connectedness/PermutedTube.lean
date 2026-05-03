import OSReconstruction.ComplexLieGroups.Connectedness.ForwardTubeDomain

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- The extended forward tube: the orbit of the forward tube under the complex
    Lorentz group. T'_n = ⋃_Λ Λ · FT_n -/
def ExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ (Λ : ComplexLorentzGroup d),
    { z | ∃ w ∈ ForwardTube d n, z = complexLorentzAction Λ w }

/-- The permuted forward tube for permutation π:
    π(T_n) = {z ∈ ℂ^{n(d+1)} : (z_{π(1)}, ..., z_{π(n)}) ∈ T_n}. -/
def PermutedForwardTube (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

private lemma strictMono_perm_eq_one_local {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (hσ : StrictMono σ) :
    σ = 1 := by
  let e : Fin n ≃o Fin n := hσ.orderIsoOfSurjective σ σ.surjective
  have he : e = OrderIso.refl (Fin n) := Subsingleton.elim _ _
  apply Equiv.ext
  intro i
  have hval : e i = i := by
    simp [he]
  simpa [e] using hval

private lemma forwardTube_step_pos
    {z : Fin (n + 1) → Fin (d + 1) → ℂ}
    (hz : z ∈ ForwardTube d (n + 1))
    (i : Fin n) :
    0 < (z i.succ 0 - z i.castSucc 0).im := by
  have hk := hz i.succ
  simpa [ForwardTube, InOpenForwardCone] using hk.1

private lemma strictMono_imTime
    {z : Fin (n + 1) → Fin (d + 1) → ℂ}
    (hz : z ∈ ForwardTube d (n + 1)) :
    StrictMono (fun k : Fin (n + 1) => (z k 0).im) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hstep : 0 < (z i.succ 0 - z i.castSucc 0).im :=
    forwardTube_step_pos (d := d) hz i
  have him : (z i.succ 0).im - (z i.castSucc 0).im > 0 := by
    simpa [Complex.sub_im] using hstep
  linarith

private lemma strictMono_perm_of_strictMono_comp_local
    {n : ℕ}
    {f : Fin n → ℝ}
    (hf : StrictMono f)
    (σ : Equiv.Perm (Fin n))
    (hfσ : StrictMono (fun k : Fin n => f (σ k))) :
    StrictMono σ := by
  intro a b hab
  have hlt : f (σ a) < f (σ b) := hfσ hab
  by_contra hnot
  have hle : σ b ≤ σ a := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt' | heq
  · exact (lt_asymm hlt (hf hlt')).elim
  · exact (lt_irrefl _) (heq ▸ hlt)

/-- If `w` lies in both `FT` and `π(FT)`, then `π = 1`. -/
theorem permutedForwardTube_forces_perm_one
    (π : Equiv.Perm (Fin n))
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ ForwardTube d n)
    (hπw : w ∈ PermutedForwardTube d n π) :
    π = 1 := by
  cases n with
  | zero =>
      exact Subsingleton.elim π 1
  | succ m =>
      have hy : StrictMono (fun k : Fin (m + 1) => (w k 0).im) :=
        strictMono_imTime (d := d) hw
      have hyπ : StrictMono (fun k : Fin (m + 1) => (w (π k) 0).im) := by
        have hperm : (fun k => w (π k)) ∈ ForwardTube d (m + 1) := by
          simpa [PermutedForwardTube] using hπw
        exact strictMono_imTime (d := d) hperm
      exact strictMono_perm_eq_one_local π
        (strictMono_perm_of_strictMono_comp_local hy π hyπ)

/-- For nontrivial `π`, `FT` and `π(FT)` are disjoint. -/
theorem forwardTube_inter_permutedForwardTube_eq_empty_of_ne_one
    (π : Equiv.Perm (Fin n))
    (hπ : π ≠ 1) :
    ForwardTube d n ∩ PermutedForwardTube d n π = (∅ : Set (Fin n → Fin (d + 1) → ℂ)) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hwFT, hwPFT⟩
    have hπ1 := permutedForwardTube_forces_perm_one (d := d) (n := n) π hwFT hwPFT
    exact (hπ hπ1).elim
  · intro hw
    exact hw.elim

/-- The permuted extended tube T''_n = ⋃_{π ∈ S_n} ⋃_{Λ ∈ L₊(ℂ)} Λ · π(T_n). -/
def PermutedExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = complexLorentzAction Λ w }

/-- The `π`-branch sector of PET, written as the pullback of the ordinary
extended tube by the coordinate permutation `π`. -/
def permutedExtendedTubeSector (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | (fun k => z (π k)) ∈ ExtendedTube d n}

/-- The forward tube is contained in the extended tube. -/
theorem forwardTube_subset_extendedTube :
    ForwardTube d n ⊆ ExtendedTube d n := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨1, z, hz, ?_⟩
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The extended tube is contained in the permuted extended tube. -/
theorem extendedTube_subset_permutedExtendedTube :
    ExtendedTube d n ⊆ PermutedExtendedTube d n := by
  intro z hz
  obtain ⟨Λ, w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨Equiv.refl _, Λ, w, ?_, hzw⟩
  show (fun k => w ((Equiv.refl _) k)) ∈ ForwardTube d n
  simp only [Equiv.refl_apply]
  exact hw

/-- The forward tube is contained in the permuted extended tube. -/
theorem forwardTube_subset_permutedExtendedTube :
    ForwardTube d n ⊆ PermutedExtendedTube d n :=
  fun _ hz => extendedTube_subset_permutedExtendedTube (forwardTube_subset_extendedTube hz)

/-- The Lorentz action z ↦ Λ·z is an open map (it's a homeomorphism). -/
theorem complexLorentzAction_isOpenMap (Λ : ComplexLorentzGroup d) :
    IsOpenMap (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) :=
  IsOpenMap.of_inverse
    (continuous_complexLorentzAction_snd Λ⁻¹)
    (fun z => by rw [← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one])
    (fun z => by rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one])

/-- The extended tube is open (union of Lorentz images of the open forward tube). -/
theorem isOpen_extendedTube : IsOpen (@ExtendedTube d n) := by
  suffices h : ExtendedTube d n =
      ⋃ Λ : ComplexLorentzGroup d,
        (fun z => complexLorentzAction Λ z) '' (ForwardTube d n) by
    rw [h]
    exact isOpen_iUnion (fun Λ =>
      (complexLorentzAction_isOpenMap Λ) _ isOpen_forwardTube)
  ext z
  simp only [ExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨Λ, w, hw, rfl⟩
    exact ⟨Λ, w, hw, rfl⟩
  · rintro ⟨Λ, w, hw, rfl⟩
    exact ⟨Λ, w, hw, rfl⟩

/-- The extended tube is connected (image of `G × FT` under the action map). -/
theorem isConnected_extendedTube : IsConnected (ExtendedTube d n) := by
  constructor
  · obtain ⟨w0, hw0⟩ := forwardTube_nonempty (d := d) (n := n)
    refine ⟨complexLorentzAction 1 w0, ?_⟩
    exact Set.mem_iUnion.mpr ⟨1, w0, hw0, by rw [complexLorentzAction_one]⟩
  · have hET_eq : ExtendedTube d n =
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) '' (Set.univ ×ˢ ForwardTube d n) := by
      ext z
      simp only [ExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq,
        Set.mem_image, Set.mem_prod, Set.mem_univ, true_and]
      constructor
      · rintro ⟨Λ, w, hw, rfl⟩
        exact ⟨⟨Λ, w⟩, hw, rfl⟩
      · rintro ⟨⟨Λ, w⟩, hw, rfl⟩
        exact ⟨Λ, w, hw, rfl⟩
    rw [hET_eq]
    have hcont : Continuous (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) := by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      simp only [complexLorentzAction]
      apply continuous_finset_sum
      intro ν _
      exact ((continuous_apply ν).comp ((continuous_apply μ).comp
        (ComplexLorentzGroup.continuous_val.comp continuous_fst))).mul
        ((continuous_apply ν).comp ((continuous_apply k).comp continuous_snd))
    haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
      pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
    exact (isPreconnected_univ.prod forwardTube_convex.isPreconnected).image _ hcont.continuousOn

/-- The permuted forward tube is open (preimage of FT under continuous permutation). -/
theorem isOpen_permutedForwardTube (π : Equiv.Perm (Fin n)) :
    IsOpen (PermutedForwardTube d n π) :=
  isOpen_forwardTube.preimage (continuous_pi (fun k =>
    continuous_pi (fun μ => (continuous_apply μ).comp (continuous_apply (π k)))))

/-- The permuted extended tube is open (union of images of open sets under homeomorphisms). -/
theorem isOpen_permutedExtendedTube :
    IsOpen (@PermutedExtendedTube d n) := by
  apply isOpen_iUnion
  intro π
  suffices h : { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧ z = complexLorentzAction Λ w } =
    ⋃ Λ : ComplexLorentzGroup d,
      (fun z => complexLorentzAction Λ z) '' (PermutedForwardTube d n π) by
    rw [h]
    exact isOpen_iUnion (fun Λ =>
      (complexLorentzAction_isOpenMap Λ) _ (isOpen_permutedForwardTube π))
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨Λ, w, hw, rfl⟩
    exact ⟨Λ, w, hw, rfl⟩
  · rintro ⟨Λ, w, hw, rfl⟩
    exact ⟨Λ, w, hw, rfl⟩

/-- Each explicit PET sector is open. -/
theorem isOpen_permutedExtendedTubeSector (π : Equiv.Perm (Fin n)) :
    IsOpen (permutedExtendedTubeSector d n π) := by
  have hcont : Continuous
      (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (π k)) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (π k))
  exact isOpen_extendedTube.preimage hcont

/-- The permuted extended tube is stable under complex Lorentz action. -/
theorem complexLorentzAction_mem_permutedExtendedTube
    {z : Fin n → Fin (d + 1) → ℂ} (hz : z ∈ PermutedExtendedTube d n)
    (Λ : ComplexLorentzGroup d) :
    complexLorentzAction Λ z ∈ PermutedExtendedTube d n := by
  obtain ⟨π, Λ', w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨π, Λ * Λ', w, hw, ?_⟩
  rw [hzw, complexLorentzAction_mul]

/-- Membership in the permuted extended tube is equivalently membership in one
permutation pullback of the ordinary extended tube.  This is the explicit
branch-cover form used by later gluing arguments. -/
theorem mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube :
    z ∈ PermutedExtendedTube d n ↔
      ∃ π : Equiv.Perm (Fin n), (fun k => z (π k)) ∈ ExtendedTube d n := by
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨π, Λ, w, hwπ, rfl⟩
    refine ⟨π, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Λ, ?_⟩
    refine ⟨fun k => w (π k), ?_, ?_⟩
    · simpa [PermutedForwardTube] using hwπ
    · ext k μ
      simp [complexLorentzAction]
  · rintro ⟨π, hπz⟩
    rcases Set.mem_iUnion.mp hπz with ⟨Λ, w, hw, hπz_eq⟩
    refine Set.mem_iUnion.mpr ⟨π, Λ, fun k => w (π.symm k), ?_, ?_⟩
    · simpa [PermutedForwardTube] using hw
    · ext k μ
      have hcoord := congrFun (congrFun hπz_eq (π.symm k)) μ
      simpa [complexLorentzAction] using hcoord

/-- The permuted extended tube is the union of its explicit permutation
pullback sectors. -/
theorem permutedExtendedTube_eq_iUnion_sectors :
    PermutedExtendedTube d n =
      ⋃ π : Equiv.Perm (Fin n), permutedExtendedTubeSector d n π := by
  ext z
  rw [mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube]
  simp [permutedExtendedTubeSector]

/-- An explicit sector is contained in PET. -/
theorem permutedExtendedTubeSector_subset_permutedExtendedTube
    (π : Equiv.Perm (Fin n)) :
    permutedExtendedTubeSector d n π ⊆ PermutedExtendedTube d n := by
  intro z hz
  rw [mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube]
  exact ⟨π, hz⟩

/-- A chosen permutation branch witnessing membership in the permuted extended
tube.  The accompanying theorem below is the preferred way to use this choice. -/
noncomputable def permutedExtendedTubeBranch
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    Equiv.Perm (Fin n) :=
  (mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube (d := d) (n := n)).1 hz |>.choose

/-- The chosen branch of a PET point lands in the ordinary extended tube. -/
theorem permutedExtendedTubeBranch_mem_extendedTube
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    (fun k => z (permutedExtendedTubeBranch (d := d) (n := n) z hz k)) ∈
      ExtendedTube d n :=
  (mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube (d := d) (n := n)).1 hz |>.choose_spec

end BHW
