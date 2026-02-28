import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetBasic
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d : ℕ}

/-- Subgroup stabilizer of `w` for the complex Lorentz action. -/
abbrev stabilizerSubgroup {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    Subgroup (ComplexLorentzGroup d) :=
  MulAction.stabilizer (ComplexLorentzGroup d) w

/-- Orbit quotient points whose represented configuration lies in the forward tube. -/
abbrev orbitQuotTube {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    Set (ComplexLorentzGroup d ⧸ stabilizerSubgroup w) :=
  {q | MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w q ∈ ForwardTube d n}

/-- Restrict the quotient projection to `orbitSet w`, landing in `orbitQuotTube w`. -/
abbrev orbitSetToQuotTube {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    orbitSet w → orbitQuotTube w :=
  fun Λ =>
    ⟨(QuotientGroup.mk (Λ : ComplexLorentzGroup d) :
      ComplexLorentzGroup d ⧸ stabilizerSubgroup w), by
      simpa [orbitQuotTube, MulAction.ofQuotientStabilizer_mk] using
        (show complexLorentzAction (Λ : ComplexLorentzGroup d) w ∈ ForwardTube d n from
          Λ.property)⟩

/-- Orbit subtype of `w` for the complex Lorentz action. -/
abbrev orbitSubtype {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :=
  MulAction.orbit (ComplexLorentzGroup d) w

/-- Orbit map with codomain the orbit subtype. -/
private abbrev orbitSubtypeMap {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    ComplexLorentzGroup d → orbitSubtype (d := d) w :=
  fun g => g • (⟨w, by exact MulAction.mem_orbit_self w⟩ : orbitSubtype (d := d) w)

/-- Forward-tube slice inside the orbit subtype. -/
private abbrev orbitTubeSubtype {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    Set (orbitSubtype (d := d) w) :=
  {y | y.1 ∈ ForwardTube d n}

/-- Restrict `orbitSubtypeMap` to `orbitSet`, landing in the forward-tube orbit slice. -/
private abbrev orbitSetToTubeSubtype {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    orbitSet w → orbitTubeSubtype (d := d) (n := n) w :=
  fun Λ => ⟨orbitSubtypeMap (d := d) w Λ, Λ.property⟩

private instance orbitSubtypeContinuousSMul {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    ContinuousSMul (ComplexLorentzGroup d) (orbitSubtype (d := d) w) where
  continuous_smul := by
    refine Continuous.subtype_mk
      (by
        simpa using
          (continuous_fst.smul (continuous_subtype_val.comp continuous_snd) :
            Continuous (fun p : ComplexLorentzGroup d × orbitSubtype (d := d) w => p.1 • p.2.1)))
      (by
        intro p
        rcases p.2.2 with ⟨g, hg⟩
        refine ⟨p.1 * g, ?_⟩
        rw [← hg]
        simp [smul_smul])

private instance orbitSubtypeIsPretransitive {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    MulAction.IsPretransitive (ComplexLorentzGroup d) (orbitSubtype (d := d) w) where
  exists_smul_eq := by
    intro x y
    rcases x.2 with ⟨gx, hgx⟩
    rcases y.2 with ⟨gy, hgy⟩
    refine ⟨gy * gx⁻¹, ?_⟩
    apply Subtype.ext
    calc
      (gy * gx⁻¹) • x.1 = (gy * gx⁻¹) • (gx • w) := by rw [← hgx]
      _ = gy • w := by simp [smul_smul]
      _ = y.1 := by simpa using hgy

private theorem orbitSubtypeMap_isQuotient {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    [BaireSpace (orbitSubtype (d := d) w)] :
    Topology.IsQuotientMap (orbitSubtypeMap (d := d) w) := by
  have hopen : IsOpenMap (orbitSubtypeMap (d := d) w) := by
    simpa [orbitSubtypeMap] using
      (isOpenMap_smul_of_sigmaCompact (G := ComplexLorentzGroup d)
        (X := orbitSubtype (d := d) w)
        (x := (⟨w, by exact MulAction.mem_orbit_self w⟩ : orbitSubtype (d := d) w)))
  have hcont : Continuous (orbitSubtypeMap (d := d) w) := by
    simpa [orbitSubtypeMap] using
      ((continuous_id : Continuous (fun g : ComplexLorentzGroup d => g)).smul continuous_const)
  have hsurj : Function.Surjective (orbitSubtypeMap (d := d) w) := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  exact hopen.isQuotientMap hcont hsurj

private theorem orbitTubeSubtype_isOpen {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    IsOpen (orbitTubeSubtype (d := d) (n := n) w) :=
  isOpen_forwardTube.preimage continuous_subtype_val

private theorem orbitSetToTubeSubtype_isQuotient {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    [BaireSpace (orbitSubtype (d := d) w)] :
    Topology.IsQuotientMap (orbitSetToTubeSubtype (d := d) (n := n) w) := by
  have hq : Topology.IsQuotientMap (orbitSubtypeMap (d := d) w) :=
    orbitSubtypeMap_isQuotient (d := d) (n := n) w
  have hs : IsOpen (orbitTubeSubtype (d := d) (n := n) w) :=
    orbitTubeSubtype_isOpen (d := d) (n := n) w
  simpa [orbitSetToTubeSubtype, orbitSet, orbitTubeSubtype, orbitSubtypeMap] using
    hq.restrictPreimage_isOpen hs

private theorem orbitImage_eq_ft_inter_orbitRange {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    orbitMap w '' orbitSet w =
      ForwardTube d n ∩
        Set.range (Subtype.val : orbitSubtype (d := d) w → (Fin n → Fin (d + 1) → ℂ)) := by
  ext z
  constructor
  · rintro ⟨Λ, hΛ, rfl⟩
    refine ⟨hΛ, ?_⟩
    refine ⟨⟨orbitMap w Λ, ?_⟩, rfl⟩
    refine ⟨Λ, ?_⟩
    rfl
  · rintro ⟨hzFT, ⟨y, rfl⟩⟩
    rcases y.2 with ⟨Λ, hΛ⟩
    have hmap : orbitMap w Λ = y.1 := by
      simpa [orbitMap] using hΛ
    have hΛFT : orbitMap w Λ ∈ ForwardTube d n := by
      simpa [hmap] using hzFT
    refine ⟨Λ, ?_, hmap⟩
    simpa [orbitSet] using hΛFT

/-- Baire-orbit reduction: if the orbit subtype through `w` is Baire, then the
restricted orbit map `orbitSet w → orbitMap w '' orbitSet w` is a quotient map. -/
theorem orbitSet_restricted_orbitMap_isQuotient_of_baireOrbit {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    [BaireSpace (orbitSubtype (d := d) w)] :
    Topology.IsQuotientMap (fun Λ : orbitSet w =>
      (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)) := by
  let f : orbitSubtype (d := d) w → (Fin n → Fin (d + 1) → ℂ) := Subtype.val
  have hf : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal
  let s : Set (Fin n → Fin (d + 1) → ℂ) :=
    ForwardTube d n ∩ Set.range (Subtype.val : orbitSubtype (d := d) w → (Fin n → Fin (d + 1) → ℂ))
  have hs : s ⊆ Set.range f := by
    intro z hz
    exact hz.2
  let hHomeo0 : (f ⁻¹' s) ≃ₜ s := hf.homeomorphOfSubsetRange hs
  have hdom_eq : f ⁻¹' s = orbitTubeSubtype (d := d) (n := n) w := by
    ext y
    constructor
    · intro hy
      simpa [orbitTubeSubtype, s, f] using hy.1
    · intro hy
      refine ⟨?_, ⟨y, rfl⟩⟩
      simpa [orbitTubeSubtype, s, f] using hy
  let hHomeo1 : orbitTubeSubtype (d := d) (n := n) w ≃ₜ s :=
    (Homeomorph.setCongr hdom_eq.symm).trans hHomeo0
  have himage_eq : s = orbitMap w '' orbitSet w := by
    simpa [s] using (orbitImage_eq_ft_inter_orbitRange (d := d) (n := n) w).symm
  let hHomeo : orbitTubeSubtype (d := d) (n := n) w ≃ₜ orbitMap w '' orbitSet w :=
    hHomeo1.trans (Homeomorph.setCongr himage_eq)
  have hHomeo_coe : ∀ y : orbitTubeSubtype (d := d) (n := n) w,
      ((hHomeo y : orbitMap w '' orbitSet w) : (Fin n → Fin (d + 1) → ℂ)) = y.1 := by
    intro y
    change ((Homeomorph.setCongr himage_eq (hHomeo1 y) : orbitMap w '' orbitSet w).1) = y.1
    change (hHomeo1 y).1 = y.1
    change (hHomeo0 ((Homeomorph.setCongr hdom_eq.symm y))).1 = y.1
    rfl
  let q : orbitSet w → orbitMap w '' orbitSet w :=
    fun Λ => ⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩
  have hq_eq : q = (hHomeo : orbitTubeSubtype (d := d) (n := n) w → orbitMap w '' orbitSet w) ∘
      orbitSetToTubeSubtype (d := d) (n := n) w := by
    funext Λ
    apply Subtype.ext
    simpa [q, orbitSetToTubeSubtype, orbitSubtypeMap, orbitMap] using
      (hHomeo_coe (orbitSetToTubeSubtype (d := d) (n := n) w Λ))
  have hq_comp : Topology.IsQuotientMap
      ((hHomeo : orbitTubeSubtype (d := d) (n := n) w → orbitMap w '' orbitSet w) ∘
        orbitSetToTubeSubtype (d := d) (n := n) w) :=
    Topology.IsQuotientMap.comp
      (hHomeo.isQuotientMap)
      (orbitSetToTubeSubtype_isQuotient (d := d) (n := n) w)
  simpa [q, hq_eq] using hq_comp

/-- Continuity of `ofQuotientStabilizer` for the Lorentz action follows from the
    quotient-map characterization of `QuotientGroup.mk`. -/
theorem continuous_ofQuotientStabilizer {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    Continuous (MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w) := by
  refine (QuotientGroup.isQuotientMap_mk (N := stabilizerSubgroup w)).continuous_iff.mpr ?_
  simpa [Function.comp, MulAction.ofQuotientStabilizer_mk] using
    (continuous_complexLorentzAction_fst w)

/-- The quotient by a stabilizer subgroup is a Baire space. -/
theorem baireSpace_quotientStabilizer {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    BaireSpace (ComplexLorentzGroup d ⧸ stabilizerSubgroup w) := by
  let hf : IsOpenQuotientMap
      (QuotientGroup.mk :
        ComplexLorentzGroup d →
          ComplexLorentzGroup d ⧸ stabilizerSubgroup w) :=
    QuotientGroup.isOpenQuotientMap_mk (N := stabilizerSubgroup w)
  exact IsOpenQuotientMap.baireSpace hf

/-- Continuity of the quotient-to-orbit map encoded by
`orbitEquivQuotientStabilizer.symm`. -/
theorem continuous_orbitEquivQuotientStabilizer_symm {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    Continuous ((MulAction.orbitEquivQuotientStabilizer
      (ComplexLorentzGroup d) w).symm) := by
  let g : ComplexLorentzGroup d ⧸ stabilizerSubgroup w →
      MulAction.orbit (ComplexLorentzGroup d) w :=
    (MulAction.orbitEquivQuotientStabilizer (ComplexLorentzGroup d) w).symm
  let f : ComplexLorentzGroup d ⧸ stabilizerSubgroup w →
      Fin n → Fin (d + 1) → ℂ :=
    MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w
  have hf : Continuous f := continuous_ofQuotientStabilizer (d := d) (n := n) w
  have hg_eq :
      g = fun q =>
        (⟨f q, MulAction.ofQuotientStabilizer_mem_orbit
          (ComplexLorentzGroup d) w q⟩ : MulAction.orbit (ComplexLorentzGroup d) w) := by
    funext q
    refine Quotient.inductionOn q ?_
    intro a
    apply Subtype.ext
    simp [g, f, MulAction.orbitEquivQuotientStabilizer_symm_apply,
      MulAction.ofQuotientStabilizer_mk]
  change Continuous g
  rw [hg_eq]
  exact hf.subtype_mk (fun q =>
    MulAction.ofQuotientStabilizer_mem_orbit (ComplexLorentzGroup d) w q)

/-- The quotient-tube subset is open in `G ⧸ Stab(w)`. -/
theorem isOpen_orbitQuotTube {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    IsOpen (orbitQuotTube w) := by
  exact isOpen_forwardTube.preimage (continuous_ofQuotientStabilizer (d := d) (n := n) w)

/-- The restricted quotient projection `orbitSet w → orbitQuotTube w` is a quotient map. -/
theorem orbitSetToQuotTube_isQuotient {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    Topology.IsQuotientMap (orbitSetToQuotTube (d := d) (n := n) w) := by
  let mkq : ComplexLorentzGroup d → ComplexLorentzGroup d ⧸ stabilizerSubgroup w :=
    QuotientGroup.mk
  have hqmk : Topology.IsQuotientMap mkq :=
    QuotientGroup.isQuotientMap_mk (N := stabilizerSubgroup w)
  have hopen : IsOpen (orbitQuotTube (d := d) (n := n) w) :=
    isOpen_orbitQuotTube (d := d) (n := n) w
  have hq_restrict : Topology.IsQuotientMap ((orbitQuotTube w).restrictPreimage mkq) :=
    hqmk.restrictPreimage_isOpen hopen
  simpa [orbitSetToQuotTube, orbitSet, orbitQuotTube, mkq, stabilizerSubgroup,
    MulAction.ofQuotientStabilizer_mk] using hq_restrict

/-- The set-based stabilizer predicate agrees with the subgroup carrier. -/
lemma stabilizer_eq_subgroup_carrier {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    stabilizer w = (stabilizerSubgroup w : Set (ComplexLorentzGroup d)) := by
  ext g
  rfl

/-- Quotient-tube reduction: connected stabilizer + preconnected quotient-tube codomain
    imply preconnectedness of `orbitSet w`. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected_quotTube {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    [PreconnectedSpace (orbitQuotTube w)] :
    IsPreconnected (orbitSet w) := by
  have hquot : Topology.IsQuotientMap (orbitSetToQuotTube (d := d) (n := n) w) :=
    orbitSetToQuotTube_isQuotient (d := d) (n := n) w
  have hFib : ∀ y : orbitQuotTube w,
      IsConnected ((orbitSetToQuotTube (d := d) (n := n) w) ⁻¹' ({y} : Set _)) := by
    intro y
    let Λy : ComplexLorentzGroup d := Quotient.out y.1
    have hΛy : (QuotientGroup.mk Λy : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) = y.1 :=
      Quotient.out_eq y.1
    set A : Set (ComplexLorentzGroup d) :=
      {Λ | (QuotientGroup.mk Λ : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) = y.1} with hA_def
    have hA_sub : A ⊆ orbitSet w := by
      intro Λ hΛA
      have hyFT : MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w y.1
          ∈ ForwardTube d n := y.2
      have hyFT_mk :
          MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w
            (QuotientGroup.mk Λ : ComplexLorentzGroup d ⧸ stabilizerSubgroup w)
            ∈ ForwardTube d n := by
        simpa [hΛA.symm] using hyFT
      simpa [orbitSet, MulAction.ofQuotientStabilizer_mk] using hyFT_mk
    have hA_eq_coset_image :
        A = (fun g : stabilizer w => Λy * g.1) '' Set.univ := by
      ext Λ
      constructor
      · intro hΛA
        have hmk : (QuotientGroup.mk Λy : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) =
            (QuotientGroup.mk Λ : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) := by
          simpa [hΛy] using hΛA.symm
        have hrel : Λy⁻¹ * Λ ∈ stabilizerSubgroup w :=
          (QuotientGroup.eq).mp hmk
        refine ⟨⟨Λy⁻¹ * Λ, ?_⟩, Set.mem_univ _, ?_⟩
        · simpa [stabilizer_eq_subgroup_carrier (d := d) (n := n) w] using hrel
        · simp
      · rintro ⟨g, -, rfl⟩
        have hg_sub : (g.1 : ComplexLorentzGroup d) ∈ stabilizerSubgroup w := by
          simp
        have hmk_eq :
            (QuotientGroup.mk (Λy * (g.1 : ComplexLorentzGroup d)) :
              ComplexLorentzGroup d ⧸ stabilizerSubgroup w) =
            QuotientGroup.mk Λy := by
          exact (QuotientGroup.eq).2 (by simp [hg_sub])
        simp [A, hΛy]
    have hA_conn : IsConnected A := by
      let f : stabilizer w → ComplexLorentzGroup d := fun g => Λy * g.1
      have hf_cont : Continuous f := by
        exact continuous_const.mul continuous_subtype_val
      have hIm_conn : IsConnected (f '' (Set.univ : Set (stabilizer w))) := by
        letI : ConnectedSpace (stabilizer w) := Subtype.connectedSpace hstab_conn
        simpa [f] using (isConnected_univ.image f hf_cont.continuousOn)
      simpa [hA_eq_coset_image, f] using hIm_conn
    let incl : A → orbitSet w := fun g => ⟨g.1, hA_sub g.2⟩
    have h_incl_cont : Continuous incl :=
      continuous_subtype_val.subtype_mk (fun g => hA_sub g.2)
    have h_range_conn : IsConnected (Set.range incl) := by
      letI : ConnectedSpace A := Subtype.connectedSpace hA_conn
      exact isConnected_range h_incl_cont
    have h_range_eq :
        Set.range incl =
          ((orbitSetToQuotTube (d := d) (n := n) w) ⁻¹' ({y} : Set _)) := by
      ext Λ
      constructor
      · rintro ⟨g, rfl⟩
        rcases g with ⟨g, hgA⟩
        apply Subtype.ext
        simpa [orbitSetToQuotTube, A] using hgA
      · intro hΛ
        have hmk :
            (QuotientGroup.mk (Λ : ComplexLorentzGroup d) :
              ComplexLorentzGroup d ⧸ stabilizerSubgroup w) = y.1 := by
          exact congrArg Subtype.val hΛ
        have hΛA : (Λ : ComplexLorentzGroup d) ∈ A := by
          simpa [A] using hmk
        refine ⟨⟨(Λ : ComplexLorentzGroup d), hΛA⟩, ?_⟩
        ext
        rfl
    simpa [h_range_eq] using h_range_conn
  haveI : Nonempty (orbitSet w) :=
    ⟨⟨1, by simpa [orbitSet, complexLorentzAction_one] using hw⟩⟩
  haveI : PreconnectedSpace (orbitSet w) :=
    IsQuotientMap.preconnectedSpace_of_connectedFibers
      (f := orbitSetToQuotTube (d := d) (n := n) w) hquot hFib
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- If the stabilizer is connected and the restricted orbit map is quotient onto a
    preconnected image, then a nonempty orbit set is preconnected.

    This discharges the fiber-connectedness premise in
    `orbitSet_isPreconnected_of_quotientData_nonempty` from stabilizer connectedness via
    the explicit coset description of orbit-map fibers. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected_nonempty {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (hne : Nonempty (orbitSet w))
    (hstab_conn : IsConnected (stabilizer w))
    (hquot : Topology.IsQuotientMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  refine orbitSet_isPreconnected_of_quotientData_nonempty (d := d) (n := n) w hne hquot ?_
  intro y
  rcases y with ⟨yval, hyim⟩
  rcases hyim with ⟨Λy, hΛy_orbit, rfl⟩
  set A : Set (ComplexLorentzGroup d) :=
    (orbitMap w) ⁻¹' ({orbitMap w Λy} : Set (Fin n → Fin (d + 1) → ℂ)) with hA_def
  have hyFT : orbitMap w Λy ∈ ForwardTube d n := by
    simpa [orbitSet, orbitMap] using hΛy_orbit
  have hA_sub : A ⊆ orbitSet w := by
    intro g hgA
    have hgEq : orbitMap w g = orbitMap w Λy := by
      simpa [A, Set.mem_preimage, Set.mem_singleton_iff] using hgA
    have hgEq' : complexLorentzAction g w = complexLorentzAction Λy w := by
      simpa [orbitMap] using hgEq
    change complexLorentzAction g w ∈ ForwardTube d n
    rw [hgEq']
    exact hyFT
  have hA_pre : IsPreconnected A := by
    have hA' := fiber_orbitMap_isPreconnected_of_stabilizer (d := d) (n := n) w
      hstab_conn.isPreconnected Λy
    simpa [A] using hA'
  have hA_nonempty : A.Nonempty := ⟨Λy, by simp [A]⟩
  have hA_conn : IsConnected A := ⟨hA_nonempty, hA_pre⟩
  let incl : A → orbitSet w := fun g => ⟨g.1, hA_sub g.2⟩
  have h_incl_cont : Continuous incl :=
    continuous_subtype_val.subtype_mk (fun g => hA_sub g.2)
  have h_range_conn : IsConnected (Set.range incl) := by
    letI : ConnectedSpace A := Subtype.connectedSpace hA_conn
    exact isConnected_range h_incl_cont
  let y0 : orbitMap w '' orbitSet w := ⟨orbitMap w Λy, ⟨Λy, hΛy_orbit, rfl⟩⟩
  have h_range_eq :
      Set.range incl =
        ((fun Λ : orbitSet w =>
            (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ :
              orbitMap w '' orbitSet w)) ⁻¹' ({y0} : Set _)) := by
    ext Λ
    constructor
    · rintro ⟨g, rfl⟩
      rcases g with ⟨g, hg⟩
      apply Subtype.ext
      have hgEq : orbitMap w g = orbitMap w Λy := by
        simpa [A, Set.mem_preimage, Set.mem_singleton_iff] using hg
      simpa [incl] using hgEq
    · intro hΛ
      have hEq : orbitMap w (Λ : ComplexLorentzGroup d) = orbitMap w Λy := by
        exact congrArg Subtype.val hΛ
      have hΛA : (Λ : ComplexLorentzGroup d) ∈ A := by
        simpa [A, Set.mem_preimage, Set.mem_singleton_iff] using hEq
      refine ⟨⟨(Λ : ComplexLorentzGroup d), hΛA⟩, ?_⟩
      ext
      rfl
  simpa [h_range_eq, y0] using h_range_conn

/-- If the stabilizer is connected and the restricted orbit map is quotient onto a
    preconnected image, then the orbit set is preconnected. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    (hquot : Topology.IsQuotientMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  have hne : Nonempty (orbitSet w) := ⟨⟨1, by simpa [orbitSet, complexLorentzAction_one] using hw⟩⟩
  exact orbitSet_isPreconnected_of_stabilizer_connected_nonempty
    (d := d) (n := n) w hne hstab_conn hquot

/-- Combined reduction for orbit-set preconnectedness:
    connected stabilizer + preconnected orbit image + openness of the global orbit map. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected_and_openOrbitMap {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    (hopen : IsOpenMap (orbitMap w))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  have hopen_restr :=
    orbitMap_restricted_isOpen_of_global (d := d) (n := n) w hopen
  have hquot :=
    orbitSet_restricted_orbitMap_isQuotient (d := d) (n := n) w
      (hopen_restr.subtype_mk (fun Λ => ⟨Λ, Λ.property, rfl⟩))
  exact orbitSet_isPreconnected_of_stabilizer_connected (d := d) (n := n) w hw hstab_conn hquot

/-- Baire-orbit reduction of the orbit-set preconnectedness criterion:
connected stabilizer + Baire orbit subtype + preconnected orbit image. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected_and_baireOrbit {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    [BaireSpace (orbitSubtype (d := d) w)]
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  have hquot :=
    orbitSet_restricted_orbitMap_isQuotient_of_baireOrbit (d := d) (n := n) w
  exact orbitSet_isPreconnected_of_stabilizer_connected (d := d) (n := n) w hw hstab_conn hquot

/-- Transport orbit-set preconnectedness from a forward-tube witness `u` to an
ET point `z = Δ • u`.

This is useful when ET-membership provides an explicit FT preimage and the orbit
preconnectedness machinery is available at that witness. -/
theorem orbitSet_isPreconnected_of_forwardTube_witness {n : ℕ}
    (z u : Fin n → Fin (d + 1) → ℂ)
    (Δ : ComplexLorentzGroup d)
    (hu : u ∈ ForwardTube d n)
    (hz_eq : z = complexLorentzAction Δ u)
    (hstab_conn : IsConnected (stabilizer z))
    [BaireSpace (orbitSubtype (d := d) u)]
    [PreconnectedSpace (orbitMap u '' orbitSet u)] :
    IsPreconnected (orbitSet z) := by
  have hzu : u = complexLorentzAction Δ⁻¹ z := by
    simp [hz_eq, complexLorentzAction_inv]
  have hstab_u : IsConnected (stabilizer u) := by
    have hstab_u' : IsConnected (stabilizer (complexLorentzAction Δ⁻¹ z)) :=
      isConnected_stabilizer_of_conj (d := d) (n := n) (w := z) Δ⁻¹ hstab_conn
    simpa [hzu] using hstab_u'
  have hpre_u : IsPreconnected (orbitSet u) :=
    orbitSet_isPreconnected_of_stabilizer_connected_and_baireOrbit
      (d := d) (n := n) u hu hstab_u
  exact orbitSet_isPreconnected_of_orbit_eq (d := d) (n := n) u z Δ hz_eq hpre_u

end BHW
