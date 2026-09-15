/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetBasic
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d : ℕ}

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
        change Continuous
          (fun p : ComplexLorentzGroup d × orbitSubtype (d := d) w => p.1 • p.2.1)
        rw [show (fun p : ComplexLorentzGroup d × orbitSubtype (d := d) w => p.1 • p.2.1) =
            (fun p : ComplexLorentzGroup d × orbitSubtype (d := d) w => p.1) •
              (fun p : ComplexLorentzGroup d × orbitSubtype (d := d) w => p.2.1) by
          funext p
          rfl]
        exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
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
    change Continuous (fun g : ComplexLorentzGroup d =>
      g • (⟨w, by exact MulAction.mem_orbit_self w⟩ : orbitSubtype (d := d) w))
    rw [show (fun g : ComplexLorentzGroup d =>
        g • (⟨w, by exact MulAction.mem_orbit_self w⟩ : orbitSubtype (d := d) w)) =
        (fun g : ComplexLorentzGroup d => g) •
          (fun _ => (⟨w, by exact MulAction.mem_orbit_self w⟩ : orbitSubtype (d := d) w)) by
      funext g
      rfl]
    exact (continuous_id : Continuous (fun g : ComplexLorentzGroup d => g)).smul continuous_const
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
  have hqr := hq.restrictPreimage_isOpen hs
  change Topology.IsQuotientMap (orbitSetToTubeSubtype (d := d) (n := n) w) at hqr
  exact hqr

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
      change complexLorentzAction Λ w = y.1 at hΛ
      exact hΛ
    have hΛFT : orbitMap w Λ ∈ ForwardTube d n := by
      simpa [hmap] using hzFT
    refine ⟨Λ, ?_, hmap⟩
    change complexLorentzAction Λ w ∈ ForwardTube d n
    exact hΛFT

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
    have hcoe := (hHomeo_coe (orbitSetToTubeSubtype (d := d) (n := n) w Λ)).symm
    change complexLorentzAction (Λ : ComplexLorentzGroup d) w = _ at hcoe
    simpa [q, orbitSetToTubeSubtype, orbitSubtypeMap, orbitMap] using hcoe
  have hq_comp : Topology.IsQuotientMap
      ((hHomeo : orbitTubeSubtype (d := d) (n := n) w → orbitMap w '' orbitSet w) ∘
        orbitSetToTubeSubtype (d := d) (n := n) w) :=
    Topology.IsQuotientMap.comp
      (hHomeo.isQuotientMap)
      (orbitSetToTubeSubtype_isQuotient (d := d) (n := n) w)
  simpa [q, hq_eq] using hq_comp

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

end BHW
