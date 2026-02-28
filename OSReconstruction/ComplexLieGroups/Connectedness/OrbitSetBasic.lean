import OSReconstruction.ComplexLieGroups.Connectedness.Action
import OSReconstruction.ComplexLieGroups.Connectedness.Topology
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesSCV

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d : ℕ}

/-- The orbit set U_z = {Λ : Λ·z ∈ ForwardTube} is the set of complex Lorentz
    transformations that keep z in the forward tube. -/
def orbitSet {n : ℕ} (z : Fin n → Fin (d + 1) → ℂ) : Set (ComplexLorentzGroup d) :=
  { Λ | complexLorentzAction Λ z ∈ ForwardTube d n }

/-- Orbit map at a fixed configuration `w`. -/
def orbitMap {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    ComplexLorentzGroup d → (Fin n → Fin (d + 1) → ℂ) :=
  fun Λ => complexLorentzAction Λ w

/-- Stabilizer of `w` under the complex Lorentz action. -/
def stabilizer {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) : Set (ComplexLorentzGroup d) :=
  {g | complexLorentzAction g w = w}

lemma stabilizer_contains_one {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    (1 : ComplexLorentzGroup d) ∈ stabilizer w := by
  simp [stabilizer, complexLorentzAction_one]

lemma stabilizer_closed {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    IsClosed (stabilizer w) := by
  have h1 : Continuous (orbitMap w) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    simp only [orbitMap, complexLorentzAction]
    exact continuous_finset_sum Finset.univ
      (fun ν _ => (ComplexLorentzGroup.continuous_entry μ ν).mul continuous_const)
  have h2 : Continuous (fun _ : ComplexLorentzGroup d => w) := continuous_const
  simpa [stabilizer, orbitMap] using isClosed_eq h1 h2

/-- Stabilizers are conjugate along the orbit: `Stab(Γ·w) = Γ Stab(w) Γ⁻¹`. -/
theorem stabilizer_eq_conj_image {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (Γ : ComplexLorentzGroup d) :
    stabilizer (complexLorentzAction Γ w) =
      (fun g : ComplexLorentzGroup d => Γ * g * Γ⁻¹) '' stabilizer w := by
  ext h
  constructor
  · intro hh
    refine ⟨Γ⁻¹ * h * Γ, ?_, ?_⟩
    · change complexLorentzAction (Γ⁻¹ * h * Γ) w = w
      calc
        complexLorentzAction (Γ⁻¹ * h * Γ) w
            = complexLorentzAction Γ⁻¹
                (complexLorentzAction h (complexLorentzAction Γ w)) := by
                  simp [complexLorentzAction_mul, mul_assoc]
        _ = complexLorentzAction Γ⁻¹ (complexLorentzAction Γ w) := by
              simpa [stabilizer] using congrArg (complexLorentzAction Γ⁻¹) hh
        _ = w := by simp [complexLorentzAction_inv]
    · simp [mul_assoc]
  · rintro ⟨g, hg, rfl⟩
    change complexLorentzAction (Γ * g * Γ⁻¹) (complexLorentzAction Γ w) =
      complexLorentzAction Γ w
    calc
      complexLorentzAction (Γ * g * Γ⁻¹) (complexLorentzAction Γ w)
          = complexLorentzAction Γ (complexLorentzAction g w) := by
              simp [complexLorentzAction_mul, mul_assoc, complexLorentzAction_inv]
      _ = complexLorentzAction Γ w := by
            simp [stabilizer] at hg
            simpa using congrArg (complexLorentzAction Γ) hg

/-- Connectedness of stabilizers is invariant along the orbit. -/
theorem isConnected_stabilizer_of_conj {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (Γ : ComplexLorentzGroup d)
    (hconn : IsConnected (stabilizer w)) :
    IsConnected (stabilizer (complexLorentzAction Γ w)) := by
  rw [stabilizer_eq_conj_image (d := d) (n := n) w Γ]
  have hcont : Continuous (fun g : ComplexLorentzGroup d => Γ * g * Γ⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact hconn.image _ hcont.continuousOn

/-- Fiber of the orbit map through `Λ·w` is the left coset `Λ * stabilizer(w)`. -/
lemma fiber_orbitMap_eq_leftCoset_image_stabilizer {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (Λ : ComplexLorentzGroup d) :
    (orbitMap w) ⁻¹' ({orbitMap w Λ} : Set (Fin n → Fin (d + 1) → ℂ)) =
      (fun g : ComplexLorentzGroup d => Λ * g) '' stabilizer w := by
  ext g
  constructor
  · intro hg
    have hgw : orbitMap w g = orbitMap w Λ := by
      simpa [Set.mem_preimage, orbitMap] using hg
    refine ⟨Λ⁻¹ * g, ?_, ?_⟩
    · have : complexLorentzAction (Λ⁻¹ * g) w = w := by
        calc
          complexLorentzAction (Λ⁻¹ * g) w
              = complexLorentzAction Λ⁻¹ (complexLorentzAction g w) := by
                rw [complexLorentzAction_mul]
          _ = complexLorentzAction Λ⁻¹ (complexLorentzAction Λ w) := by
                simpa [orbitMap] using congrArg (complexLorentzAction Λ⁻¹) hgw
          _ = w := by rw [complexLorentzAction_inv]
      simpa [stabilizer] using this
    · simp
  · rintro ⟨h, hhstab, rfl⟩
    change orbitMap w (Λ * h) ∈ ({orbitMap w Λ} : Set (Fin n → Fin (d + 1) → ℂ))
    simp [Set.mem_singleton_iff, orbitMap, complexLorentzAction_mul, stabilizer] at hhstab ⊢
    simp [hhstab]

lemma fiber_orbitMap_isPreconnected_of_stabilizer {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (hstab : IsPreconnected (stabilizer w)) (Λ : ComplexLorentzGroup d) :
    IsPreconnected ((orbitMap w) ⁻¹' ({orbitMap w Λ} : Set (Fin n → Fin (d + 1) → ℂ))) := by
  rw [fiber_orbitMap_eq_leftCoset_image_stabilizer (w := w) (Λ := Λ)]
  have hcont : Continuous (fun g : ComplexLorentzGroup d => Λ * g) := by
    have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
    rw [hind.continuous_iff]
    exact continuous_const.mul ComplexLorentzGroup.continuous_val
  exact hstab.image _ hcont.continuousOn

/-- Reduction principle for orbit-set preconnectedness via quotient-map fibers. -/
theorem orbitSet_isPreconnected_of_quotientData {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hquot : Topology.IsQuotientMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)))
    (hFib : ∀ y : (orbitMap w '' orbitSet w),
      IsConnected ((fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)) ⁻¹' ({y} : Set _)))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  haveI : Nonempty (orbitSet w) := ⟨⟨1, by simpa [orbitSet, complexLorentzAction_one] using hw⟩⟩
  haveI : PreconnectedSpace (orbitSet w) :=
    IsQuotientMap.preconnectedSpace_of_connectedFibers
      (f := fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)) hquot hFib
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- Reduction principle for orbit-set preconnectedness via quotient-map fibers,
with explicit nonemptiness of the orbit set. -/
theorem orbitSet_isPreconnected_of_quotientData_nonempty {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (hne : Nonempty (orbitSet w))
    (hquot : Topology.IsQuotientMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)))
    (hFib : ∀ y : (orbitMap w '' orbitSet w),
      IsConnected ((fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)) ⁻¹' ({y} : Set _)))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  haveI : Nonempty (orbitSet w) := hne
  haveI : PreconnectedSpace (orbitSet w) :=
    IsQuotientMap.preconnectedSpace_of_connectedFibers
      (f := fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)) hquot hFib
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- The orbit set contains the identity. -/
theorem mem_orbitSet_one {n : ℕ} {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ForwardTube d n) :
    (1 : ComplexLorentzGroup d) ∈ orbitSet z := by
  rw [orbitSet, Set.mem_setOf_eq, complexLorentzAction_one]
  exact hz

/-- The forward tube is open (strict inequalities on continuous functions). -/
theorem isOpen_forwardTube {n : ℕ} : IsOpen (ForwardTube d n) := by
  simpa [ForwardTube] using (BHWCore.isOpen_forwardTube (d := d) (n := n))

/-- The action map Λ ↦ Λ·z is continuous (polynomial in entries of Λ). -/
theorem continuous_complexLorentzAction_fst {n : ℕ} (z : Fin n → Fin (d + 1) → ℂ) :
    Continuous (fun Λ : ComplexLorentzGroup d => complexLorentzAction Λ z) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => (ComplexLorentzGroup.continuous_entry μ ν).mul continuous_const)

/-- The orbit set is open (preimage of an open set under a continuous map). -/
theorem isOpen_orbitSet {n : ℕ} (z : Fin n → Fin (d + 1) → ℂ) :
    IsOpen (orbitSet z) :=
  isOpen_forwardTube.preimage (continuous_complexLorentzAction_fst z)

/-- Orbit-set transport along an orbit relation:
`orbitSet (Γ • w0)` is the right-translate image of `orbitSet w0`. -/
theorem orbitSet_eq_image_mul_right_inv {n : ℕ}
    (w0 w : Fin n → Fin (d + 1) → ℂ)
    (Γ : ComplexLorentzGroup d)
    (hEq : w = complexLorentzAction Γ w0) :
    orbitSet w =
      (fun Λ : ComplexLorentzGroup d => Λ * Γ⁻¹) '' orbitSet w0 := by
  ext Λ
  constructor
  · intro hΛ
    refine ⟨Λ * Γ, ?_, ?_⟩
    · simpa [orbitSet, hEq, complexLorentzAction_mul, mul_assoc] using hΛ
    · simp [mul_assoc]
  · rintro ⟨Λ0, hΛ0, rfl⟩
    simpa [orbitSet, hEq, complexLorentzAction_mul, mul_assoc, complexLorentzAction_inv] using hΛ0

/-- Preconnectedness transport along an orbit relation. -/
theorem orbitSet_isPreconnected_of_orbit_eq {n : ℕ}
    (w0 w : Fin n → Fin (d + 1) → ℂ)
    (Γ : ComplexLorentzGroup d)
    (hEq : w = complexLorentzAction Γ w0)
    (hpre0 : IsPreconnected (orbitSet w0)) :
    IsPreconnected (orbitSet w) := by
  rw [orbitSet_eq_image_mul_right_inv (d := d) (n := n) w0 w Γ hEq]
  have hcont : Continuous (fun Λ : ComplexLorentzGroup d => Λ * Γ⁻¹) :=
    continuous_mul_right Γ⁻¹
  exact hpre0.image _ hcont.continuousOn

/-- If the global orbit map is open, then its restriction to `orbitSet w` is open. -/
theorem orbitMap_restricted_isOpen_of_global {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (hopen : IsOpenMap (orbitMap w)) :
    IsOpenMap (fun Λ : orbitSet w => orbitMap w Λ) := by
  simpa [orbitMap] using
    hopen.comp ((isOpen_orbitSet (d := d) (n := n) w).isOpenMap_subtype_val)

/-- Open orbit map into its image implies the quotient-map hypothesis used in the
    orbit-set preconnectedness reduction. -/
theorem orbitSet_restricted_orbitMap_isQuotient {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ)
    (hopen_restr : IsOpenMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w))) :
    Topology.IsQuotientMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)) := by
  let φ : orbitSet w → orbitMap w '' orbitSet w :=
    fun Λ => ⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩
  have hsurj : Function.Surjective φ := by
    intro y
    rcases y.property with ⟨Λ, hΛ, hy⟩
    refine ⟨⟨Λ, hΛ⟩, ?_⟩
    apply Subtype.ext
    simpa [φ] using hy
  have hcont_orbit_restr : Continuous (fun Λ : orbitSet w => orbitMap w Λ) :=
    (continuous_complexLorentzAction_fst w).comp continuous_subtype_val
  have hcont : Continuous φ := by
    exact hcont_orbit_restr.subtype_mk (fun Λ => ⟨Λ, Λ.property, rfl⟩)
  simpa [φ] using hopen_restr.isQuotientMap hcont hsurj

end BHW
