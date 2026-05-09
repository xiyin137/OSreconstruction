import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJost

/-!
# OS45 local BHW/Jost hull geometry

This file starts the non-source-descent local BHW/Jost carrier for the strict
OS II / OS I §4.5 route.  It contains only the concrete proper-complex
Lorentz saturation and path-component geometry used by the later local
Bargmann-Hall-Wightman continuation theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Proper-complex Lorentz saturation of the identity extended tube and the
selected adjacent permuted extended-tube sector.  This is the local OS I §4.5
BHW/Jost ambient; it is not global PET branch independence. -/
def os45BHWJostAmbient
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
      u ∈ BHW.ExtendedTube d n ∧ z = BHW.complexLorentzAction Λ u} ∪
    {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
      u ∈ BHW.permutedExtendedTubeSector d n τ ∧
        z = BHW.complexLorentzAction Λ u}

/-- The local BHW/Jost hull is the path component of the concrete ambient. -/
def os45BHWJostHull
    (d n : ℕ) (τ : Equiv.Perm (Fin n))
    (zbase : Fin n → Fin (d + 1) → ℂ) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  pathComponentIn (BHW.os45BHWJostAmbient d n τ) zbase

/-- Points of the ordinary extended tube lie in the local BHW/Jost ambient. -/
theorem os45BHWJostAmbient_mem_identity
    (τ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ BHW.ExtendedTube d n) :
    z ∈ BHW.os45BHWJostAmbient d n τ := by
  exact Or.inl ⟨1, z, hz, (BHW.complexLorentzAction_one z).symm⟩

/-- Points of the selected adjacent permuted sector lie in the local
BHW/Jost ambient. -/
theorem os45BHWJostAmbient_mem_adjacent
    (τ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ BHW.permutedExtendedTubeSector d n τ) :
    z ∈ BHW.os45BHWJostAmbient d n τ := by
  exact Or.inr ⟨1, z, hz, (BHW.complexLorentzAction_one z).symm⟩

private theorem isOpen_complexLorentz_saturation
    {S : Set (Fin n → Fin (d + 1) → ℂ)}
    (hS : IsOpen S) :
    IsOpen
      {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
        u ∈ S ∧ z = BHW.complexLorentzAction Λ u} := by
  have hset :
      {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
        u ∈ S ∧ z = BHW.complexLorentzAction Λ u} =
        ⋃ Λ : ComplexLorentzGroup d,
          (fun u : Fin n → Fin (d + 1) → ℂ =>
            BHW.complexLorentzAction Λ u) '' S := by
    ext z
    constructor
    · rintro ⟨Λ, u, hu, rfl⟩
      exact Set.mem_iUnion.mpr ⟨Λ, u, hu, rfl⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨Λ, u, hu, rfl⟩
      exact ⟨Λ, u, hu, rfl⟩
  rw [hset]
  exact isOpen_iUnion fun Λ =>
    (BHW.complexLorentzAction_isOpenMap Λ) S hS

/-- The local BHW/Jost ambient is open. -/
theorem os45BHWJostAmbient_open
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    IsOpen (BHW.os45BHWJostAmbient d n τ) := by
  exact
    (isOpen_complexLorentz_saturation
      (d := d) (n := n) BHW.isOpen_extendedTube).union
      (isOpen_complexLorentz_saturation
        (d := d) (n := n)
        (BHW.isOpen_permutedExtendedTubeSector
          (d := d) (n := n) τ))

/-- The base point belongs to its local BHW/Jost hull once it lies in the
ambient. -/
theorem mem_os45BHWJostHull_self
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    zbase ∈ BHW.os45BHWJostHull d n τ zbase := by
  simpa [BHW.os45BHWJostHull] using
    (mem_pathComponentIn_self hzbase)

/-- The local BHW/Jost hull is contained in its concrete ambient. -/
theorem os45BHWJostHull_subset_ambient
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ) :
    BHW.os45BHWJostHull d n τ zbase ⊆
      BHW.os45BHWJostAmbient d n τ := by
  intro z hz
  exact hz.target_mem

/-- The local BHW/Jost hull is nonempty when its base point lies in the
ambient. -/
theorem os45BHWJostHull_nonempty
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    (BHW.os45BHWJostHull d n τ zbase).Nonempty :=
  ⟨zbase, BHW.mem_os45BHWJostHull_self
    (d := d) (n := n) τ zbase hzbase⟩

/-- The local BHW/Jost hull is path-connected when its base point lies in the
ambient. -/
theorem os45BHWJostHull_isPathConnected
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    IsPathConnected (BHW.os45BHWJostHull d n τ zbase) := by
  simpa [BHW.os45BHWJostHull] using
    (isPathConnected_pathComponentIn hzbase)

/-- The local BHW/Jost hull is connected when its base point lies in the
ambient. -/
theorem os45BHWJostHull_connected
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    IsConnected (BHW.os45BHWJostHull d n τ zbase) :=
  (BHW.os45BHWJostHull_isPathConnected
    (d := d) (n := n) τ zbase hzbase).isConnected

/-- The local BHW/Jost hull is open when its base point lies in the
ambient. -/
theorem os45BHWJostHull_open
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    IsOpen (BHW.os45BHWJostHull d n τ zbase) :=
  BHW.isOpen_pathComponentIn_of_isOpen_normed
    (BHW.os45BHWJostAmbient_open d n τ) hzbase

/-- Any ordinary extended-tube point lies in the local BHW/Jost hull based at
an ordinary extended-tube point. -/
theorem mem_os45BHWJostHull_of_extendedTube
    (τ : Equiv.Perm (Fin n))
    {zbase z : Fin n → Fin (d + 1) → ℂ}
    (hzbase : zbase ∈ BHW.ExtendedTube d n)
    (hz : z ∈ BHW.ExtendedTube d n) :
    z ∈ BHW.os45BHWJostHull d n τ zbase := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined : JoinedIn (BHW.ExtendedTube d n) zbase z :=
    hpath.joinedIn zbase hzbase z hz
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) τ hw)

/-- Any selected adjacent-sector point lies in the local BHW/Jost hull based
at a selected adjacent-sector point. -/
theorem mem_os45BHWJostHull_of_permutedExtendedTubeSector
    (τ : Equiv.Perm (Fin n))
    {zbase z : Fin n → Fin (d + 1) → ℂ}
    (hzbase : zbase ∈ BHW.permutedExtendedTubeSector d n τ)
    (hz : z ∈ BHW.permutedExtendedTubeSector d n τ) :
    z ∈ BHW.os45BHWJostHull d n τ zbase := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hconn :
      IsConnected (BHW.permutedExtendedTubeSector d n τ) :=
    ⟨⟨zbase, hzbase⟩,
      BHW.permutedExtendedTubeSector_isPreconnected
        (d := d) (n := n) τ⟩
  have hpath :
      IsPathConnected (BHW.permutedExtendedTubeSector d n τ) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.permutedExtendedTubeSector d n τ)
      (BHW.isOpen_permutedExtendedTubeSector
        (d := d) (n := n) τ)).mp hconn
  have hjoined :
      JoinedIn (BHW.permutedExtendedTubeSector d n τ) zbase z :=
    hpath.joinedIn zbase hzbase z hz
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_adjacent
      (d := d) (n := n) τ hw)

end BHW
