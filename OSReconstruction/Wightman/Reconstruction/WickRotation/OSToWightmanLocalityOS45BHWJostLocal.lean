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

/-- The selected adjacent Wick edge is joined to the checked Figure-2-4
rotated lift inside the local BHW/Jost ambient. -/
theorem os45Figure24_joined_adjacentWick_to_adjLift0
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (fun k => wickRotatePoint (x (P.τ k)))
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval)) := by
  classical
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  have hzlift_ET : zlift ∈ BHW.ExtendedTube d n := by
    simpa [zlift] using
      P.adjLift_mem_extendedTube x hx (0 : unitInterval)
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x (0 : unitInterval)
  have hInv :
      BHW.complexLorentzAction Λinv zlift = zadj := by
    have hraw :
        BHW.complexLorentzAction Λinv zlift =
          BHW.permAct (d := d) P.τ Γ := by
      simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
        hΛinv (BHW.permAct (d := d) P.τ Γ)
    calc
      BHW.complexLorentzAction Λinv zlift
          = BHW.permAct (d := d) P.τ Γ := hraw
      _ = zadj := by
        ext k μ
        simp [zadj, Γ, BHW.os45Figure24IdentityPath_zero, BHW.permAct]
  have hgrp :
      JoinedIn (Set.univ : Set (ComplexLorentzGroup d)) Λinv 1 :=
    (ComplexLorentzGroup.isPathConnected (d := d)).joinedIn
      Λinv (Set.mem_univ _) 1 (Set.mem_univ _)
  refine
    ⟨{ toFun := fun t =>
          BHW.complexLorentzAction (hgrp.somePath t) zlift
       continuous_toFun :=
          (BHW.continuous_complexLorentzAction_fst
            (d := d) (n := n) zlift).comp
            hgrp.somePath.continuous_toFun
       source' := by
          change
            BHW.complexLorentzAction (hgrp.somePath 0) zlift = zadj
          rw [hgrp.somePath.source]
          exact hInv
       target' := by
          change
            BHW.complexLorentzAction (hgrp.somePath 1) zlift = zlift
          rw [hgrp.somePath.target]
          exact BHW.complexLorentzAction_one zlift },
      ?_⟩
  intro t
  exact Or.inl ⟨hgrp.somePath t, zlift, hzlift_ET, rfl⟩

/-- The checked Figure-2-4 lift at `0` is joined to the real source patch
inside the local BHW/Jost ambient through the ordinary extended tube. -/
theorem os45Figure24_joined_adjLift0_to_realPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval))
      (BHW.realEmbed x) := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  have hzlift_ET : zlift ∈ BHW.ExtendedTube d n := by
    simpa [zlift] using
      P.adjLift_mem_extendedTube x hx (0 : unitInterval)
  have hreal_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n :=
    P.V_ET x hx
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined :
      JoinedIn (BHW.ExtendedTube d n) zlift (BHW.realEmbed x) :=
    hpath.joinedIn zlift hzlift_ET (BHW.realEmbed x) hreal_ET
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) P.τ hw)

/-- The inverse Figure-2-4 Lorentz rotation sends the checked lift at `0` to
the selected adjacent Wick edge. -/
theorem os45Figure24_exists_lorentz_adjLift0_to_adjacentWick
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) :
    ∃ Λ : ComplexLorentzGroup d,
      BHW.complexLorentzAction Λ
          (BHW.os45Figure24AdjacentLift
            (d := d) (n := n) hd P.τ x (0 : unitInterval)) =
        fun k => wickRotatePoint (x (P.τ k)) := by
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  refine ⟨Λinv, ?_⟩
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x (0 : unitInterval)
  have hraw :
      BHW.complexLorentzAction Λinv zlift =
        BHW.permAct (d := d) P.τ Γ := by
    simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
      hΛinv (BHW.permAct (d := d) P.τ Γ)
  calc
    BHW.complexLorentzAction Λinv
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (0 : unitInterval))
        = BHW.complexLorentzAction Λinv zlift := by rfl
    _ = BHW.permAct (d := d) P.τ Γ := hraw
    _ = zadj := by
      ext k μ
      simp [zadj, Γ, BHW.os45Figure24IdentityPath_zero, BHW.permAct]
    _ = (fun k => wickRotatePoint (x (P.τ k))) := by rfl

/-- The selected adjacent Wick edge is joined to the real source patch inside
the local BHW/Jost ambient. -/
theorem os45Figure24_joined_adjacentWick_to_realPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (fun k => wickRotatePoint (x (P.τ k)))
      (BHW.realEmbed x) :=
  (BHW.os45Figure24_joined_adjacentWick_to_adjLift0
    (d := d) (n := n) hd P x hx).trans
    (BHW.os45Figure24_joined_adjLift0_to_realPatch
      (d := d) (n := n) hd P x hx)

private theorem os45Figure24_joined_realPatch_to_realPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {x y : NPointDomain d n} (hx : x ∈ P.V) (hy : y ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (BHW.realEmbed x) (BHW.realEmbed y) := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined :
      JoinedIn (BHW.ExtendedTube d n)
        (BHW.realEmbed x) (BHW.realEmbed y) :=
    hpath.joinedIn (BHW.realEmbed x) (P.V_ET x hx)
      (BHW.realEmbed y) (P.V_ET y hy)
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) P.τ hw)

/-- A real point of the checked Figure-2-4 source patch is joined to its
ordinary Wick edge inside the local BHW/Jost ambient. -/
theorem os45Figure24_joined_realPatch_to_ordinaryWick
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (BHW.realEmbed x) (fun k => wickRotatePoint (x k)) := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hwick_ET :
      (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n := by
    have hroot :
        (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
          _root_.ForwardTube d n :=
      wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
        (P.V_ordered x hx)
    have hBHW :
        (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
          BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hroot
    exact BHW.forwardTube_subset_extendedTube (by simpa using hBHW)
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined :
      JoinedIn (BHW.ExtendedTube d n)
        (BHW.realEmbed x) (fun k => wickRotatePoint (x k)) :=
    hpath.joinedIn (BHW.realEmbed x) (P.V_ET x hx)
      (fun k => wickRotatePoint (x k)) hwick_ET
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) P.τ hw)

/-- Every real point of the checked Figure-2-4 source patch lies in the local
BHW/Jost hull based at any selected adjacent Wick point of the same patch. -/
theorem mem_os45BHWJostHull_realPatch_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    BHW.realEmbed x ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      (BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx)

/-- The checked Figure-2-4 lift at `0` lies in the local BHW/Jost hull based
at any selected adjacent Wick point of the same source patch. -/
theorem mem_os45BHWJostHull_adjLift0_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval) ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      ((BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx).trans
        (BHW.os45Figure24_joined_adjLift0_to_realPatch
          (d := d) (n := n) hd P x hx).symm)

/-- Every ordinary Wick point of the checked Figure-2-4 source patch lies in
the local BHW/Jost hull based at any selected adjacent Wick point of the same
source patch. -/
theorem mem_os45BHWJostHull_ordinaryWick_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    (fun k => wickRotatePoint (x k)) ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      ((BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx).trans
        (BHW.os45Figure24_joined_realPatch_to_ordinaryWick
          (d := d) (n := n) hd P hx))

/-- Every selected adjacent Wick point of the checked Figure-2-4 source patch
lies in the local BHW/Jost hull based at any selected adjacent Wick point of
the same patch. -/
theorem mem_os45BHWJostHull_adjacentWick_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    (fun k => wickRotatePoint (x (P.τ k))) ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      ((BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx).trans
        ((BHW.os45Figure24_joined_adjLift0_to_realPatch
          (d := d) (n := n) hd P x hx).symm.trans
          (BHW.os45Figure24_joined_adjacentWick_to_adjLift0
            (d := d) (n := n) hd P x hx).symm))

/-- Checked local OS45/BHW/Jost hull geometry for one canonical Figure-2-4
source patch.  This record contains only the finite-dimensional path-component
carrier and pointwise membership fields; analytic branch continuation is the
next layer. -/
structure OS45BHWJostHullData
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) where
  zbase : Fin n → Fin (d + 1) → ℂ
  zbase_eq :
    zbase = fun k => wickRotatePoint (P.xseed (P.τ k))
  ΩJ : Set (Fin n → Fin (d + 1) → ℂ)
  ΩJ_eq :
    ΩJ = BHW.os45BHWJostHull d n P.τ zbase
  zbase_mem_ambient :
    zbase ∈ BHW.os45BHWJostAmbient d n P.τ
  ΩJ_open : IsOpen ΩJ
  ΩJ_connected : IsConnected ΩJ
  ΩJ_subset_hull :
    ΩJ ⊆ BHW.os45BHWJostHull d n P.τ zbase
  adjacentWick_mem :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x (P.τ k))) ∈ ΩJ
  realPatch_mem :
    ∀ x, x ∈ P.V → BHW.realEmbed x ∈ ΩJ
  adjLift0_mem :
    ∀ x, x ∈ P.V →
      BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval) ∈ ΩJ

/-- Producer for the pure local BHW/Jost hull attached to the canonical
Figure-2-4 source patch. -/
def os45_BHWJostHullData_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n)
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    BHW.OS45BHWJostHullData (d := d) hd n i hi P := by
  classical
  let zbase : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (P.xseed (P.τ k))
  have hzbase_ambient :
      zbase ∈ BHW.os45BHWJostAmbient d n P.τ := by
    simpa [zbase] using
      (BHW.os45Figure24_joined_adjacentWick_to_realPatch
        (d := d) (n := n) hd P P.xseed P.xseed_mem).source_mem
  refine
    { zbase := zbase
      zbase_eq := rfl
      ΩJ := BHW.os45BHWJostHull d n P.τ zbase
      ΩJ_eq := rfl
      zbase_mem_ambient := hzbase_ambient
      ΩJ_open :=
        BHW.os45BHWJostHull_open
          (d := d) (n := n) P.τ zbase hzbase_ambient
      ΩJ_connected :=
        BHW.os45BHWJostHull_connected
          (d := d) (n := n) P.τ zbase hzbase_ambient
      ΩJ_subset_hull := ?_
      adjacentWick_mem := ?_
      realPatch_mem := ?_
      adjLift0_mem := ?_ }
  · intro z hz
    exact hz
  · intro x hx
    simpa [zbase] using
      BHW.mem_os45BHWJostHull_adjacentWick_of_figure24
        (d := d) (n := n) hd P P.xseed_mem hx
  · intro x hx
    simpa [zbase] using
      BHW.mem_os45BHWJostHull_realPatch_of_figure24
        (d := d) (n := n) hd P P.xseed_mem hx
  · intro x hx
    simpa [zbase] using
      BHW.mem_os45BHWJostHull_adjLift0_of_figure24
        (d := d) (n := n) hd P P.xseed_mem hx

/-- The ordinary Wick edge of the checked source patch lies in the stored
local BHW/Jost hull. -/
theorem OS45BHWJostHullData.ordinaryWick_mem
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x k)) ∈ H.ΩJ := by
  intro x hx
  simpa [H.ΩJ_eq, H.zbase_eq] using
    BHW.mem_os45BHWJostHull_ordinaryWick_of_figure24
      (d := d) (n := n) hd P P.xseed_mem hx

/-- The stored local hull is contained in the concrete local BHW/Jost
ambient. -/
theorem OS45BHWJostHullData.ΩJ_subset_ambient
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ΩJ ⊆ BHW.os45BHWJostAmbient d n P.τ := by
  intro z hz
  exact
    BHW.os45BHWJostHull_subset_ambient
      (d := d) (n := n) P.τ H.zbase
      (H.ΩJ_subset_hull hz)

/-- The ordinary extended tube is one initial domain for the local BHW/Jost
ambient. -/
theorem OS45BHWJostHullData.extendedTube_subset_ambient
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.ExtendedTube d n ⊆ BHW.os45BHWJostAmbient d n P.τ := by
  intro z hz
  exact BHW.os45BHWJostAmbient_mem_identity
    (d := d) (n := n) P.τ hz

/-- The selected adjacent permuted extended-tube sector is the other initial
domain for the local BHW/Jost ambient. -/
theorem OS45BHWJostHullData.permutedExtendedTubeSector_subset_ambient
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.permutedExtendedTubeSector d n P.τ ⊆
      BHW.os45BHWJostAmbient d n P.τ := by
  intro z hz
  exact BHW.os45BHWJostAmbient_mem_adjacent
    (d := d) (n := n) P.τ hz

/-- Ordinary Wick rotations of the checked source patch lie in the ordinary
extended tube. -/
theorem OS45BHWJostHullData.ordinaryWick_mem_extendedTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n := by
  intro x hx
  have hft_eq : BHW.ForwardTube d n = _root_.ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, _root_.ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hroot :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        _root_.ForwardTube d n :=
    wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
      (P.V_ordered x hx)
  have hBHW :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        BHW.ForwardTube d n := by
    simpa [hft_eq] using hroot
  exact BHW.forwardTube_subset_extendedTube (by simpa using hBHW)

/-- Adjacent Wick rotations of the checked source patch lie in the selected
adjacent initial sector. -/
theorem OS45BHWJostHullData.adjacentWick_mem_permutedExtendedTubeSector
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x (P.τ k))) ∈
        BHW.permutedExtendedTubeSector d n P.τ := by
  intro x hx
  have hsector :
      (fun k => wickRotatePoint
        (x ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) ∈
        BHW.permutedExtendedTubeSector d n
          (Equiv.swap i ⟨i.val + 1, hi⟩) :=
    BHW.os45_adjacentWick_mem_selectedAdjacentSector_of_ordered
      (d := d) (n := n) i hi x (P.V_ordered x hx)
  simpa [P.τ_eq] using hsector

/-- The real source patch lies in the ordinary extended tube. -/
theorem OS45BHWJostHullData.realPatch_mem_extendedTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V → BHW.realEmbed x ∈ BHW.ExtendedTube d n :=
  P.V_ET

/-- The real source patch also lies in the selected adjacent initial sector
after applying the stored source permutation. -/
theorem OS45BHWJostHullData.realPatch_mem_permutedExtendedTubeSector
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      BHW.realEmbed x ∈ BHW.permutedExtendedTubeSector d n P.τ := by
  intro x hx
  rw [BHW.permutedExtendedTubeSector]
  simpa [BHW.permAct_realEmbed] using P.V_swapET x hx

/-- The ordinary initial extended tube meets the stored local hull at the
checked Figure-2-4 seed. -/
theorem OS45BHWJostHullData.extendedTube_meets_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    (BHW.ExtendedTube d n ∩ H.ΩJ).Nonempty := by
  refine ⟨fun k => wickRotatePoint (P.xseed k), ?_, ?_⟩
  · exact H.ordinaryWick_mem_extendedTube P.xseed P.xseed_mem
  · exact H.ordinaryWick_mem P.xseed P.xseed_mem

/-- The selected adjacent initial sector meets the stored local hull at the
checked Figure-2-4 adjacent Wick seed. -/
theorem OS45BHWJostHullData.permutedExtendedTubeSector_meets_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ).Nonempty := by
  refine ⟨fun k => wickRotatePoint (P.xseed (P.τ k)), ?_, ?_⟩
  · exact H.adjacentWick_mem_permutedExtendedTubeSector P.xseed P.xseed_mem
  · exact H.adjacentWick_mem P.xseed P.xseed_mem

/-- Assemble the existing source-patch BHW/Jost pair carrier from the strict
local BHW/Jost hull and two supplied branches on that hull.  The analytic
work is exactly the production of the branches and the four trace equations;
this constructor is only carrier bookkeeping. -/
noncomputable def OS45BHWJostHullData.toPairDataOfBranches
    [NeZero d]
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (Bord Btau : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (Bord_holo : DifferentiableOn ℂ Bord H.ΩJ)
    (Btau_holo : DifferentiableOn ℂ Btau H.ΩJ)
    (Bord_wick_trace :
      ∀ x, x ∈ P.V →
        Bord (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)))
    (Btau_wick_trace :
      ∀ x, x ∈ P.V →
        Btau (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))))
    (Bord_real_trace :
      ∀ x, x ∈ P.V →
        Bord (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))
    (Btau_real_trace :
      ∀ x, x ∈ P.V →
        Btau (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (P.τ k)))) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi P.V where
  τ := P.τ
  τ_eq := P.τ_eq
  U := H.ΩJ
  V_open := P.V_open
  V_nonempty := P.V_nonempty
  U_open := H.ΩJ_open
  U_connected := H.ΩJ_connected
  wick_mem := H.ordinaryWick_mem
  real_mem := H.realPatch_mem
  Bord := Bord
  Btau := Btau
  Bord_holo := Bord_holo
  Btau_holo := Btau_holo
  Bord_wick_trace := Bord_wick_trace
  Btau_wick_trace := Btau_wick_trace
  Bord_real_trace := Bord_real_trace
  Btau_real_trace := Btau_real_trace

/-- Lorentz transport from the checked Figure-2-4 lift at `0` back to the
selected adjacent Wick edge, for any branch invariant on the checked local
hull. -/
theorem os45_BHWJostLiftTransport_onPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {WJ branchτ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hW_inv :
      ∀ Λ z, z ∈ H.ΩJ →
        BHW.complexLorentzAction Λ z ∈ H.ΩJ →
          WJ (BHW.complexLorentzAction Λ z) = WJ z)
    (hW_adjacent :
      ∀ x, x ∈ P.V →
        WJ (fun k => wickRotatePoint (x (P.τ k))) =
          branchτ (fun k => wickRotatePoint (x (P.τ k)))) :
    ∀ x, x ∈ P.V →
      WJ
          (BHW.os45Figure24AdjacentLift
            (d := d) (n := n) hd P.τ x (0 : unitInterval)) =
        branchτ (fun k => wickRotatePoint (x (P.τ k))) := by
  intro x hx
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  rcases BHW.os45Figure24_exists_lorentz_adjLift0_to_adjacentWick
      (d := d) (n := n) hd P x with
    ⟨Λinv, hΛinv⟩
  have hzlift : zlift ∈ H.ΩJ := by
    simpa [zlift] using H.adjLift0_mem x hx
  have hΛ_mem : BHW.complexLorentzAction Λinv zlift ∈ H.ΩJ := by
    rw [show BHW.complexLorentzAction Λinv zlift = zadj by
      simpa [zlift, zadj] using hΛinv]
    exact H.adjacentWick_mem x hx
  calc
    WJ
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (0 : unitInterval))
        = WJ zlift := by rfl
    _ = WJ (BHW.complexLorentzAction Λinv zlift) := by
          exact (hW_inv Λinv zlift hzlift hΛ_mem).symm
    _ = WJ zadj := by
          rw [show BHW.complexLorentzAction Λinv zlift = zadj by
            simpa [zlift, zadj] using hΛinv]
    _ = branchτ zadj := hW_adjacent x hx
    _ = branchτ (fun k => wickRotatePoint (x (P.τ k))) := by rfl

end BHW
