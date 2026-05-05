import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45

noncomputable section

open Topology

namespace BHW

variable {d n : ℕ}

/-- The common-real-edge map underlying the fixed OS45 quarter-turn chart:
permute by `σ`, then halve the time coordinate. This is a real linear
homeomorphism of configuration space, so its image turns the selected real-open
slice into an honest real-open edge set. -/
noncomputable def os45CommonEdgeRealCLE
    (σ : Equiv.Perm (Fin n)) :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  { toFun := os45CommonEdgeRealPoint (d := d) (n := n) σ
    invFun := fun y k μ =>
      if μ = 0 then 2 * y (σ.symm k) 0 else y (σ.symm k) μ
    map_add' := by
      intro x y
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [os45CommonEdgeRealPoint]
        ring
      · simp [os45CommonEdgeRealPoint, hμ]
    map_smul' := by
      intro a x
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [os45CommonEdgeRealPoint, smul_eq_mul]
        ring
      · simp [os45CommonEdgeRealPoint, hμ, smul_eq_mul]
    left_inv := by
      intro x
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [os45CommonEdgeRealPoint]
        ring_nf
      · simp [os45CommonEdgeRealPoint, hμ]
    right_inv := by
      intro y
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [os45CommonEdgeRealPoint]
      · simp [os45CommonEdgeRealPoint, hμ]
    continuous_toFun := by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      by_cases hμ : μ = 0
      · subst hμ
        simpa [os45CommonEdgeRealPoint, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (by
            continuity : Continuous fun x : NPointDomain d n => (1 / 2 : ℝ) * x (σ k) 0)
      · simpa [os45CommonEdgeRealPoint, hμ] using
          (by
            continuity : Continuous fun x : NPointDomain d n => x (σ k) μ)
    continuous_invFun := by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      by_cases hμ : μ = 0
      · subst hμ
        simpa using
          (by
            continuity : Continuous fun y : NPointDomain d n => (2 : ℝ) * y (σ.symm k) 0)
      · simpa [hμ] using
          (by
            continuity : Continuous fun y : NPointDomain d n => y (σ.symm k) μ) }

@[simp] theorem os45CommonEdgeRealCLE_apply
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45CommonEdgeRealCLE (d := d) (n := n) σ x =
      os45CommonEdgeRealPoint (d := d) (n := n) σ x := by
  rfl

@[simp] theorem os45CommonEdgeRealCLE_symm_apply
    (σ : Equiv.Perm (Fin n))
    (y : NPointDomain d n) :
    (os45CommonEdgeRealCLE (d := d) (n := n) σ).symm y =
      fun k μ => if μ = 0 then 2 * y (σ.symm k) 0 else y (σ.symm k) μ := by
  rfl

/-- The image of an open set under the OS45 common-edge map is open. -/
theorem isOpen_image_os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n))
    {V : Set (NPointDomain d n)}
    (hV_open : IsOpen V) :
    IsOpen (os45CommonEdgeRealPoint (d := d) (n := n) σ '' V) := by
  simpa [os45CommonEdgeRealCLE_apply] using
    (os45CommonEdgeRealCLE (d := d) (n := n) σ).toHomeomorph.isOpenMap V hV_open

/-- The image of a connected set under the OS45 common-edge map is connected. -/
theorem isConnected_image_os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n))
    {V : Set (NPointDomain d n)}
    (hV_conn : IsConnected V) :
    IsConnected (os45CommonEdgeRealPoint (d := d) (n := n) σ '' V) := by
  exact hV_conn.image _ (os45CommonEdgeRealCLE (d := d) (n := n) σ).continuous.continuousOn

/-- The selected OS45 real-open slice can be transported to a genuine common
real edge for the quarter-turn geometry. This makes the edge set explicit
before the slot-2 common-boundary theorem is proved. -/
theorem choose_os45_common_real_edge_for_adjacent_swap
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (V E : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      E = os45CommonEdgeRealPoint (d := d) (n := n) ρ '' V ∧
      IsOpen E ∧ IsConnected E ∧ E.Nonempty ∧
      (∀ y ∈ E, ∃ x ∈ V,
        y = os45CommonEdgeRealPoint (d := d) (n := n) ρ x ∧
        BHW.realEmbed x ∈ adjacentOS45RealEdgeDomain (d := d) (n := n) i hi ∧
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi ρ ∧
        OS45OppositeTubeBranchGeometry (d := d) (n := n) ρ x ∧
        OS45OppositeTubeBranchGeometry (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases os45_adjacent_localEOWGeometry
      (d := d) (n := n) hd i hi with
    ⟨V, ρ, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET, hV_ordered,
      hV_swap_ordered, hV_wick, hV_real, hV_geom, hV_swap_geom⟩
  let E : Set (NPointDomain d n) :=
    os45CommonEdgeRealPoint (d := d) (n := n) ρ '' V
  have hE_open : IsOpen E := by
    exact isOpen_image_os45CommonEdgeRealPoint
      (d := d) (n := n) ρ hV_open
  have hE_conn : IsConnected E := by
    exact isConnected_image_os45CommonEdgeRealPoint
      (d := d) (n := n) ρ hV_conn
  have hE_ne : E.Nonempty := by
    rcases hV_ne with ⟨x, hxV⟩
    exact ⟨os45CommonEdgeRealPoint (d := d) (n := n) ρ x, ⟨x, hxV, rfl⟩⟩
  refine ⟨V, E, ρ, hV_open, hV_conn, hV_ne, rfl, hE_open, hE_conn, hE_ne, ?_⟩
  intro y hyE
  rcases hyE with ⟨x, hxV, rfl⟩
  refine ⟨x, hxV, rfl, hV_real x hxV, hV_wick x hxV, hV_geom x hxV, ?_⟩
  simpa [τ] using hV_swap_geom x hxV

end BHW
