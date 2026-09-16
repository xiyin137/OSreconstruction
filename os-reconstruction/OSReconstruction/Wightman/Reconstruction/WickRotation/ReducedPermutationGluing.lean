/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ReducedExtendedTube
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SliceGluing
















noncomputable section

open Complex Topology Set Filter LorentzLieGroup

namespace BHW

variable {d m : ℕ} [NeZero d]

theorem Route1ReducedAnalyticInput.perm_eq_on_forwardTube_of_mapsTo
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : MapsTo (permOnReducedDiff (d := d) (n := m + 1) σ)
      (ReducedForwardTubeN d m) (reducedExtendedTubeN d m)) :
    ∀ ξ ∈ ReducedForwardTubeN d m,
      F.toFun ξ = F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
  let A := F.toAbsoluteInput Wfn χ
  have hreal : ∀ (R : RestrictedLorentzGroup d)
      (z : Fin (m + 1) → Fin (d + 1) → ℂ), z ∈ ForwardTube d (m + 1) →
      A.toFun (fun k μ => ∑ ν, (R.val.val μ ν : ℂ) * z k ν) = A.toFun z := by
    intro R z hz
    exact A.real_lorentz_invariant (lorentzGroupToWightman R) z hz
  have hd : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨b, hb⟩ := forwardJostSet_nonempty (d := d) (n := m + 1) (by omega) hd
  let a : Fin (m + 1) → Fin (d + 1) → ℝ := fun k => b (σ.symm k)
  have ha : a ∈ JostSet d (m + 1) :=
    jostSet_permutation_invariant σ.symm (forwardJostSet_subset_jostSet hd hb)
  have haET : permAct σ (realEmbed a) ∈ ExtendedTube d (m + 1) := by
    change permAct σ (realEmbed a) ∈ BHWCore.ExtendedTube d (m + 1)
    convert forwardJostSet_subset_extendedTube hd b hb using 1
    ext k μ
    simp [permAct, realEmbed, a]
  obtain ⟨U, hU, hlocal⟩ :=
    PermutationBoundary.extendF_perm_eq_near_real_jost_anchor A.toFun A.holomorphic
      hreal Wfn.W A.boundary_values Wfn.locally_commutative σ a ha haET
  let P : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    (permAct σ) ⁻¹' ExtendedTube d (m + 1)
  have hP : IsOpen P := isOpen_extendedTube.preimage (continuous_permAct σ)
  let V := (interior U ∩ P) ∩ ForwardTube d (m + 1)
  have hV : IsOpen V := (isOpen_interior.inter hP).inter isOpen_forwardTube
  have hne : V.Nonempty := by
    exact (mem_closure_iff_nhds.mp (realEmbed_mem_closure_forwardTube a))
      (interior U ∩ P) (inter_mem (interior_mem_nhds.mpr hU) (hP.mem_nhds haET))
  let T := (permOnReducedDiff (d := d) (n := m + 1) σ).comp
    (reducedDiffMap (m + 1) d)
  let G := F.preInput.extend ∘ T
  have hG : DifferentiableOn ℂ G (ForwardTube d (m + 1)) := by
    apply F.preInput.extend_holomorphic.comp T.differentiableOn
    intro z hz
    exact hσ ((mem_forwardTube_iff_basepoint_and_reducedDiff z).mp hz).2
  have heq : EqOn A.toFun G V := by
    intro z hz
    have hz' : z ∈ (interior U ∩ P) ∩ ForwardTube d (m + 1) := hz
    calc
      A.toFun z = extendF A.toFun (permAct σ z) :=
        hlocal z ⟨interior_subset hz'.1.1, hz'.2⟩
      _ = F.preInput.extend (reducedDiffMap (m + 1) d (permAct σ z)) :=
        F.preInput.extend_pullback _ hz'.1.2
      _ = G z := by
        change _ = F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1) σ
          (reducedDiffMap (m + 1) d z))
        rw [permOnReducedDiff_reducedDiffMap]
        rfl
  have hall := identity_theorem_product_of_eqOn_open isOpen_forwardTube
    ⟨forwardTube_nonempty, forwardTube_convex.isPreconnected⟩ hV hne inter_subset_right
    A.holomorphic hG heq
  intro ξ hξ
  have h := hall (safeSection_mem_forwardTube m ξ hξ)
  change F.toFun (reducedDiffMap (m + 1) d (safeSection d m ξ)) =
    F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1) σ
      (reducedDiffMap (m + 1) d (safeSection d m ξ))) at h
  simpa only [reducedDiffMap_safeSection] using h

def reversalLorentz (d : ℕ) [NeZero d] : ComplexLorentzGroup d where
  val := Matrix.diagonal (fun μ => if μ.val ≤ 1 then (-1 : ℂ) else 1)
  metric_preserving := by
    apply ComplexLorentzGroup.of_metric_preserving_matrix
    simp only [Matrix.diagonal_transpose, ComplexLorentzGroup.ηℂ,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> ring
  proper := by
    rw [Matrix.det_diagonal]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
    simp [Fin.prod_univ_succ]

theorem reversalLorentz_action (z : Fin m → Fin (d + 1) → ℂ)
    (k : Fin m) (μ : Fin (d + 1)) :
    complexLorentzAction (reversalLorentz d) z k μ =
      if μ.val ≤ 1 then -z k μ else z k μ := by
  simp [complexLorentzAction, complexLorentzVectorAction, reversalLorentz, Matrix.diagonal_apply,
    ite_mul]

omit [NeZero d] in
theorem reducedDiffMap_rev (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    reducedDiffMap (m + 1) d (permAct Fin.revPerm z) =
      fun j μ => -reducedDiffMap (m + 1) d z (Fin.rev j) μ := by
  funext (j : Fin m) (μ : Fin (d + 1))
  simp only [reducedDiffMap_eq_successive_differences]
  change z (Fin.rev j.succ) μ - z (Fin.rev j.castSucc) μ =
    -(z ((Fin.rev j).succ) μ - z ((Fin.rev j).castSucc) μ)
  rw [Fin.rev_succ, Fin.rev_castSucc]
  ring

omit [NeZero d] in
theorem permOnReducedDiff_rev (ξ : ReducedNPointConfig d m) :
    permOnReducedDiff (d := d) (n := m + 1) Fin.revPerm ξ =
      fun j μ => -ξ (Fin.rev j) μ := by
  change reducedDiffMap (m + 1) d (permAct Fin.revPerm
    (reducedDiffSection (m + 1) d ξ)) = _
  rw [reducedDiffMap_rev, reducedDiffMap_section]

theorem reversalLorentz_rev_mem_forwardTube
    (ξ : ReducedNPointConfig d m) (hξ : ξ ∈ ReducedForwardTubeN d m) :
    complexLorentzAction (reversalLorentz d)
      (permOnReducedDiff (d := d) (n := m + 1) Fin.revPerm ξ) ∈
        ReducedForwardTubeN d m := by
  intro j
  have hj := hξ (Fin.rev j)
  rw [permOnReducedDiff_rev]
  refine ⟨?_, ?_⟩
  · simpa [reversalLorentz_action] using hj.1
  · convert hj.2 using 1
    apply Finset.sum_congr rfl
    intro μ _
    dsimp only
    simp [complexLorentzAction, complexLorentzVectorAction, reversalLorentz,
      Matrix.diagonal_apply, ite_mul]
    split_ifs <;> simp

theorem permOnReducedDiff_rev_mapsTo :
    MapsTo (permOnReducedDiff (d := d) (n := m + 1) Fin.revPerm)
      (ReducedForwardTubeN d m) (reducedExtendedTubeN d m) := by
  intro ξ hξ
  apply (mem_reducedExtendedTubeN_iff _).mpr
  refine ⟨(reversalLorentz d)⁻¹,
    complexLorentzAction (reversalLorentz d)
      (permOnReducedDiff (d := d) (n := m + 1) Fin.revPerm ξ),
    reversalLorentz_rev_mem_forwardTube ξ hξ, ?_⟩
  exact complexLorentzAction_inv _ _

theorem Route1ReducedAnalyticInput.rev_eq_on_forwardTube
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (ξ : ReducedNPointConfig d m) (hξ : ξ ∈ ReducedForwardTubeN d m) :
    F.toFun ξ = F.preInput.extend
      (permOnReducedDiff (d := d) (n := m + 1) Fin.revPerm ξ) :=
  F.perm_eq_on_forwardTube_of_mapsTo Wfn χ Fin.revPerm
    permOnReducedDiff_rev_mapsTo ξ hξ

omit [NeZero d] in
theorem permOnReducedDiff_action (σ : Equiv.Perm (Fin (m + 1)))
    (L : ComplexLorentzGroup d) (ξ : ReducedNPointConfig d m) :
    permOnReducedDiff (d := d) (n := m + 1) σ (complexLorentzAction L ξ) =
      complexLorentzAction L (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
  calc
    _ = permOnReducedDiff (d := d) (n := m + 1) σ
        (reducedDiffMap (m + 1) d
          (complexLorentzAction L (reducedDiffSection (m + 1) d ξ))) := by
      rw [reducedDiffMap_action, reducedDiffMap_section]
    _ = reducedDiffMap (m + 1) d (permAct σ
        (complexLorentzAction L (reducedDiffSection (m + 1) d ξ))) :=
      permOnReducedDiff_reducedDiffMap σ _
    _ = reducedDiffMap (m + 1) d (complexLorentzAction L
        (permAct σ (reducedDiffSection (m + 1) d ξ))) := rfl
    _ = _ := by rw [reducedDiffMap_action]; rfl

theorem reducedExtendedTubeN_lorentz_invariant
    (L : ComplexLorentzGroup d) (ξ : ReducedNPointConfig d m)
    (hξ : ξ ∈ reducedExtendedTubeN d m) :
    complexLorentzAction L ξ ∈ reducedExtendedTubeN d m := by
  obtain ⟨M, η, hη, rfl⟩ := (mem_reducedExtendedTubeN_iff ξ).mp hξ
  exact (mem_reducedExtendedTubeN_iff _).mpr
    ⟨L * M, η, hη, complexLorentzAction_mul L M η⟩

omit [NeZero d] in
theorem exists_forward_add_smul (a b : Fin (d + 1) → ℝ)
    (ha : InOpenForwardCone d a) :
    ∃ t : ℝ, InOpenForwardCone d (fun μ => b μ + t * a μ) := by
  have hopen : IsOpen {t : ℝ | InOpenForwardCone d (fun μ => a μ + t * b μ)} := by
    change IsOpen ({t : ℝ | 0 < a 0 + t * b 0} ∩
      {t : ℝ | ∑ μ, minkowskiSignature d μ * (a μ + t * b μ) ^ 2 < 0})
    apply IsOpen.inter
    · exact isOpen_lt continuous_const (by fun_prop)
    · exact isOpen_lt (by fun_prop) continuous_const
  have he : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      InOpenForwardCone d (fun μ => a μ + t * b μ) :=
    nhdsWithin_le_nhds (hopen.mem_nhds (by simpa using ha))
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hc⟩ := (hpos.and he).exists
  refine ⟨t⁻¹, ?_⟩
  have hscale := inOpenForwardCone_smul_pos hc (inv_pos.mpr ht)
  change InOpenForwardCone d (fun μ => t⁻¹ * (a μ + t * b μ)) at hscale
  have heq : (fun μ => t⁻¹ * (a μ + t * b μ)) =
      (fun μ => b μ + t⁻¹ * a μ) := by
    funext μ
    field_simp
    ring
  rwa [heq] at hscale

theorem exists_forward_lift_of_reduced_perm_overlap
    (σ : Equiv.Perm (Fin (m + 1))) (hσ : σ ≠ 1) (hrev : σ ≠ Fin.revPerm)
    (L : ComplexLorentzGroup d) (ξ : ReducedNPointConfig d m)
    (hξ : ξ ∈ ReducedForwardTubeN d m)
    (hLξ : complexLorentzAction L (permOnReducedDiff (d := d) (n := m + 1) σ ξ) ∈
      ReducedForwardTubeN d m) :
    ∃ z : Fin (m + 1) → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d (m + 1) ∧
      complexLorentzAction L (permAct σ z) ∈ ForwardTube d (m + 1) ∧
      reducedDiffMap (m + 1) d z = ξ := by
  let z := safeSection d m ξ
  have hz : z ∈ ForwardTube d (m + 1) := safeSection_mem_forwardTube m ξ hξ
  have hzξ : reducedDiffMap (m + 1) d z = ξ := reducedDiffMap_safeSection _ _ _
  have hdiff : reducedDiffMap (m + 1) d (complexLorentzAction L (permAct σ z)) =
      complexLorentzAction L (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
    rw [reducedDiffMap_action]
    exact congrArg (complexLorentzAction L)
      ((permOnReducedDiff_reducedDiffMap σ z).symm.trans
        (congrArg (permOnReducedDiff (d := d) (n := m + 1) σ) hzξ))
  have hred : reducedDiffMap (m + 1) d (complexLorentzAction L (permAct σ z)) ∈
      ReducedForwardTubeN d m := hdiff ▸ hLξ
  obtain ⟨v, hv⟩ := SliceGeometry.exists_imaginary_forward_of_relative_perm_overlap
    L σ hσ hrev z
    (fun i => by
      convert hz i.succ using 1
      ext μ
      congr 2)
    (fun i => by
      convert hred i using 1
      ext μ
      simp only [reducedDiffMap_eq_successive_differences, Complex.sub_im]
      congr 2 <;> apply Fin.ext <;> rfl)
  obtain ⟨t, ht⟩ := exists_forward_add_smul (SliceGeometry.imaginaryPart L v)
    (fun μ => (complexLorentzAction L (permAct σ z) 0 μ).im) hv
  let w : Fin (m + 1) → Fin (d + 1) → ℂ := fun k μ => z k μ + (t * v μ : ℝ)
  have hwξ : reducedDiffMap (m + 1) d w = ξ := by
    rw [reducedDiffMap_translate_uniform_eq]
    exact hzξ
  refine ⟨w, ?_, ?_, hwξ⟩
  · apply (mem_forwardTube_iff_basepoint_and_reducedDiff w).mpr
    constructor
    · simpa [w] using ((mem_forwardTube_iff_basepoint_and_reducedDiff z).mp hz).1
    · rwa [hwξ]
  · apply (mem_forwardTube_iff_basepoint_and_reducedDiff _).mpr
    constructor
    · convert ht using 1
      funext μ
      simp [w, permAct, complexLorentzAction, complexLorentzVectorAction,
        SliceGeometry.imaginaryPart, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Complex.mul_im, Finset.sum_add_distrib, Finset.mul_sum,
        mul_add, mul_left_comm, add_assoc]
      change ∑ x, t * ((L.val μ x).im * v x) = t * ∑ x, (L.val μ x).im * v x
      rw [Finset.mul_sum]
    · have hwDiff : reducedDiffMap (m + 1) d (complexLorentzAction L (permAct σ w)) =
          complexLorentzAction L (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
        rw [reducedDiffMap_action]
        exact congrArg (complexLorentzAction L)
          ((permOnReducedDiff_reducedDiffMap σ w).symm.trans
            (congrArg (permOnReducedDiff (d := d) (n := m + 1) σ) hwξ))
      exact hwDiff ▸ hLξ

theorem Route1ReducedAnalyticInput.perm_eq_on_forwardTube
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (σ : Equiv.Perm (Fin (m + 1))) (ξ : ReducedNPointConfig d m)
    (hξ : ξ ∈ ReducedForwardTubeN d m)
    (hσξ : permOnReducedDiff (d := d) (n := m + 1) σ ξ ∈ reducedExtendedTubeN d m) :
    F.toFun ξ = F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
  by_cases hσ : σ = 1
  · subst σ
    rw [permOnReducedDiff_one, F.preInput.extend_eq ξ hξ]
    rfl
  by_cases hrev : σ = Fin.revPerm
  · subst σ
    exact F.rev_eq_on_forwardTube Wfn χ ξ hξ
  obtain ⟨L, η, hη, hηξ⟩ := (mem_reducedExtendedTubeN_iff _).mp hσξ
  have hLξ : complexLorentzAction L⁻¹
      (permOnReducedDiff (d := d) (n := m + 1) σ ξ) ∈ ReducedForwardTubeN d m := by
    rw [← hηξ, complexLorentzAction_inv]
    exact hη
  obtain ⟨z, hz, hLz, hzξ⟩ :=
    exists_forward_lift_of_reduced_perm_overlap σ hσ hrev L⁻¹ ξ hξ hLξ
  let A := F.toAbsoluteInput Wfn χ
  have hreal : ∀ (R : RestrictedLorentzGroup d)
      (z : Fin (m + 1) → Fin (d + 1) → ℂ), z ∈ ForwardTube d (m + 1) →
      A.toFun (fun k μ => ∑ ν, (R.val.val μ ν : ℂ) * z k ν) = A.toFun z := by
    intro R z hz
    exact A.real_lorentz_invariant (lorentzGroupToWightman R) z hz
  have hzET : permAct σ z ∈ ExtendedTube d (m + 1) := by
    refine mem_iUnion.mpr ⟨L, complexLorentzAction L⁻¹ (permAct σ z), hLz, ?_⟩
    simpa using (complexLorentzAction_inv L⁻¹ (permAct σ z)).symm
  calc
    F.toFun ξ = A.toFun z := by
      change F.toFun ξ = F.toFun (reducedDiffMap (m + 1) d z)
      rw [hzξ]
    _ = extendF A.toFun (permAct σ z) :=
      PermutationBoundary.extendF_perm_eq_on_forward_lorentz_slice A.toFun A.holomorphic
        hreal Wfn.W A.boundary_values Wfn.locally_commutative σ hσ L⁻¹ z hz hLz
    _ = F.preInput.extend (reducedDiffMap (m + 1) d (permAct σ z)) :=
      F.preInput.extend_pullback _ hzET
    _ = F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
      rw [← hzξ, permOnReducedDiff_reducedDiffMap]
      rfl

theorem Route1ReducedAnalyticInput.extend_perm_eq_on_overlap
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (σ : Equiv.Perm (Fin (m + 1))) (ξ : ReducedNPointConfig d m)
    (hξ : ξ ∈ reducedExtendedTubeN d m)
    (hσξ : permOnReducedDiff (d := d) (n := m + 1) σ ξ ∈ reducedExtendedTubeN d m) :
    F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1) σ ξ) =
      F.preInput.extend ξ := by
  obtain ⟨L, η, hη, rfl⟩ := (mem_reducedExtendedTubeN_iff ξ).mp hξ
  have hση : permOnReducedDiff (d := d) (n := m + 1) σ η ∈
      reducedExtendedTubeN d m := by
    have h := reducedExtendedTubeN_lorentz_invariant L⁻¹ _ hσξ
    rwa [permOnReducedDiff_action, complexLorentzAction_inv] at h
  rw [permOnReducedDiff_action,
    F.preInput.extend_lorentz_invariant L _ hση,
    F.preInput.extend_lorentz_invariant L _
      ((mem_reducedExtendedTubeN_iff η).mpr ⟨1, η, hη, complexLorentzAction_one η⟩),
    F.preInput.extend_eq η hη]
  exact (F.perm_eq_on_forwardTube Wfn χ σ η hη hση).symm

theorem mem_reducedPermutedExtendedTubeN_iff (ξ : ReducedNPointConfig d m) :
    ξ ∈ ReducedPermutedExtendedTubeN d m ↔
      ∃ σ : Equiv.Perm (Fin (m + 1)),
        permOnReducedDiff (d := d) (n := m + 1) σ ξ ∈ reducedExtendedTubeN d m := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨σ, hσ⟩ := mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube.mp hz
    refine ⟨σ, ?_⟩
    rw [reducedExtendedTubeN_eq_image]
    exact ⟨permAct σ z, hσ, (permOnReducedDiff_reducedDiffMap σ z).symm⟩
  · rintro ⟨σ, hσ⟩
    rw [reducedExtendedTubeN_eq_image] at hσ
    obtain ⟨z, hz, hzξ⟩ := hσ
    refine ⟨permAct σ⁻¹ z, ?_, ?_⟩
    · apply mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube.mpr
      refine ⟨σ, ?_⟩
      simpa [permAct] using hz
    · calc
        _ = permOnReducedDiff (d := d) (n := m + 1) σ⁻¹
            (reducedDiffMap (m + 1) d z) := (permOnReducedDiff_reducedDiffMap σ⁻¹ z).symm
        _ = permOnReducedDiff (d := d) (n := m + 1) σ⁻¹
            (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by rw [hzξ]
        _ = ξ := by rw [← permOnReducedDiff_mul, mul_inv_cancel, permOnReducedDiff_one]

omit [NeZero d] in
theorem isOpen_reducedExtendedTubeN : IsOpen (reducedExtendedTubeN d m) :=
  (diffCoordEquiv m d).toHomeomorph.isOpenMap _ isOpen_extendedTube

theorem isOpen_reducedPermutedExtendedTubeN : IsOpen (ReducedPermutedExtendedTubeN d m) := by
  have heq : ReducedPermutedExtendedTubeN d m =
      ⋃ σ : Equiv.Perm (Fin (m + 1)),
        (permOnReducedDiff (d := d) (n := m + 1) σ) ⁻¹' reducedExtendedTubeN d m := by
    ext ξ
    simp only [mem_reducedPermutedExtendedTubeN_iff, mem_iUnion, mem_preimage]
  rw [heq]
  exact isOpen_iUnion (fun σ => isOpen_reducedExtendedTubeN.preimage
    (permOnReducedDiff (d := d) (n := m + 1) σ).continuous)

def Route1ReducedAnalyticInput.permutedExtend
    {Wfn : WightmanFunctions d} {χ : NormalizedBasepointCutoff d}
    (F : Route1ReducedAnalyticInput Wfn χ m) (ξ : ReducedNPointConfig d m) : ℂ := by
  classical
  exact if h : ξ ∈ ReducedPermutedExtendedTubeN d m then
    F.preInput.extend (permOnReducedDiff (d := d) (n := m + 1)
      ((mem_reducedPermutedExtendedTubeN_iff ξ).mp h).choose ξ)
  else 0

theorem Route1ReducedAnalyticInput.permutedExtend_eq_sector
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (σ : Equiv.Perm (Fin (m + 1))) (ξ : ReducedNPointConfig d m)
    (hσ : permOnReducedDiff (d := d) (n := m + 1) σ ξ ∈ reducedExtendedTubeN d m) :
    F.permutedExtend ξ = F.preInput.extend
      (permOnReducedDiff (d := d) (n := m + 1) σ ξ) := by
  have hξ := (mem_reducedPermutedExtendedTubeN_iff ξ).mpr ⟨σ, hσ⟩
  rw [permutedExtend, dif_pos hξ]
  let τ := ((mem_reducedPermutedExtendedTubeN_iff ξ).mp hξ).choose
  have hτ := ((mem_reducedPermutedExtendedTubeN_iff ξ).mp hξ).choose_spec
  have heq : permOnReducedDiff (d := d) (n := m + 1) (σ⁻¹ * τ)
      (permOnReducedDiff (d := d) (n := m + 1) σ ξ) =
      permOnReducedDiff (d := d) (n := m + 1) τ ξ := by
    rw [← permOnReducedDiff_mul, mul_inv_cancel_left]
  have h := F.extend_perm_eq_on_overlap Wfn χ (σ⁻¹ * τ) _ hσ (heq.symm ▸ hτ)
  rwa [heq] at h

theorem Route1ReducedAnalyticInput.permutedExtend_holomorphic
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m) :
    DifferentiableOn ℂ F.permutedExtend (ReducedPermutedExtendedTubeN d m) := by
  intro ξ hξ
  obtain ⟨σ, hσ⟩ := (mem_reducedPermutedExtendedTubeN_iff ξ).mp hξ
  let P := permOnReducedDiff (d := d) (n := m + 1) σ
  have hU : IsOpen (P ⁻¹' reducedExtendedTubeN d m) :=
    isOpen_reducedExtendedTubeN.preimage P.continuous
  have hG : DifferentiableOn ℂ (F.preInput.extend ∘ P) (P ⁻¹' reducedExtendedTubeN d m) :=
    F.preInput.extend_holomorphic.comp P.differentiableOn (fun _ hx => hx)
  have heq : F.permutedExtend =ᶠ[nhds ξ] F.preInput.extend ∘ P := by
    filter_upwards [hU.mem_nhds hσ] with η hη
    exact F.permutedExtend_eq_sector Wfn χ σ η hη
  exact ((hG.differentiableAt (hU.mem_nhds hσ)).congr_of_eventuallyEq heq).differentiableWithinAt

theorem Route1ReducedAnalyticInput.permutedExtend_eq
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (ξ : ReducedNPointConfig d m) (hξ : ξ ∈ ReducedForwardTubeN d m) :
    F.permutedExtend ξ = F.toFun ξ := by
  have hET := (mem_reducedExtendedTubeN_iff ξ).mpr ⟨1, ξ, hξ, complexLorentzAction_one ξ⟩
  have h := F.permutedExtend_eq_sector Wfn χ 1 ξ
    (by rw [permOnReducedDiff_one]; exact hET)
  rw [permOnReducedDiff_one, F.preInput.extend_eq ξ hξ] at h
  exact h

theorem Route1ReducedAnalyticInput.permutedExtend_lorentz_invariant
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m) :
    IsReducedLorentzInvariant (d := d) (n := m + 1) F.permutedExtend := by
  intro L ξ hξ _
  obtain ⟨σ, hσ⟩ := (mem_reducedPermutedExtendedTubeN_iff ξ).mp hξ
  have hLσ : permOnReducedDiff (d := d) (n := m + 1) σ (complexLorentzAction L ξ) ∈
      reducedExtendedTubeN d m := by
    rw [permOnReducedDiff_action]
    exact reducedExtendedTubeN_lorentz_invariant L _ hσ
  rw [F.permutedExtend_eq_sector Wfn χ σ _ hLσ,
    F.permutedExtend_eq_sector Wfn χ σ _ hσ, permOnReducedDiff_action]
  exact F.preInput.extend_lorentz_invariant L _ hσ

theorem Route1ReducedAnalyticInput.permutedExtend_perm_invariant
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m) :
    IsReducedPermutationInvariant (d := d) (n := m + 1) F.permutedExtend := by
  intro σ ξ _ hσξ
  obtain ⟨τ, hτ⟩ := (mem_reducedPermutedExtendedTubeN_iff _).mp hσξ
  have hστ : permOnReducedDiff (d := d) (n := m + 1) (σ * τ) ξ ∈
      reducedExtendedTubeN d m := by rwa [permOnReducedDiff_mul]
  rw [F.permutedExtend_eq_sector Wfn χ τ _ hτ,
    F.permutedExtend_eq_sector Wfn χ (σ * τ) _ hστ, permOnReducedDiff_mul]

theorem Route1ReducedAnalyticInput.permutedExtend_unique
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (F : Route1ReducedAnalyticInput Wfn χ m)
    (G : ReducedNPointConfig d m → ℂ)
    (hG : DifferentiableOn ℂ G (ReducedPermutedExtendedTubeN d m))
    (heq : ∀ η ∈ ReducedForwardTubeN d m, G η = F.toFun η) :
    ∀ η ∈ ReducedPermutedExtendedTubeN d m, G η = F.permutedExtend η := by
  have hsub : ReducedForwardTubeN d m ⊆ ReducedPermutedExtendedTubeN d m := by
    intro ξ hξ
    apply (mem_reducedPermutedExtendedTubeN_iff ξ).mpr
    refine ⟨1, ?_⟩
    rw [permOnReducedDiff_one]
    exact (mem_reducedExtendedTubeN_iff ξ).mpr ⟨1, ξ, hξ, complexLorentzAction_one ξ⟩
  have h := identity_theorem_product_of_eqOn_open isOpen_reducedPermutedExtendedTubeN
    (isConnected_reducedPermutedExtendedTube (d := d) (n := m + 1))
    (isOpen_reducedForwardCone (m + 1) d) (reducedForwardCone_nonempty (m + 1) d)
    hsub hG (F.permutedExtend_holomorphic Wfn χ)
    (fun ξ hξ => (heq ξ hξ).trans (F.permutedExtend_eq Wfn χ ξ hξ).symm)
  exact fun _ hη => h hη

theorem reducedBHW_of_input_proved
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ)
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ∃ (F_ext : ReducedNPointConfig d m → ℂ),
      DifferentiableOn ℂ F_ext (ReducedPermutedExtendedTubeN d m) ∧
      (∀ η ∈ ReducedForwardTubeN d m, F_ext η = hInput.toFun η) ∧
      IsReducedLorentzInvariant (d := d) (n := m + 1) F_ext ∧
      IsReducedPermutationInvariant (d := d) (n := m + 1) F_ext ∧
      (∀ (G : ReducedNPointConfig d m → ℂ),
        DifferentiableOn ℂ G (ReducedPermutedExtendedTubeN d m) →
        (∀ η ∈ ReducedForwardTubeN d m, G η = hInput.toFun η) →
        ∀ η ∈ ReducedPermutedExtendedTubeN d m, G η = F_ext η) :=
  ⟨hInput.permutedExtend, hInput.permutedExtend_holomorphic Wfn χ,
    hInput.permutedExtend_eq Wfn χ, hInput.permutedExtend_lorentz_invariant Wfn χ,
    hInput.permutedExtend_perm_invariant Wfn χ, hInput.permutedExtend_unique Wfn χ⟩

end BHW
