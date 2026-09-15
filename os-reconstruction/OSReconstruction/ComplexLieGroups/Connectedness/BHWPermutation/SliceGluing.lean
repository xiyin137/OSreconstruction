import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationBoundary
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.LorentzSliceBoundary
import OSReconstruction.SCV.LocalBoundaryUniqueness

/-!
# Permutation Gluing Through Fixed Lorentz Slices

Local distributional boundary matching at real spacelike anchors gives branch
agreement. One-variable identity on a convex fixed-Lorentz slice propagates it
to any forward overlap, and Lorentz transport reaches every extended overlap.
The proof works in all positive spatial dimensions without seed connectedness.
-/

noncomputable section

open Complex Topology Filter MeasureTheory Set LorentzLieGroup

namespace BHW.PermutationBoundary

variable {d n : ℕ} [NeZero d]

private theorem forwardTube_eq_root : BHW.ForwardTube d n = _root_.ForwardTube d n := by
  ext z
  simp only [BHW.ForwardTube, _root_.ForwardTube, Set.mem_setOf_eq]
  exact forall_congr' fun k => bhw_inOpenForwardCone_iff_wightman _

set_option maxHeartbeats 1000000 in
theorem extendF_perm_eq_near_real_jost_anchor
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (L : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (L.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Tendsto (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hF_local_dist : IsAdjacentLocallyCommutativeWeak d W)
    (σ : Equiv.Perm (Fin n)) (a : NPointDomain d n)
    (ha : a ∈ JostSet d n) (haET : permAct σ (realEmbed a) ∈ ExtendedTube d n) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℂ), U ∈ nhds (realEmbed a) ∧
      ∀ z ∈ U ∩ ForwardTube d n, F z = extendF F (permAct σ z) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let c := eR a
  let P : (Fin (n * (d + 1)) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
    fun w => permAct σ (e.symm w)
  let Q : (Fin (n * (d + 1)) → ℂ) → NPointDomain d n :=
    fun w => eR.symm (fun i => (w i).re)
  have hP : Differentiable ℂ P := by
    intro w
    apply differentiableAt_pi.mpr
    intro k
    apply differentiableAt_pi.mpr
    intro μ
    exact ((differentiable_apply μ).comp ((differentiable_apply (σ k)).comp
      e.symm.differentiable)).differentiableAt
  have hQ : Continuous Q := eR.symm.continuous.comp
    (continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i))
  have hembed : ∀ x : NPointDomain d n, e.symm (SCV.realEmbed (eR x)) = realEmbed x := by
    intro x
    ext k μ
    simp [e, eR, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply, SCV.realEmbed, realEmbed]
  have hQembed : ∀ x : NPointDomain d n, Q (SCV.realEmbed (eR x)) = x := by
    intro x
    simp [Q, SCV.realEmbed]
  let V := P ⁻¹' ExtendedTube d n ∩ Q ⁻¹' JostSet d n
  have hV : IsOpen V := (isOpen_extendedTube.preimage hP.continuous).inter
    (isOpen_jostSet.preimage hQ)
  have hc : SCV.realEmbed c ∈ V := by
    constructor
    · simpa [P, c, hembed] using haET
    · simpa [c, hQembed] using ha
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV (SCV.realEmbed c) hc
  let F₀ : (Fin (n * (d + 1)) → ℂ) → ℂ := F ∘ e.symm
  let G₀ : (Fin (n * (d + 1)) → ℂ) → ℂ := extendF F ∘ P
  have hF₀ : DifferentiableOn ℂ F₀ (SCV.TubeDomain (ForwardConeFlat d n)) := by
    rw [← forwardTube_flatten_eq_tubeDomain]
    apply (hF_holo.mono (by rw [forwardTube_eq_root])).comp e.symm.differentiableOn
    rintro w ⟨z, hz, rfl⟩
    simpa [e] using hz
  have hcinv := complex_lorentz_invariance n F hF_holo hF_real_inv
  have hG₀ : DifferentiableOn ℂ G₀ (Metric.ball (SCV.realEmbed c) R) :=
    (extendF_holomorphicOn n F hF_holo hcinv).comp hP.differentiableOn
      (fun _ hw => (hRV hw).1)
  have hboundary : ∀ ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ,
      HasCompactSupport (ψ : (Fin (n * (d + 1)) → ℝ) → ℂ) →
      tsupport (ψ : (Fin (n * (d + 1)) → ℝ) → ℂ) ⊆ Metric.ball c R →
      ∀ η ∈ ForwardConeFlat d n,
        Tendsto (fun ε : ℝ => ∫ x : Fin (n * (d + 1)) → ℝ,
          F₀ (fun i => (x i : ℂ) + ε * (η i : ℂ) * I) * ψ x)
          (nhdsWithin 0 (Ioi 0)) (nhds (∫ x, G₀ (SCV.realEmbed x) * ψ x)) := by
    intro ψ hψ hs η hη
    obtain ⟨η', hη', rfl⟩ := hη
    let f : SchwartzNPoint d n := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR ψ
    have hf : HasCompactSupport (f : NPointDomain d n → ℂ) :=
      hψ.comp_homeomorph eR.toHomeomorph
    have hfs : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        SCV.realEmbed (eR x) ∈ Metric.ball (SCV.realEmbed c) R := by
      intro x hx
      have heq : tsupport (f : NPointDomain d n → ℂ) =
          eR.toHomeomorph ⁻¹' tsupport (ψ : (Fin (n * (d + 1)) → ℝ) → ℂ) :=
        tsupport_comp_eq_preimage (g := (ψ : (Fin (n * (d + 1)) → ℝ) → ℂ)) eR.toHomeomorph
      have hx' := hs (show eR x ∈ tsupport (ψ : (Fin (n * (d + 1)) → ℝ) → ℂ) from by
        rw [heq] at hx
        exact hx)
      have hemb : SCV.realEmbed (eR x) - SCV.realEmbed c = SCV.realEmbed (eR x - c) := by
        ext i
        simp [SCV.realEmbed]
      simpa [Metric.mem_ball, dist_eq_norm, hemb, SCV.norm_realEmbed_eq] using hx'
    have hfJ : ∀ x, f x ≠ 0 → x ∈ JostSet d n := by
      intro x hx
      have h := (hRV (hfs x (subset_tsupport _ hx))).2
      simpa only [Set.mem_preimage, hQembed] using h
    have hfET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n := by
      intro x hx
      have h := (hRV (hfs x hx)).1
      have h' : permAct σ (realEmbed x) ∈ ExtendedTube d n := by
        simpa [P, hembed] using h
      exact h'
    have hpair := extendF_perm_pairing_eq_boundary_of_jost_support F hF_holo hF_real_inv
      W hF_bv_dist hF_local_dist σ f hf hfJ hfET
    have hGpair : (∫ x, G₀ (SCV.realEmbed x) * ψ x) = W n f := by
      rw [integral_flatten_change_of_variables n (d + 1)]
      convert hpair using 1
      apply integral_congr_ae
      filter_upwards with x
      change extendF F (permAct σ (e.symm (SCV.realEmbed (eR x)))) * ψ (eR x) =
        extendF F (realEmbed (fun k => x (σ k))) * ψ (eR x)
      rw [hembed]
      rfl
    rw [hGpair]
    refine (hF_bv_dist f η' hη').congr' (Eventually.of_forall fun ε => ?_)
    dsimp only
    rw [integral_flatten_change_of_variables n (d + 1)]
    apply integral_congr_ae
    filter_upwards with x
    have harg : e.symm (fun i => ((eR x) i : ℂ) + ε * ((eR η') i : ℂ) * I) =
        (fun k μ => (x k μ : ℂ) + ε * (η' k μ : ℂ) * I) := by
      ext k μ
      simp only [e, eR, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply,
        Equiv.symm_apply_apply]
    change F (fun k μ => (x k μ : ℂ) + ε * (η' k μ : ℂ) * I) * ψ (eR x) =
      F (e.symm (fun i => ((eR x) i : ℂ) + ε * ((eR η') i : ℂ) * I)) * ψ (eR x)
    rw [harg]
  have heq := SCV.local_eq_of_distributional_boundary_pairing
    (forwardConeFlat_isOpen d n) (forwardConeFlat_isCone d n) c hR
    (hF₀.mono inter_subset_right) hG₀ hboundary
  refine ⟨e ⁻¹' Metric.ball (SCV.realEmbed c) (R / 8), ?_, ?_⟩
  · apply e.continuous.continuousAt.preimage_mem_nhds
    have hc' : e (realEmbed a) = SCV.realEmbed c := by
      rw [← hembed a, e.apply_symm_apply]
    rw [hc']
    exact Metric.ball_mem_nhds _ (by positivity)
  · intro z hz
    have hzflat : e z ∈ SCV.TubeDomain (ForwardConeFlat d n) := by
      rw [← forwardTube_flatten_eq_tubeDomain]
      exact mem_image_of_mem e (by simpa only [forwardTube_eq_root] using hz.2)
    simpa [F₀, G₀, P] using heq (e z) ⟨hz.1, hzflat⟩

set_option maxHeartbeats 1000000 in
theorem extendF_perm_eq_on_forward_lorentz_slice
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (L : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (L.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Tendsto (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hF_local_dist : IsAdjacentLocallyCommutativeWeak d W)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (L : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    (hLz : complexLorentzAction L (permAct σ z) ∈ ForwardTube d n) :
    F z = extendF F (permAct σ z) := by
  obtain ⟨a, ha, hLa, hseg⟩ :=
    SliceGeometry.exists_real_jost_anchor_segment_of_perm_overlap L σ hσ z hz hLz
  have htoET : ∀ w, complexLorentzAction L (permAct σ w) ∈ ForwardTube d n →
      permAct σ w ∈ ExtendedTube d n := by
    intro w hw
    exact Set.mem_iUnion.mpr ⟨L⁻¹, complexLorentzAction L (permAct σ w), hw,
      (complexLorentzAction_inv L _).symm⟩
  obtain ⟨U, hU, hlocal⟩ := extendF_perm_eq_near_real_jost_anchor F hF_holo hF_real_inv
    W hF_bv_dist hF_local_dist σ a ha (htoET _ hLa)
  let φ : ℂ → (Fin n → Fin (d + 1) → ℂ) := fun w => (1 - w) • realEmbed a + w • z
  have hφ0 : φ 0 = realEmbed a := by simp [φ]
  have hφ1 : φ 1 = z := by simp [φ]
  have hφ : Differentiable ℂ φ := by
    fun_prop
  have hφseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      φ (t : ℂ) ∈ ForwardTube d n ∧
      complexLorentzAction L (permAct σ (φ (t : ℂ))) ∈ ForwardTube d n := by
    intro t ht ht1
    have heq : φ (t : ℂ) = (1 - t) • realEmbed a + t • z := by
      ext k μ
      simp only [φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_sub, Complex.ofReal_one]
    simpa only [heq] using hseg t ht ht1
  let A : ℂ → (Fin n → Fin (d + 1) → ℂ) := fun w =>
    complexLorentzAction L (permAct σ (φ w))
  have hperm : Differentiable ℂ (fun w => permAct σ (φ w)) := by
    intro w
    apply differentiableAt_pi.mpr
    intro k
    exact ((differentiable_apply (σ k)).comp hφ).differentiableAt
  have hA : Differentiable ℂ A := by
    intro w
    apply differentiableAt_pi.mpr
    intro k
    apply differentiableAt_pi.mpr
    intro μ
    change DifferentiableAt ℂ (fun w => ∑ ν, L.val μ ν * (permAct σ (φ w)) k ν) w
    exact DifferentiableAt.fun_sum fun ν _ => (differentiableAt_const (L.val μ ν)).mul
      (differentiableAt_pi.mp (differentiableAt_pi.mp (hperm w) k) ν)
  let D : Set ℂ := φ ⁻¹' ForwardTube d n ∩ A ⁻¹' ForwardTube d n
  have hD : IsOpen D := (isOpen_forwardTube.preimage hφ.continuous).inter
    (isOpen_forwardTube.preimage hA.continuous)
  have hφaff : ∀ (u v : ℂ) (s t : ℝ), s + t = 1 →
      φ (s • u + t • v) = s • φ u + t • φ v := by
    intro u v s t hst
    have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    ext k μ
    change (1 - ((s : ℂ) * u + (t : ℂ) * v)) * (a k μ : ℂ) +
      ((s : ℂ) * u + (t : ℂ) * v) * z k μ =
      (s : ℂ) * ((1 - u) * (a k μ : ℂ) + u * z k μ) +
      (t : ℂ) * ((1 - v) * (a k μ : ℂ) + v * z k μ)
    linear_combination -(a k μ : ℂ) * hst'
  have hDconv : Convex ℝ D := by
    intro u hu v hv s t hs ht hst
    constructor
    · change φ (s • u + t • v) ∈ ForwardTube d n
      rw [hφaff u v s t hst]
      exact forwardTube_convex hu.1 hv.1 hs ht hst
    · change complexLorentzAction L (permAct σ (φ (s • u + t • v))) ∈ ForwardTube d n
      rw [hφaff u v s t hst]
      change complexLorentzAction L (s • permAct σ (φ u) + t • permAct σ (φ v)) ∈ ForwardTube d n
      rw [complexLorentzAction_real_linear]
      exact forwardTube_convex hu.2 hv.2 hs ht hst
  have h1 : (1 : ℂ) ∈ D := by simpa [D, A, hφ1] using And.intro hz hLz
  have hnear : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), φ (t : ℂ) ∈ interior U := by
    have hc := hφ.continuous.comp Complex.continuous_ofReal
    have ht : Tendsto (fun t : ℝ => φ (t : ℂ)) (nhds 0) (nhds (realEmbed a)) := by
      change Tendsto (φ ∘ Complex.ofReal) (nhds 0) (nhds (realEmbed a))
      simpa [hφ0] using (hc.continuousAt (x := 0)).tendsto
    exact (ht.eventually (interior_mem_nhds.mpr hU)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t := self_mem_nhdsWithin
  have hlt : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨t, ht, ht1, htU⟩ := (hpos.and (hlt.and hnear)).exists
  have htD : (t : ℂ) ∈ D := hφseg t ht ht1.le
  have hagree : (F ∘ φ) =ᶠ[nhds (t : ℂ)] (fun w => extendF F (permAct σ (φ w))) := by
    have hφU : ∀ᶠ w in nhds (t : ℂ), φ w ∈ interior U :=
      hφ.continuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds htU)
    filter_upwards [hφU, hD.mem_nhds htD] with w hwU hwD
    exact hlocal (φ w) ⟨interior_subset hwU, hwD.1⟩
  have hcinv := complex_lorentz_invariance n F hF_holo hF_real_inv
  have hFdiff : DifferentiableOn ℂ (F ∘ φ) D :=
    hF_holo.comp hφ.differentiableOn (fun _ hw => hw.1)
  have hGdiff : DifferentiableOn ℂ (fun w => extendF F (permAct σ (φ w))) D :=
    (extendF_holomorphicOn n F hF_holo hcinv).comp hperm.differentiableOn
      (fun _ hw => htoET _ hw.2)
  have hfreq : ∃ᶠ w in nhdsWithin (t : ℂ) {(t : ℂ)}ᶜ,
      (F ∘ φ) w = extendF F (permAct σ (φ w)) :=
    (hagree.filter_mono nhdsWithin_le_nhds).frequently
  have heq := identity_theorem_connected hD ⟨⟨1, h1⟩, hDconv.isPreconnected⟩
    (F ∘ φ) (fun w => extendF F (permAct σ (φ w))) hFdiff hGdiff (t : ℂ) htD hfreq h1
  simpa [hφ1] using heq

/-- Permutation agreement on every extended-tube overlap, using local
distributional uniqueness and fixed-Lorentz slices, not overlap connectivity. -/
theorem extendF_perm_eq_on_overlap
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (L : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (L.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Tendsto (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hF_local_dist : IsAdjacentLocallyCommutativeWeak d W)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ExtendedTube d n)
    (hσz : permAct σ z ∈ ExtendedTube d n) :
    extendF F (permAct σ z) = extendF F z := by
  by_cases hσ : σ = 1
  · subst σ
    rfl
  obtain ⟨Λ, w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  obtain ⟨M, u, hu, hσzu⟩ := Set.mem_iUnion.mp hσz
  have hperm : complexLorentzAction Λ (permAct σ w) = permAct σ z := by
    rw [hzw]
    rfl
  let L := M⁻¹ * Λ
  have hLw : complexLorentzAction L (permAct σ w) ∈ ForwardTube d n := by
    dsimp [L]
    rw [complexLorentzAction_mul, hperm, hσzu, complexLorentzAction_inv]
    exact hu
  have hσwET : permAct σ w ∈ ExtendedTube d n :=
    Set.mem_iUnion.mpr ⟨L⁻¹, complexLorentzAction L (permAct σ w), hLw,
      (complexLorentzAction_inv L _).symm⟩
  have hslice := extendF_perm_eq_on_forward_lorentz_slice F hF_holo hF_real_inv
    W hF_bv_dist hF_local_dist σ hσ L w hw hLw
  calc
    extendF F (permAct σ z) = extendF F (complexLorentzAction Λ (permAct σ w)) := by rw [hperm]
    _ = extendF F (permAct σ w) :=
      extendF_complex_lorentz_invariant n F hF_holo hF_real_inv Λ _ hσwET
    _ = F w := hslice.symm
    _ = extendF F w := (extendF_eq_on_forwardTube n F hF_holo hF_real_inv w hw).symm
    _ = extendF F z := by
      rw [hzw]
      exact (extendF_complex_lorentz_invariant n F hF_holo hF_real_inv Λ w
        (forwardTube_subset_extendedTube hw)).symm

end BHW.PermutationBoundary
