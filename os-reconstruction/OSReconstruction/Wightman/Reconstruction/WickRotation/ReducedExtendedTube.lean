/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ReducedBoundaryUniqueness















noncomputable section

open Complex Topology Set

namespace BHW

variable {d m : ℕ} [NeZero d]

/-- Auxiliary cumulative-coordinate kernel; it has no physical permutation
symmetry assumption. -/
def ReducedForwardTubePreInput.cumulative (F : ReducedForwardTubePreInput d m) :
    (Fin m → Fin (d + 1) → ℂ) → ℂ :=
  F.toFun ∘ diffCoordEquiv m d

theorem ReducedForwardTubePreInput.cumulative_holomorphic
    (F : ReducedForwardTubePreInput d m) :
    DifferentiableOn ℂ F.cumulative (ForwardTube d m) := by
  apply F.holomorphic.comp (diffCoordEquiv m d).differentiableOn
  intro z hz
  change diffCoordEquiv m d z ∈ ProductForwardCone d m
  rwa [forwardTube_eq_diffCoord_preimage] at hz

theorem ReducedForwardTubePreInput.cumulative_real_invariant
    (F : ReducedForwardTubePreInput d m)
    (R : LorentzLieGroup.RestrictedLorentzGroup d)
    (z : Fin m → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d m) :
    F.cumulative (fun k μ => ∑ ν, (R.val.val μ ν : ℂ) * z k ν) =
      F.cumulative z := by
  have hR : wightmanToLorentzGroup (lorentzGroupToWightman R) = R := by rfl
  have hz' : diffCoordEquiv m d z ∈ ReducedForwardTubeN d m := by
    change diffCoordEquiv m d z ∈ ProductForwardCone d m
    rwa [forwardTube_eq_diffCoord_preimage] at hz
  have hRz : complexLorentzAction (ComplexLorentzGroup.ofReal R)
      (diffCoordEquiv m d z) ∈ ReducedForwardTubeN d m := by
    rw [← diffCoordEquiv_action]
    change diffCoordEquiv m d _ ∈ ProductForwardCone d m
    exact (show complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈
      diffCoordEquiv m d ⁻¹' ProductForwardCone d m from
      (forwardTube_eq_diffCoord_preimage (n := m) (d := d)) ▸
        ofReal_preserves_forwardTube R z hz)
  have h := F.real_lorentz_invariant (lorentzGroupToWightman R) _ hz'
  rw [hR] at h
  change F.toFun (diffCoordEquiv m d
    (complexLorentzAction (ComplexLorentzGroup.ofReal R) z)) = _
  rw [diffCoordEquiv_action]
  exact h hRz

/-- Reduced unpermuted domain, in cumulative coordinates. Its equality with
the quotient image of absolute ET is proved below. -/
def reducedExtendedTubeN (d m : ℕ) : Set (ReducedNPointConfig d m) :=
  diffCoordEquiv m d '' ExtendedTube d m

theorem mem_reducedExtendedTubeN_iff (η : ReducedNPointConfig d m) :
    η ∈ reducedExtendedTubeN d m ↔
      ∃ (L : ComplexLorentzGroup d) (ξ : ReducedNPointConfig d m),
        ξ ∈ ReducedForwardTubeN d m ∧ complexLorentzAction L ξ = η := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨L, w, hw, hzw⟩ := mem_iUnion.mp hz
    refine ⟨L, diffCoordEquiv m d w, ?_, ?_⟩
    · change diffCoordEquiv m d w ∈ ProductForwardCone d m
      rwa [forwardTube_eq_diffCoord_preimage] at hw
    · rw [hzw, diffCoordEquiv_action]
      rfl
  · rintro ⟨L, ξ, hξ, rfl⟩
    refine ⟨complexLorentzAction L ((diffCoordEquiv m d).symm ξ), ?_, ?_⟩
    · apply mem_iUnion.mpr
      refine ⟨L, (diffCoordEquiv m d).symm ξ, ?_, rfl⟩
      rw [forwardTube_eq_diffCoord_preimage]
      simpa using hξ
    · simp only [diffCoordEquiv_action, ContinuousLinearEquiv.apply_symm_apply]
      rfl

theorem reducedExtendedTubeN_eq_image :
    reducedExtendedTubeN d m =
      reducedDiffMap (m + 1) d '' ExtendedTube d (m + 1) := by
  ext η
  rw [mem_reducedExtendedTubeN_iff]
  constructor
  · rintro ⟨L, ξ, hξ, rfl⟩
    refine ⟨complexLorentzAction L (safeSection d m ξ), ?_, ?_⟩
    · exact mem_iUnion.mpr ⟨L, safeSection d m ξ,
        safeSection_mem_forwardTube m ξ hξ, rfl⟩
    · rw [reducedDiffMap_action, reducedDiffMap_safeSection]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨L, w, hw, hzw⟩ := mem_iUnion.mp hz
    refine ⟨L, reducedDiffMap (m + 1) d w,
      ((mem_forwardTube_iff_basepoint_and_reducedDiff w).mp hw).2, ?_⟩
    rw [hzw, reducedDiffMap_action]

/-- Complex-Lorentz extension in reduced variables, before permutation gluing. -/
def ReducedForwardTubePreInput.extend (F : ReducedForwardTubePreInput d m) :
    ReducedNPointConfig d m → ℂ :=
  extendF F.cumulative ∘ (diffCoordEquiv m d).symm

theorem ReducedForwardTubePreInput.extend_holomorphic
    (F : ReducedForwardTubePreInput d m) :
    DifferentiableOn ℂ F.extend (reducedExtendedTubeN d m) := by
  apply (extendF_holomorphicOn m F.cumulative F.cumulative_holomorphic
    (complex_lorentz_invariance m F.cumulative F.cumulative_holomorphic
      F.cumulative_real_invariant)).comp (diffCoordEquiv m d).symm.differentiableOn
  rintro η ⟨z, hz, rfl⟩
  simpa using hz

theorem ReducedForwardTubePreInput.extend_eq
    (F : ReducedForwardTubePreInput d m)
    (η : ReducedNPointConfig d m) (hη : η ∈ ReducedForwardTubeN d m) :
    F.extend η = F.toFun η := by
  have hmem : (diffCoordEquiv m d).symm η ∈ ForwardTube d m := by
    rw [forwardTube_eq_diffCoord_preimage]
    simpa using hη
  have h := extendF_eq_on_forwardTube m F.cumulative F.cumulative_holomorphic
    F.cumulative_real_invariant _ hmem
  simpa [extend, cumulative] using h

theorem ReducedForwardTubePreInput.extend_lorentz_invariant
    (F : ReducedForwardTubePreInput d m)
    (L : ComplexLorentzGroup d)
    (η : ReducedNPointConfig d m) (hη : η ∈ reducedExtendedTubeN d m) :
    F.extend (complexLorentzAction L η) = F.extend η := by
  obtain ⟨z, hz, rfl⟩ := hη
  have h := extendF_complex_lorentz_invariant m F.cumulative
    F.cumulative_holomorphic F.cumulative_real_invariant L z hz
  change extendF F.cumulative ((diffCoordEquiv m d).symm
    (complexLorentzAction L (diffCoordEquiv m d z))) = _
  rw [← diffCoordEquiv_action]
  simpa [extend] using h

theorem ReducedForwardTubePreInput.complex_lorentz_invariant
    (F : ReducedForwardTubePreInput d m)
    (L : ComplexLorentzGroup d) (η : ReducedNPointConfig d m)
    (hη : η ∈ ReducedForwardTubeN d m)
    (hLη : complexLorentzAction L η ∈ ReducedForwardTubeN d m) :
    F.toFun (complexLorentzAction L η) = F.toFun η := by
  have hmem : η ∈ reducedExtendedTubeN d m :=
    (mem_reducedExtendedTubeN_iff η).mpr ⟨1, η, hη, complexLorentzAction_one η⟩
  rw [← F.extend_eq _ hLη, ← F.extend_eq _ hη]
  exact F.extend_lorentz_invariant L η hmem

theorem ReducedForwardTubePreInput.pullback_complex_lorentz_invariant
    (F : ReducedForwardTubePreInput d m)
    (L : ComplexLorentzGroup d) (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1))
    (hLz : complexLorentzAction L z ∈ ForwardTube d (m + 1)) :
    pullbackReducedExtension F.toFun (complexLorentzAction L z) =
      pullbackReducedExtension F.toFun z := by
  change F.toFun (reducedDiffMap (m + 1) d (complexLorentzAction L z)) = _
  rw [reducedDiffMap_action]
  apply F.complex_lorentz_invariant L
    _ ((mem_forwardTube_iff_basepoint_and_reducedDiff z).mp hz).2
  simpa only [reducedDiffMap_action] using
    ((mem_forwardTube_iff_basepoint_and_reducedDiff _).mp hLz).2

/-- The absolute unpermuted extension factors through successive differences. -/
theorem ReducedForwardTubePreInput.extend_pullback
    (F : ReducedForwardTubePreInput d m)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d (m + 1)) :
    extendF (pullbackReducedExtension F.toFun) z =
      F.extend (reducedDiffMap (m + 1) d z) := by
  obtain ⟨L, w, hw, hzw⟩ := mem_iUnion.mp hz
  have hext : extendF (pullbackReducedExtension F.toFun) z =
      pullbackReducedExtension F.toFun w := by
    unfold extendF
    have hex : ∃ w', w' ∈ ForwardTube d (m + 1) ∧
        ∃ L' : ComplexLorentzGroup d, z = complexLorentzAction L' w' :=
      ⟨w, hw, L, hzw⟩
    rw [dif_pos hex]
    rcases hex.choose_spec with ⟨hw', L', hz'⟩
    exact extendF_preimage_eq_of_cinv (m + 1) (pullbackReducedExtension F.toFun)
      F.pullback_complex_lorentz_invariant hw' hw (hz'.symm.trans hzw)
  have hred := ((mem_forwardTube_iff_basepoint_and_reducedDiff w).mp hw).2
  have hredET : reducedDiffMap (m + 1) d w ∈ reducedExtendedTubeN d m :=
    (mem_reducedExtendedTubeN_iff _).mpr ⟨1, _, hred, complexLorentzAction_one _⟩
  rw [hext, hzw, reducedDiffMap_action, F.extend_lorentz_invariant L _ hredET,
    F.extend_eq _ hred]
  rfl

def ReducedForwardTubeInput.preInput
    {W : (n : ℕ) → SchwartzNPoint d n → ℂ} (F : ReducedForwardTubeInput W m) :
    ReducedForwardTubePreInput d m where
  toFun := F.toFun
  holomorphic := F.holomorphic
  real_lorentz_invariant := F.real_lorentz_invariant

end BHW
