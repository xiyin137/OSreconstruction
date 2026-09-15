/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.ComplexLieGroups.Connectedness.Permutation

/-!
# Permutation locality on real spacelike boundary tests

This layer is independent of permutation continuation. In particular, the
one-sided pairing theorem below only requires the permuted real support to
lie in the extended tube, not both orders of the real configuration.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace MeasureTheory

namespace BHW.PermutationBoundary

variable {d : ℕ}

/-- Permutations preserve the ambient product volume on `NPointDomain d n`. -/
theorem integral_perm_eq_self {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (σ k)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- Light-cone convention bridge for real-edge approach rays. -/
theorem bhw_inOpenForwardCone_iff_wightman [NeZero d]
    (η : Fin (d + 1) → ℝ) :
    BHW.InOpenForwardCone d η ↔ _root_.InOpenForwardCone d η := by
  unfold BHW.InOpenForwardCone _root_.InOpenForwardCone
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    ring_nf
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    ring_nf

abbrev permuteSchwartz {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv) f

@[simp] theorem permuteSchwartz_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    permuteSchwartz (d := d) σ f x = f (fun i => x (σ i)) := by
  rfl

@[simp] theorem permuteSchwartz_one {n : ℕ} (f : SchwartzNPoint d n) :
    permuteSchwartz (d := d) (1 : Equiv.Perm (Fin n)) f = f := by
  ext x
  simp [permuteSchwartz]

@[simp] theorem permuteSchwartz_mul {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (f : SchwartzNPoint d n) :
    permuteSchwartz (d := d) (σ * τ) f =
      permuteSchwartz (d := d) σ (permuteSchwartz (d := d) τ f) := by
  ext x
  simp [permuteSchwartz]

private theorem permute_support_jost {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ JostSet d n) :
    ∀ x : NPointDomain d n, permuteSchwartz (d := d) σ f x ≠ 0 → x ∈ JostSet d n := by
  intro x hx
  have hy : (fun i => x (σ i)) ∈ JostSet d n := hf _ hx
  simpa using jostSet_permutation_invariant (d := d) (n := n) σ.symm hy

private theorem areSpacelikeSeparated_of_jost_pair (x y : Fin (d + 1) → ℝ)
    (h : IsSpacelike d (fun μ => x μ - y μ)) :
    MinkowskiSpace.AreSpacelikeSeparated d x y := by
  unfold MinkowskiSpace.AreSpacelikeSeparated MinkowskiSpace.IsSpacelike
  have heq : MinkowskiSpace.minkowskiNormSq d (x - y) =
      ∑ μ, minkowskiSignature d μ * (x μ - y μ) ^ 2 := by
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    apply Finset.sum_congr rfl
    intro μ _
    simp [MinkowskiSpace.metricSignature, minkowskiSignature, Pi.sub_apply, pow_two]
    ring_nf
  rw [heq]
  exact h

/-- Adjacent weak locality gives every permutation on pairwise-spacelike tests. -/
theorem distributional_perm_invariant_on_jost_support
    (n : ℕ)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_local_dist : IsAdjacentLocallyCommutativeWeak d W)
    (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ JostSet d n)
    (σ : Equiv.Perm (Fin n)) :
    W n (permuteSchwartz (d := d) σ f) = W n f := by
  refine Fin.Perm.adjSwap_induction (n := n)
    (motive := fun τ => W n (permuteSchwartz (d := d) τ f) = W n f) ?_ ?_ σ
  · simp [permuteSchwartz]
  · intro τ i hi hτ
    let gτ : SchwartzNPoint d n := permuteSchwartz (d := d) τ f
    have hsupp :
        ∀ x : NPointDomain d n, gτ x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) := by
      intro x hx
      have hxJ : x ∈ JostSet d n :=
        permute_support_jost (d := d) (n := n) τ f hf x hx
      have hij : i ≠ ⟨i.val + 1, hi⟩ := by
        intro hEq
        have : i.val = i.val + 1 := by simpa using congrArg Fin.val hEq
        omega
      exact areSpacelikeSeparated_of_jost_pair (d := d) (x i) (x ⟨i.val + 1, hi⟩)
        (hxJ.2 i ⟨i.val + 1, hi⟩ hij)
    have hswap0 :
        W n gτ =
          W n (permuteSchwartz (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) gτ) := by
      refine hF_local_dist n i hi gτ
        (permuteSchwartz (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) gτ) hsupp ?_
      intro x
      change permuteSchwartz (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) gτ x =
        gτ (fun k => x ((Equiv.swap i ⟨i.val + 1, hi⟩) k))
      rw [permuteSchwartz_apply]
    calc
      W n (permuteSchwartz (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * τ) f)
          = W n (permuteSchwartz (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) gτ) := by
              simp [gτ, permuteSchwartz_mul]
      _ = W n gτ := hswap0.symm
      _ = W n f := hτ

/-- On spacelike test support, the permuted extended branch has the original
boundary distribution. The unpermuted real support need not lie in ET. -/
theorem extendF_perm_pairing_eq_boundary_of_jost_support [NeZero d] {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (L : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (L.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Tendsto (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hF_local_dist : IsAdjacentLocallyCommutativeWeak d W)
    (s : Equiv.Perm (Fin n)) (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_jost : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ JostSet d n)
    (hf_permET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      realEmbed (fun k => x (s k)) ∈ ExtendedTube d n) :
    (∫ x : NPointDomain d n, extendF F (realEmbed (fun k => x (s k))) * f x) = W n f := by
  have hF_cinv : ∀ (L : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction L z ∈ ForwardTube d n →
      F (complexLorentzAction L z) = F z :=
    complex_lorentz_invariance n F hF_holo hF_real_inv
  let e : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) s⁻¹).toContinuousLinearEquiv
  let g : SchwartzNPoint d n := permuteSchwartz s⁻¹ f
  have hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ) :=
    hf_compact.comp_homeomorph e.toHomeomorph
  have hg_ET : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      realEmbed x ∈ ExtendedTube d n := by
    intro x hx
    have heq : tsupport (g : NPointDomain d n → ℂ) =
        e.toHomeomorph ⁻¹' tsupport (f : NPointDomain d n → ℂ) :=
      tsupport_comp_eq_preimage (g := (f : NPointDomain d n → ℂ)) e.toHomeomorph
    have hxs : (fun k => x (s⁻¹ k)) ∈ tsupport (f : NPointDomain d n → ℂ) := by
      rw [heq] at hx
      exact hx
    simpa using hf_permET _ hxs
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη := (inForwardCone_iff_mem_forwardConeAbs η).2 hη_abs
  have hη_FT : ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) ∈ ForwardTube d n := by
    intro x ε hε k
    have him : (fun μ => ((x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I -
        (if hk : k.val = 0 then 0 else
          fun μ => (x ⟨k.val - 1, by omega⟩ μ : ℂ) +
            ε * (η ⟨k.val - 1, by omega⟩ μ : ℂ) * Complex.I) μ).im) =
        ε • (fun μ => η k μ - (if hk : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩) μ) := by
      ext μ
      by_cases hk : k.val = 0 <;>
        simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Pi.smul_apply]
      ring
    change InOpenForwardCone d _
    rw [him]
    exact (bhw_inOpenForwardCone_iff_wightman _).2 (inOpenForwardCone_smul d ε hε _ (hη k))
  have hpair : (∫ x : NPointDomain d n, extendF F (realEmbed x) * g x) = W n g :=
    tendsto_nhds_unique
      (tendsto_extendF_boundary_integral_of_hasCompactSupport_ET n F hF_holo hF_cinv
        g hg_compact η hη_FT hg_ET)
      (hF_bv_dist g η hη)
  calc
    (∫ x : NPointDomain d n, extendF F (realEmbed (fun k => x (s k))) * f x) =
        ∫ x : NPointDomain d n, extendF F (realEmbed x) * g x := by
      simpa [g, permuteSchwartz] using
        integral_perm_eq_self s (fun x : NPointDomain d n => extendF F (realEmbed x) * g x)
    _ = W n g := hpair
    _ = W n f := distributional_perm_invariant_on_jost_support n W hF_local_dist f hf_jost s⁻¹

end BHW.PermutationBoundary
