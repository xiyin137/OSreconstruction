import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-- Coordinate permutation of a Schwartz test function. -/
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

/-- Permuting the coordinates of a compactly supported Schwartz test function
preserves compact support. -/
theorem permuteSchwartz_hasCompactSupport {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (permuteSchwartz (d := d) σ f : NPointDomain d n → ℂ) := by
  let e : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv
  simpa [permuteSchwartz, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    hf.comp_homeomorph e.toHomeomorph

/-- Topological support of a permuted Schwartz test is the preimage of the
original topological support under the coordinate permutation. -/
theorem tsupport_permuteSchwartz {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) :
    tsupport (permuteSchwartz (d := d) σ f : NPointDomain d n → ℂ) =
      (((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv :
          NPointDomain d n ≃L[ℝ] NPointDomain d n).toHomeomorph) ⁻¹'
        tsupport (f : NPointDomain d n → ℂ) := by
  let e : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv
  simpa [permuteSchwartz, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    (tsupport_comp_eq_preimage
      (g := (f : NPointDomain d n → ℂ)) e.toHomeomorph)

/-- Jost support is preserved by coordinate permutation of test functions. -/
theorem permute_support_jost {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n)
    (hf : ∀ x : NPointDomain d n, f x ≠ 0 → x ∈ JostSet d n) :
    ∀ x : NPointDomain d n,
      permuteSchwartz (d := d) σ f x ≠ 0 → x ∈ JostSet d n := by
  intro x hx
  have hy : (fun i => x (σ i)) ∈ JostSet d n := hf _ hx
  simpa using jostSet_permutation_invariant (d := d) (n := n) σ.symm hy

/-- Permutations preserve the ambient product volume on `NPointDomain d n`. -/
theorem integral_perm_eq_self {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (σ k)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- Compact-test pairing equality on a real-open Jost edge implies pointwise
equality of the two `extendF` real-edge traces there.

This is the non-circular analytic spine needed by the OS route: the hard input
is the compactly supported edge-distribution equality `hEdge`; this theorem
only turns it into pointwise equality on the chosen real-open edge by the
existing compact-support uniqueness theorem. -/
theorem extendF_perm_eq_on_realOpen_of_edgePairingEquality [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ET : ∀ x ∈ V, realEmbed x ∈ ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            extendF F (realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            extendF F (realEmbed x) * φ x) :
    ∀ x ∈ V,
      extendF F (realEmbed (fun k => x (σ k))) =
        extendF F (realEmbed x) := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hExtend_cont : ContinuousOn (extendF F) (ExtendedTube d n) :=
    (extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn
  have hrealEmbed_cont :
      Continuous (realEmbed : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))
  have hpermReal_cont :
      Continuous (fun x : NPointDomain d n => realEmbed (fun k => x (σ k))) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply (σ k)))
  let gV : NPointDomain d n → ℂ :=
    fun x => extendF F (realEmbed (fun k => x (σ k)))
  let hVf : NPointDomain d n → ℂ :=
    fun x => extendF F (realEmbed x)
  have hgV_cont : ContinuousOn gV V := by
    refine hExtend_cont.comp hpermReal_cont.continuousOn ?_
    intro x hx
    exact hV_permET x hx
  have hhVf_cont : ContinuousOn hVf V := by
    refine hExtend_cont.comp hrealEmbed_cont.continuousOn ?_
    intro x hx
    exact hV_ET x hx
  have hEqOn : Set.EqOn gV hVf V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hgV_cont hhVf_cont ?_
    intro φ hφ_compact hφ_tsupport
    exact hEdge φ hφ_compact hφ_tsupport
  intro x hx
  exact hEqOn hx

/-- Connected-domain propagation from a real-open edge pairing equality to the
whole explicit extended-tube/permuted-extended-tube overlap.

The geometric input is the connectedness of the explicit overlap
`{z | z ∈ ExtendedTube d n ∧ permAct σ z ∈ ExtendedTube d n}`.  The analytic
input is the compact-test edge pairing equality on a nonempty real-open slice
`V` of that overlap. -/
theorem extendF_perm_overlap_of_edgePairingEquality [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hOverlap_conn :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ ExtendedTube d n ∧ permAct (d := d) σ z ∈ ExtendedTube d n})
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_ET : ∀ x ∈ V, realEmbed x ∈ ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            extendF F (realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            extendF F (realEmbed x) * φ x) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | z ∈ ExtendedTube d n ∧ permAct (d := d) σ z ∈ ExtendedTube d n}
  have hperm_cont :
      Continuous (fun z : Fin n → Fin (d + 1) → ℂ => permAct (d := d) σ z) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (σ k))
  have hD_open : IsOpen D := by
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hz
    exact hz.1
  have hD_sub_permET : D ⊆ {z | (fun k => z (σ k)) ∈ ExtendedTube d n} := by
    intro z hz
    simpa [D, permAct] using hz.2
  have hV_sub_D : ∀ x ∈ V, realEmbed x ∈ D := by
    intro x hx
    exact ⟨hV_ET x hx, by simpa [D, permAct, realEmbed] using hV_permET x hx⟩
  have hV_eq : ∀ x ∈ V,
      extendF F (fun k => (realEmbed x) (σ k)) = extendF F (realEmbed x) := by
    intro x hx
    simpa [realEmbed] using
      extendF_perm_eq_on_realOpen_of_edgePairingEquality
        (d := d) n F hF_holo hF_lorentz σ V hV_open hV_ET hV_permET hEdge x hx
  have hmain :=
    extendF_perm_eq_on_connectedDomain_of_realOpen
      (d := d) n F hF_holo hF_lorentz σ D hD_open hOverlap_conn
      hD_sub_ET hD_sub_permET V hV_open hV_ne hV_sub_D hV_eq
  intro z hz hσz
  have hzD : z ∈ D := ⟨hz, hσz⟩
  simpa [D, permAct] using hmain z hzD

end BHW
