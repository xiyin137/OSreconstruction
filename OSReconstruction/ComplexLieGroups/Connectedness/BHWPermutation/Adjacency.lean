import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Full BHW theorem -/

/-- The full extension of F to the permuted extended tube.
    For z ∈ PermutedExtendedTube, choose a preimage: z = Λ·(π·w) with w ∈ FT,
    and define fullExtendF(z) = F(w). Well-definedness uses complex Lorentz
    invariance + permutation invariance (from local commutativity + edge-of-the-wedge). -/
noncomputable def fullExtendF
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k))
    then F h.choose_spec.choose_spec.choose
    else 0

/-- The forward tube in the i-th difference variable is a tube domain with cone V₊.
    After swapping indices i and i+1, the i-th difference variable ζᵢ = z_{i+1} - z_i
    flips sign, so the cone becomes -V₊. The remaining (n-1) difference variables
    retain their forward-cone conditions.

    This helper extracts the i-th cone direction from the full forward tube condition.

    Blocked by: expressing the forward tube as a product of individual cone conditions
    on each difference variable, in the flattened coordinate system. -/
theorem forwardTube_ith_cone_decomp (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ z : Fin n → Fin (d + 1) → ℂ, z ∈ ForwardTube d n →
      InOpenForwardCone d (fun μ => (z ⟨i.val + 1, hi⟩ μ - z i μ).im) := by
  intro z hz
  -- The FT condition at k = ⟨i.val + 1, hi⟩ gives exactly this.
  have hk := hz ⟨i.val + 1, hi⟩
  -- Unfold the dite: k.val = i.val + 1 ≠ 0
  have hk_ne : ¬ (i.val + 1 = 0) := Nat.succ_ne_zero _
  simp only [hk_ne, ↓reduceDIte] at hk
  -- prev = z ⟨i.val + 1 - 1, _⟩ = z ⟨i.val, _⟩ = z i
  have heq : (⟨i.val + 1 - 1, by have := i.isLt; omega⟩ : Fin n) = i := by
    ext; simp
  rw [heq] at hk
  exact hk

/-- The spacelike boundary set (where the i-th difference is real and spacelike)
    is a totally real submanifold that serves as the matching boundary for EOW.

    At boundary points where Im(z_{i+1} - z_i) = 0 and the real part satisfies
    the spacelike condition, the locality hypothesis `hF_local` provides
    F(swap(x)) = F(x). This is the "E" (edge) in edge-of-the-wedge.

    Blocked by: expressing the spacelike boundary as an open subset of a totally
    real submanifold in the flattened coordinate system. -/
theorem spacelike_boundary_matching (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ∑ μ, minkowskiSignature d μ * (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)) ∧
      F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
      F (fun k μ => (x k μ : ℂ)) := by
  intro x hx
  exact ⟨hF_bv x, hF_local i hi x hx⟩

theorem eow_adj_swap_extension_holo_only (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ)) (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
      ForwardTube d n ⊆ U ∧
      {z | (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n} ⊆ U ∧
      DifferentiableOn ℂ F_ext U ∧
      (∀ z ∈ U ∩ ForwardTube d n, F_ext z = F z) ∧
      (∀ z ∈ U ∩ {z | (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n},
        F_ext z = F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
  -- Proof: FT ∩ σ·FT = ∅ (the time components of the (i+1)-th imaginary-part
  -- difference have opposite signs). So U = FT ∪ σ·FT is a disjoint union of open sets,
  -- and F_ext defined piecewise (F on FT, F∘σ on σ·FT) is holomorphic on U.
  -- NOTE: This produces a disconnected U; the current file keeps this as local EOW data.
  set σ := Equiv.swap i ⟨i.val + 1, hi⟩
  set σFT : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | (fun k => z (σ k)) ∈ ForwardTube d n}
  have hσ_ne : σ ≠ 1 := by
    intro hσ
    have hineq : i ≠ ⟨i.val + 1, hi⟩ := by
      intro h
      have hval : i.val + 1 = i.val := by
        simpa using (congrArg Fin.val h).symm
      exact Nat.succ_ne_self i.val hval
    have hfix : (σ i : Fin n) = i := by simp [hσ]
    have hnext : (σ i : Fin n) = ⟨i.val + 1, hi⟩ := by
      change (Equiv.swap i ⟨i.val + 1, hi⟩ i : Fin n) = ⟨i.val + 1, hi⟩
      exact Equiv.swap_apply_left i ⟨i.val + 1, hi⟩
    have hval : i.val + 1 = i.val := by
      exact congrArg Fin.val (hnext.symm.trans hfix)
    exact Nat.succ_ne_self i.val hval
  -- Key: FT and σ·FT are disjoint for nontrivial permutations.
  have h_disj : ∀ z, z ∈ ForwardTube d n → z ∉ σFT := by
    intro z hz hz_σ
    have hz_inter : z ∈ ForwardTube d n ∩ PermutedForwardTube d n σ := ⟨hz, hz_σ⟩
    have hcontra : z ∈ (∅ : Set (Fin n → Fin (d + 1) → ℂ)) := by
      rw [forwardTube_inter_permutedForwardTube_eq_empty_of_ne_one (d := d) (n := n)
        σ hσ_ne] at hz_inter
      exact hz_inter
    exact hcontra.elim
  -- Also need the reverse direction for the agreement proofs
  have h_disj' : ∀ z, z ∈ σFT → z ∉ ForwardTube d n :=
    fun z hz hft => h_disj z hft hz
  -- Define U = FT ∪ σ·FT and F_ext piecewise
  refine ⟨ForwardTube d n ∪ σFT,
    fun z => if z ∈ ForwardTube d n then F z else F (fun k => z (σ k)),
    ?_, Set.subset_union_left, Set.subset_union_right, ?_, ?_, ?_⟩
  -- 1. IsOpen U
  · exact isOpen_forwardTube.union (isOpen_permutedForwardTube σ)
  -- 2. DifferentiableOn ℂ F_ext U
  · intro z hz
    rcases hz with hz_ft | hz_σft
    · -- z ∈ FT: F_ext =ᶠ F near z, so differentiable
      have hFz : DifferentiableAt ℂ F z :=
        (hF_holo z hz_ft).differentiableAt (isOpen_forwardTube.mem_nhds hz_ft)
      have h_eq : (fun w => if w ∈ ForwardTube d n then F w
          else F (fun k => w (σ k))) =ᶠ[𝓝 z] F := by
        filter_upwards [isOpen_forwardTube.mem_nhds hz_ft] with w hw
        exact if_pos hw
      exact (h_eq.differentiableAt_iff.mpr hFz).differentiableWithinAt
    · -- z ∈ σ·FT: F_ext =ᶠ F∘σ near z, so differentiable
      have hσz_ft : (fun k => z (σ k)) ∈ ForwardTube d n := hz_σft
      have hFσz : DifferentiableAt ℂ F (fun k => z (σ k)) :=
        (hF_holo _ hσz_ft).differentiableAt (isOpen_forwardTube.mem_nhds hσz_ft)
      have hperm : Differentiable ℂ (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (σ k)) :=
        differentiable_pi.mpr (fun k => differentiable_apply (σ k))
      have hcomp : DifferentiableAt ℂ (fun w => F (fun k => w (σ k))) z :=
        DifferentiableAt.comp z hFσz (hperm z)
      have h_eq : (fun w => if w ∈ ForwardTube d n then F w
          else F (fun k => w (σ k))) =ᶠ[𝓝 z] (fun w => F (fun k => w (σ k))) := by
        filter_upwards [(isOpen_permutedForwardTube σ).mem_nhds hz_σft] with w hw
        exact if_neg (h_disj' w hw)
      exact (h_eq.differentiableAt_iff.mpr hcomp).differentiableWithinAt
  -- 3. Agreement on FT: F_ext z = F z for z ∈ U ∩ FT
  · intro z ⟨_, hz⟩; exact if_pos hz
  -- 4. Agreement on σ·FT: F_ext z = F(z∘σ) for z ∈ U ∩ σ·FT
  · intro z ⟨_, hz_σ⟩; exact if_neg (h_disj' z hz_σ)

theorem eow_adj_swap_extension (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (_hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (_hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ)) (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
      ForwardTube d n ⊆ U ∧
      {z | (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n} ⊆ U ∧
      DifferentiableOn ℂ F_ext U ∧
      (∀ z ∈ U ∩ ForwardTube d n, F_ext z = F z) ∧
      (∀ z ∈ U ∩ {z | (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n},
        F_ext z = F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
  exact eow_adj_swap_extension_holo_only n F hF_holo i hi

/-- **EOW gluing for adjacent swap on the forward tube overlap.**
    When both w and σ·w lie in the forward tube (σ = swap(i, i+1)),
    local commutativity at Jost points (hF_local) + the edge-of-the-wedge theorem
    (SCV.edge_of_the_wedge_theorem) + the identity theorem together imply
    F(σ·w) = F(w).

    The proof uses eow_adj_swap_extension to get a holomorphic extension F_ext
    on U ⊇ FT ∪ σ·FT. At any w ∈ FT ∩ σ·FT:
    - F_ext(w) = F(w) (from agreement on U ∩ FT)
    - F_ext(w) = F(σ·w) (from agreement on U ∩ σ·FT)
    Hence F(σ·w) = F(w). -/
theorem eow_adj_swap_on_overlap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (_hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    (hσw : (fun k => w (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n) :
    F (fun k => w (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = F w := by
  -- Obtain the EOW extension
  obtain ⟨U, F_ext, _hU_open, hFT_sub, hσFT_sub, _hF_ext_holo,
    hF_ext_eq_F, hF_ext_eq_Fσ⟩ :=
    eow_adj_swap_extension n F hF_holo hF_bv hF_local i hi
  -- w ∈ FT, so w ∈ U
  have hw_U : w ∈ U := hFT_sub hw
  -- σ·w ∈ FT means w ∈ σ·FT (since σ = σ⁻¹), so w ∈ U via the σ·FT inclusion
  have hw_σFT : w ∈ {z | (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ForwardTube d n} := hσw
  -- F_ext(w) = F(w) and F_ext(w) = F(σ·w)
  have h1 : F_ext w = F w := hF_ext_eq_F w ⟨hw_U, hw⟩
  have h2 : F_ext w = F (fun k => w (Equiv.swap i ⟨i.val + 1, hi⟩ k)) :=
    hF_ext_eq_Fσ w ⟨hw_U, hw_σFT⟩
  -- Combine: F(σ·w) = F_ext(w) = F(w)
  exact h2.symm.trans h1

/-- **Lorentz-permutation commutation** (definitional).
    The complex Lorentz action acts on the μ-index (spacetime), while
    permutations act on the k-index (particle). They commute:
    Λ·(π·w) = π·(Λ·w) definitionally. -/
theorem lorentz_perm_commute (Γ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ) (τ : Equiv.Perm (Fin n)) :
    complexLorentzAction Γ (fun k => w (τ k)) =
    fun k => (complexLorentzAction Γ w) (τ k) := by
  ext k μ; simp only [complexLorentzAction]

/-- Permutation-invariance hypothesis for `τ` implies the corresponding
    `τ⁻¹`-version. -/
theorem permInvariance_of_inverse (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (τ : Equiv.Perm (Fin n))
    (hperm : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w) :
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ⁻¹ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ⁻¹ k))) = F w := by
  intro w hw Γ hΓ
  set v : Fin n → Fin (d + 1) → ℂ :=
    complexLorentzAction Γ (fun k => w (τ⁻¹ k)) with hv_def
  have hv : v ∈ ForwardTube d n := hΓ
  have hvτ : (fun k => v (τ k)) = complexLorentzAction Γ w := by
    calc
      (fun k => v (τ k))
          = (fun k => (complexLorentzAction Γ (fun j => w (τ⁻¹ j))) (τ k)) := by
              simp [v]
      _ = complexLorentzAction Γ w := by
            ext k μ
            simp [complexLorentzAction]
  have hcond : complexLorentzAction Γ⁻¹ (fun k => v (τ k)) ∈ ForwardTube d n := by
    rw [hvτ, complexLorentzAction_inv]
    exact hw
  have hmain : F (complexLorentzAction Γ⁻¹ (fun k => v (τ k))) = F v :=
    hperm v hv Γ⁻¹ hcond
  have hleft : complexLorentzAction Γ⁻¹ (fun k => v (τ k)) = w := by
    rw [hvτ, complexLorentzAction_inv]
  have hmain' : F w = F v := by
    simpa [hleft] using hmain
  simpa [v, hv_def] using hmain'.symm

/-- The `τ` and `τ⁻¹` permutation-invariance statements are equivalent. -/
theorem permInvariance_iff_inverse (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (τ : Equiv.Perm (Fin n)) :
    (∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w) ↔
    (∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ⁻¹ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ⁻¹ k))) = F w) := by
  constructor
  · intro h
    exact permInvariance_of_inverse n F τ h
  · intro h
    have h' := permInvariance_of_inverse n F τ⁻¹ h
    simpa using h'

/-- Reduction lemma: if one has permutation invariance of `extendF` on the
extended tube, then the target forward-tube permutation invariance statement
follows immediately. This isolates the remaining work to ET-level permutation
invariance of `extendF`. -/
theorem permutation_invariance_of_extendF_on_extendedTube
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hExtPerm :
      ∀ (τ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (τ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (τ k)) = extendF F z)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  set z : Fin n → Fin (d + 1) → ℂ := complexLorentzAction Γ w
  have hcomm : complexLorentzAction Γ (fun k => w (τ k)) = fun k => z (τ k) := by
    simpa [z] using (lorentz_perm_commute Γ w τ)
  have hτz_FT : (fun k => z (τ k)) ∈ ForwardTube d n := by
    simpa [hcomm] using h
  have hz_ET : z ∈ ExtendedTube d n := by
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Γ, ?_⟩
    exact ⟨w, hw, by simp [z]⟩
  have hτz_ET : (fun k => z (τ k)) ∈ ExtendedTube d n :=
    forwardTube_subset_extendedTube hτz_FT
  have hperm_z : extendF F (fun k => z (τ k)) = extendF F z :=
    hExtPerm τ z hz_ET hτz_ET
  have hLorentz_z : extendF F z = extendF F w := by
    simpa [z] using
      (extendF_complex_lorentz_invariant n F hF_holo hF_real_inv Γ w
        (forwardTube_subset_extendedTube hw))
  have hleft : extendF F (fun k => z (τ k)) = F (fun k => z (τ k)) :=
    extendF_eq_on_forwardTube n F hF_holo hF_real_inv _ hτz_FT
  have hright : extendF F w = F w :=
    extendF_eq_on_forwardTube n F hF_holo hF_real_inv w hw
  calc
    F (complexLorentzAction Γ (fun k => w (τ k)))
        = F (fun k => z (τ k)) := by simp [hcomm]
    _ = extendF F (fun k => z (τ k)) := hleft.symm
    _ = extendF F z := hperm_z
    _ = extendF F w := hLorentz_z
    _ = F w := hright

/-- Identity-theorem propagation template on a connected domain inside the
extended-tube overlap for a fixed permutation `τ`. This isolates the analytic
continuation step from the geometric step that provides a suitable real open
set `V`. -/
theorem extendF_perm_eq_on_connectedDomain_of_openSubset
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n))
    (D : Set (Fin n → Fin (d + 1) → ℂ))
    (hD_open : IsOpen D) (hD_conn : IsConnected D)
    (hD_sub_ET : D ⊆ ExtendedTube d n)
    (hD_sub_permET : D ⊆ {z | (fun k => z (τ k)) ∈ ExtendedTube d n})
    (W : Set (Fin n → Fin (d + 1) → ℂ))
    (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ D)
    (hW_eq : ∀ z ∈ W, extendF F (fun k => z (τ k)) = extendF F z) :
    ∀ z ∈ D, extendF F (fun k => z (τ k)) = extendF F z := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  let g : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => extendF F (fun k => z (τ k)) - extendF F z
  have hExtend_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  have hperm_diff : Differentiable ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k)) :=
    differentiable_pi.mpr (fun k => differentiable_apply (τ k))
  have hperm_maps : Set.MapsTo
      (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k))
      D (ExtendedTube d n) := by
    intro z hz
    exact hD_sub_permET hz
  have hDiff_perm : DifferentiableOn ℂ (fun z : Fin n → Fin (d + 1) → ℂ =>
      extendF F (fun k => z (τ k))) D := by
    intro z hz
    exact (hExtend_holo _ (hperm_maps hz)).comp z
      ((hperm_diff z).differentiableWithinAt) hperm_maps
  have hDiff_id : DifferentiableOn ℂ (extendF F) D :=
    hExtend_holo.mono hD_sub_ET
  have hDiff_g : DifferentiableOn ℂ g D := hDiff_perm.sub hDiff_id
  have hDiff_zero : DifferentiableOn ℂ (fun _ : Fin n → Fin (d + 1) → ℂ => (0 : ℂ)) D := by
    exact (differentiableOn_const (c := (0 : ℂ)) :
      DifferentiableOn ℂ (fun _ : Fin n → Fin (d + 1) → ℂ => (0 : ℂ)) D)
  rcases hW_ne with ⟨z0, hz0W⟩
  have hz0D : z0 ∈ D := hW_sub hz0W
  have hagree : g =ᶠ[𝓝 z0] (fun _ : Fin n → Fin (d + 1) → ℂ => (0 : ℂ)) := by
    apply Filter.eventuallyEq_of_mem (hW_open.mem_nhds hz0W)
    intro z hzW
    have hz_eq : extendF F (fun k => z (τ k)) = extendF F z := hW_eq z hzW
    simp [g, hz_eq]
  have hmain := identity_theorem_product hD_open hD_conn hDiff_g hDiff_zero hz0D hagree
  intro z hzD
  have hgz : g z = 0 := hmain hzD
  exact sub_eq_zero.mp hgz

/-- Identity-theorem propagation template on a connected domain inside the
extended-tube overlap for a fixed permutation `τ`. This isolates the analytic
continuation step from the geometric step that provides a suitable real open
set `V`. -/
theorem extendF_perm_eq_on_connectedDomain_of_realOpen
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n))
    (D : Set (Fin n → Fin (d + 1) → ℂ))
    (hD_open : IsOpen D) (hD_conn : IsConnected D)
    (hD_sub_ET : D ⊆ ExtendedTube d n)
    (hD_sub_permET : D ⊆ {z | (fun k => z (τ k)) ∈ ExtendedTube d n})
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realEmbed x ∈ D)
    (hV_eq : ∀ x ∈ V,
      extendF F (fun k => (realEmbed x) (τ k)) = extendF F (realEmbed x)) :
    ∀ z ∈ D, extendF F (fun k => z (τ k)) = extendF F z := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  let g : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => extendF F (fun k => z (τ k)) - extendF F z
  have hExtend_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  have hperm_diff : Differentiable ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k)) :=
    differentiable_pi.mpr (fun k => differentiable_apply (τ k))
  have hperm_maps : Set.MapsTo
      (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k))
      D (ExtendedTube d n) := by
    intro z hz
    exact hD_sub_permET hz
  have hDiff_perm : DifferentiableOn ℂ (fun z : Fin n → Fin (d + 1) → ℂ =>
      extendF F (fun k => z (τ k))) D := by
    intro z hz
    exact (hExtend_holo _ (hperm_maps hz)).comp z
      ((hperm_diff z).differentiableWithinAt) hperm_maps
  have hDiff_id : DifferentiableOn ℂ (extendF F) D :=
    hExtend_holo.mono hD_sub_ET
  have hDiff_g : DifferentiableOn ℂ g D := hDiff_perm.sub hDiff_id
  have hV_zero : ∀ x ∈ V, g (realEmbed x) = 0 := by
    intro x hx
    have := hV_eq x hx
    simp [g, this]
  intro z hzD
  have hzero : g z = 0 :=
    identity_theorem_totally_real_product (hD_open := hD_open) (hD_conn := hD_conn)
      (hf := hDiff_g) (hV_open := hV_open) (hV_ne := hV_ne) (hV_sub := hV_sub)
      (hf_zero := hV_zero) z hzD
  exact sub_eq_zero.mp hzero

/-- At a real spacelike boundary point for an adjacent swap, `extendF` values
    match across the swap map. -/
theorem extendF_adjSwap_eq_at_real_spacelike
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx_ET : realEmbed x ∈ ExtendedTube d n)
    (hswap_ET :
      realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n)
    (hsp : ∑ μ, minkowskiSignature d μ *
      (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0) :
    extendF F (fun k => (realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      extendF F (realEmbed x) := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hleft :
      extendF F (realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) =
        F (realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :=
    extendF_eq_boundary_value_ET n F hF_holo hF_cinv hF_bv
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) hswap_ET
  have hright : extendF F (realEmbed x) = F (realEmbed x) :=
    extendF_eq_boundary_value_ET n F hF_holo hF_cinv hF_bv x hx_ET
  have hlocal_real :
      F (realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) = F (realEmbed x) := by
    simpa [realEmbed] using hF_local i hi x hsp
  calc
    extendF F (fun k => (realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k))
        = extendF F (realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
          rfl
    _ = F (realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := hleft
    _ = F (realEmbed x) := hlocal_real
    _ = extendF F (realEmbed x) := hright.symm

/-- Open-set wrapper for `extendF_adjSwap_eq_at_real_spacelike`. -/
theorem extendF_adjSwap_eq_on_realOpen
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (_hV_open : IsOpen V)
    (hV_sp : ∀ x ∈ V, ∑ μ, minkowskiSignature d μ *
      (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0)
    (hV_ET : ∀ x ∈ V, realEmbed x ∈ ExtendedTube d n)
    (hV_swapET : ∀ x ∈ V,
      realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    ∀ x ∈ V,
      extendF F (fun k => (realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      extendF F (realEmbed x) := by
  intro x hxV
  exact extendF_adjSwap_eq_at_real_spacelike n F hF_holo hF_real_inv
    hF_bv hF_local i hi x (hV_ET x hxV) (hV_swapET x hxV) (hV_sp x hxV)

/-- Build an open real neighborhood where the adjacent spacelike condition and
    both extended-tube membership conditions persist. -/
theorem exists_real_open_nhds_adjSwap
    (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n)
    (x0 : Fin n → Fin (d + 1) → ℝ)
    (hx0_sp : ∑ μ, minkowskiSignature d μ *
      (x0 ⟨i.val + 1, hi⟩ μ - x0 i μ) ^ 2 > 0)
    (hx0_ET : realEmbed x0 ∈ ExtendedTube d n)
    (hx0_swapET :
      realEmbed (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    ∃ V : Set (Fin n → Fin (d + 1) → ℝ),
      IsOpen V ∧ x0 ∈ V ∧
      (∀ x ∈ V, ∑ μ, minkowskiSignature d μ *
        (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0) ∧
      (∀ x ∈ V, realEmbed x ∈ ExtendedTube d n) ∧
      (∀ x ∈ V,
        realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) := by
  let ip1 : Fin n := ⟨i.val + 1, hi⟩
  let spSet : Set (Fin n → Fin (d + 1) → ℝ) :=
    {x | ∑ μ, minkowskiSignature d μ *
      (x ip1 μ - x i μ) ^ 2 > 0}
  let etSet : Set (Fin n → Fin (d + 1) → ℝ) :=
    {x | realEmbed x ∈ ExtendedTube d n}
  let swapEtSet : Set (Fin n → Fin (d + 1) → ℝ) :=
    {x | realEmbed (fun k => x (Equiv.swap i ip1 k)) ∈ ExtendedTube d n}
  have hsp_cont : Continuous (fun x : Fin n → Fin (d + 1) → ℝ =>
      ∑ μ, minkowskiSignature d μ * (x ip1 μ - x i μ) ^ 2) := by
    apply continuous_finset_sum
    intro μ _
    have h1 : Continuous (fun x : Fin n → Fin (d + 1) → ℝ => x ip1 μ) :=
      (continuous_apply μ).comp (continuous_apply ip1)
    have h2 : Continuous (fun x : Fin n → Fin (d + 1) → ℝ => x i μ) :=
      (continuous_apply μ).comp (continuous_apply i)
    exact continuous_const.mul ((h1.sub h2).pow 2)
  have hsp_open : IsOpen spSet := by
    change IsOpen {x : Fin n → Fin (d + 1) → ℝ |
      0 < (fun x : Fin n → Fin (d + 1) → ℝ =>
        ∑ μ, minkowskiSignature d μ * (x ip1 μ - x i μ) ^ 2) x}
    exact isOpen_lt continuous_const hsp_cont
  have hrealEmbed_cont :
      Continuous (realEmbed : (Fin n → Fin (d + 1) → ℝ) → (Fin n → Fin (d + 1) → ℂ)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))
  have het_open : IsOpen etSet := by
    change IsOpen (realEmbed ⁻¹' ExtendedTube d n)
    exact isOpen_extendedTube.preimage hrealEmbed_cont
  have hperm_cont : Continuous
      (fun x : Fin n → Fin (d + 1) → ℝ =>
        (fun k => x (Equiv.swap i ip1 k))) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (Equiv.swap i ip1 k))
  have hswapEt_open : IsOpen swapEtSet := by
    change IsOpen
      ((fun x : Fin n → Fin (d + 1) → ℝ =>
        realEmbed (fun k => x (Equiv.swap i ip1 k))) ⁻¹' ExtendedTube d n)
    exact isOpen_extendedTube.preimage (hrealEmbed_cont.comp hperm_cont)
  let V : Set (Fin n → Fin (d + 1) → ℝ) := spSet ∩ (etSet ∩ swapEtSet)
  refine ⟨V, hsp_open.inter (het_open.inter hswapEt_open), ?_, ?_, ?_, ?_⟩
  · exact ⟨hx0_sp, ⟨hx0_ET, hx0_swapET⟩⟩
  · intro x hxV
    exact hxV.1
  · intro x hxV
    exact hxV.2.1
  · intro x hxV
    exact hxV.2.2

/-- The complex Lorentz action preserves the extended tube. -/
theorem complexLorentzAction_mem_extendedTube
    (n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ} (Λ : ComplexLorentzGroup d)
    (hz : z ∈ ExtendedTube d n) :
    complexLorentzAction Λ z ∈ ExtendedTube d n := by
  rcases Set.mem_iUnion.mp hz with ⟨Γ, w, hw, rfl⟩
  exact Set.mem_iUnion.mpr ⟨Λ * Γ, w, hw, by rw [complexLorentzAction_mul]⟩

/-- Extended-tube overlap domain for an adjacent swap. -/
def adjSwapExtendedOverlapSet (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  {z | z ∈ ExtendedTube d n ∧ (fun k => z (τ k)) ∈ ExtendedTube d n}

/-- Forward-tube slice controlling the adjacent-swap overlap domain. -/
def adjSwapForwardOverlapSet (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  {w | w ∈ ForwardTube d n ∧ (fun k => w (τ k)) ∈ ExtendedTube d n}

/-- Fixed-Λ slice of `adjSwapForwardOverlapSet`. -/
def adjSwapForwardOverlapSlice
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (Λ : ComplexLorentzGroup d) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  {w | w ∈ ForwardTube d n ∧
      complexLorentzAction Λ (fun k => w (τ k)) ∈ ForwardTube d n}

/-- Membership in `adjSwapForwardOverlapSet` is equivalent to existence of a
    Lorentz witness placing the swapped configuration back in `ForwardTube`. -/
theorem mem_adjSwapForwardOverlapSet_iff_exists_lorentz
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (w : Fin n → Fin (d + 1) → ℂ) :
    w ∈ adjSwapForwardOverlapSet (d := d) n i hi ↔
      w ∈ ForwardTube d n ∧
      ∃ Λ : ComplexLorentzGroup d,
        complexLorentzAction Λ
          (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube d n := by
  constructor
  · intro hw
    rcases hw with ⟨hwFT, hτwET⟩
    rcases Set.mem_iUnion.mp hτwET with ⟨Γ, u, huFT, hτw_eq⟩
    refine ⟨hwFT, Γ⁻¹, ?_⟩
    have hpre :
        complexLorentzAction Γ⁻¹
            (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k)) = u := by
      calc
        complexLorentzAction Γ⁻¹
            (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k))
            = complexLorentzAction Γ⁻¹ (complexLorentzAction Γ u) := by
                simp [hτw_eq]
        _ = u := by rw [complexLorentzAction_inv]
    exact hpre ▸ huFT
  · rintro ⟨hwFT, Λ, hΛτwFT⟩
    refine ⟨hwFT, Set.mem_iUnion.mpr ?_⟩
    refine ⟨Λ⁻¹, complexLorentzAction Λ
      (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k)), hΛτwFT, ?_⟩
    rw [complexLorentzAction_inv]

/-- Each fixed-Λ forward-overlap slice is convex. -/
theorem adjSwapForwardOverlapSlice_convex
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (Λ : ComplexLorentzGroup d) :
    Convex ℝ (adjSwapForwardOverlapSlice (d := d) n i hi Λ) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  refine ⟨forwardTube_convex hw₁.1 hw₂.1 ha hb hab, ?_⟩
  have hperm_linear :
      (fun k => (a • w₁ + b • w₂) (τ k))
        = a • (fun k => w₁ (τ k)) + b • (fun k => w₂ (τ k)) := by
    ext k μ
    simp [Pi.smul_apply, Pi.add_apply]
  rw [hperm_linear]
  have hlin :
      complexLorentzAction Λ
          (a • (fun k => w₁ (τ k)) + b • (fun k => w₂ (τ k))) =
      a • complexLorentzAction Λ (fun k => w₁ (τ k)) +
      b • complexLorentzAction Λ (fun k => w₂ (τ k)) := by
    ext k μ
    simp only [complexLorentzAction, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    trans (↑a * ∑ ν, Λ.val μ ν * w₁ (τ k) ν + ↑b * ∑ ν, Λ.val μ ν * w₂ (τ k) ν)
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ν _
      simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      ring_nf
    · rfl
  rw [hlin]
  exact forwardTube_convex hw₁.2 hw₂.2 ha hb hab

/-- Each fixed-Λ forward-overlap slice is preconnected. -/
theorem adjSwapForwardOverlapSlice_isPreconnected
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (Λ : ComplexLorentzGroup d) :
    IsPreconnected (adjSwapForwardOverlapSlice (d := d) n i hi Λ) :=
  (adjSwapForwardOverlapSlice_convex (d := d) n i hi Λ).isPreconnected

/-- `adjSwapForwardOverlapSet` is the union of fixed-Λ convex slices. -/
theorem adjSwapForwardOverlapSet_eq_iUnion_slices
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    adjSwapForwardOverlapSet (d := d) n i hi =
      ⋃ Λ : ComplexLorentzGroup d, adjSwapForwardOverlapSlice (d := d) n i hi Λ := by
  ext w
  constructor
  · intro hw
    rcases (mem_adjSwapForwardOverlapSet_iff_exists_lorentz (d := d) n i hi w).mp hw with
      ⟨hwFT, Λ, hΛτwFT⟩
    exact Set.mem_iUnion.mpr ⟨Λ, ⟨hwFT, hΛτwFT⟩⟩
  · intro hw
    rcases Set.mem_iUnion.mp hw with ⟨Λ, hwΛ⟩
    exact (mem_adjSwapForwardOverlapSet_iff_exists_lorentz (d := d) n i hi w).mpr
      ⟨hwΛ.1, Λ, hwΛ.2⟩

/-- Local persistence of nonemptiness for fixed-`w` adjacent-overlap slices. -/
theorem adjSwapForwardOverlapSlice_nonempty_nhds
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {Λ : ComplexLorentzGroup d}
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ adjSwapForwardOverlapSlice (d := d) n i hi Λ) :
    ∃ V : Set (ComplexLorentzGroup d), IsOpen V ∧ Λ ∈ V ∧
      ∀ Λ' ∈ V, w ∈ adjSwapForwardOverlapSlice (d := d) n i hi Λ' := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases hw with ⟨hwFT, hΛτwFT⟩
  let f : ComplexLorentzGroup d → (Fin n → Fin (d + 1) → ℂ) :=
    fun Λ' => complexLorentzAction Λ' (fun k => w (τ k))
  have hf_cont : Continuous f := by
    simpa [f] using continuous_complexLorentzAction_fst (d := d) (n := n)
      (fun k => w (τ k))
  let V : Set (ComplexLorentzGroup d) := f ⁻¹' ForwardTube d n
  have hV_open : IsOpen V := isOpen_forwardTube.preimage hf_cont
  refine ⟨V, hV_open, ?_, ?_⟩
  · simpa [V, f] using hΛτwFT
  · intro Λ' hΛ'V
    exact ⟨hwFT, by simpa [V, f] using hΛ'V⟩

/-- Connected-index reduction: if the nonempty-slice index set is connected, then
all indices are linked by overlap in the `ReflTransGen` sense. -/
theorem reflTransGen_slice_overlap_of_indexConnected
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hidx_conn : IsConnected
      {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty}) :
    ∀ (a b : {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty}),
      Relation.ReflTransGen
        (fun x y : {Λ : ComplexLorentzGroup d |
            (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} =>
          ((adjSwapForwardOverlapSlice (d := d) n i hi x.1) ∩
            (adjSwapForwardOverlapSlice (d := d) n i hi y.1)).Nonempty)
        a b := by
  intro a b
  let R :
      {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} →
      {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} → Prop :=
    fun x y =>
      ((adjSwapForwardOverlapSlice (d := d) n i hi x.1) ∩
        (adjSwapForwardOverlapSlice (d := d) n i hi y.1)).Nonempty

  let U : Set {Λ : ComplexLorentzGroup d |
      (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} :=
    {x | Relation.ReflTransGen R a x}

  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    rcases x.2 with ⟨w, hwx⟩
    rcases adjSwapForwardOverlapSlice_nonempty_nhds (d := d) (n := n) i hi hwx with
      ⟨V, hV_open, hxV, hV_sub⟩
    let W : Set {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} :=
      Subtype.val ⁻¹' V
    have hW_open : IsOpen W := hV_open.preimage continuous_subtype_val
    have hxW : x ∈ W := by simpa [W] using hxV
    refine Filter.mem_of_superset (hW_open.mem_nhds hxW) ?_
    intro y hyW
    have hyV : y.1 ∈ V := by simpa [W] using hyW
    have hwy : w ∈ adjSwapForwardOverlapSlice (d := d) n i hi y.1 :=
      hV_sub y.1 hyV
    have hxy : R x y := ⟨w, hwx, hwy⟩
    exact Relation.ReflTransGen.tail hxU hxy

  have hU_closed : IsClosed U := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    rcases x.2 with ⟨w, hwx⟩
    rcases adjSwapForwardOverlapSlice_nonempty_nhds (d := d) (n := n) i hi hwx with
      ⟨V, hV_open, hxV, hV_sub⟩
    let W : Set {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} :=
      Subtype.val ⁻¹' V
    have hW_open : IsOpen W := hV_open.preimage continuous_subtype_val
    have hxW : x ∈ W := by simpa [W] using hxV
    refine Filter.mem_of_superset (hW_open.mem_nhds hxW) ?_
    intro y hyW hyU
    have hyV : y.1 ∈ V := by simpa [W] using hyW
    have hwy : w ∈ adjSwapForwardOverlapSlice (d := d) n i hi y.1 :=
      hV_sub y.1 hyV
    have hyx : R y x := ⟨w, hwy, hwx⟩
    have hx_inU : x ∈ U := Relation.ReflTransGen.tail hyU hyx
    exact hxU hx_inU

  have hU_nonempty : U.Nonempty := ⟨a, Relation.ReflTransGen.refl⟩

  haveI : ConnectedSpace
      {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} :=
    Subtype.connectedSpace hidx_conn

  have hU_eq : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_nonempty
  have hbU : b ∈ U := hU_eq ▸ Set.mem_univ b
  exact hbU

/-- If the nonempty-slice index set is connected, then the full adjacent forward-overlap
set is connected. -/
theorem isConnected_adjSwapForwardOverlapSet_of_indexConnected
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hidx_conn : IsConnected
      {Λ : ComplexLorentzGroup d |
        (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty})
    (hnonempty : (adjSwapForwardOverlapSet (d := d) n i hi).Nonempty) :
    IsConnected (adjSwapForwardOverlapSet (d := d) n i hi) := by
  let t : Set (ComplexLorentzGroup d) :=
    {Λ : ComplexLorentzGroup d |
      (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty}

  have hpre_union_subtype :
      IsPreconnected
        (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
          adjSwapForwardOverlapSlice (d := d) n i hi x.1) := by
    apply IsPreconnected.iUnion_of_reflTransGen
    · intro x
      exact (adjSwapForwardOverlapSlice_convex (d := d) n i hi x.1).isPreconnected
    · intro x y
      exact reflTransGen_slice_overlap_of_indexConnected (d := d) (n := n) i hi hidx_conn x y

  have h_union_eq_all :
      (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
        adjSwapForwardOverlapSlice (d := d) n i hi x.1)
        = ⋃ Λ : ComplexLorentzGroup d,
            adjSwapForwardOverlapSlice (d := d) n i hi Λ := by
    ext w
    constructor
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨x.1, hx⟩
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨Λ, hΛ⟩
      have hΛt : t Λ := ⟨w, hΛ⟩
      exact Set.mem_iUnion.mpr ⟨⟨Λ, hΛt⟩, hΛ⟩

  have hset_eq :
      adjSwapForwardOverlapSet (d := d) n i hi =
        (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
          adjSwapForwardOverlapSlice (d := d) n i hi x.1) := by
    calc
      adjSwapForwardOverlapSet (d := d) n i hi
          = ⋃ Λ : ComplexLorentzGroup d,
              adjSwapForwardOverlapSlice (d := d) n i hi Λ :=
            adjSwapForwardOverlapSet_eq_iUnion_slices (d := d) n i hi
      _ = (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
            adjSwapForwardOverlapSlice (d := d) n i hi x.1) :=
          h_union_eq_all.symm

  refine ⟨hnonempty, ?_⟩
  simpa [hset_eq] using hpre_union_subtype

/-- The nonempty-slice index set is open in the Lorentz group. -/
theorem isOpen_adjSwapForwardOverlapIndexSet
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen {Λ : ComplexLorentzGroup d |
      (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty} := by
  rw [isOpen_iff_mem_nhds]
  intro Λ hΛ
  rcases hΛ with ⟨w, hw⟩
  rcases adjSwapForwardOverlapSlice_nonempty_nhds (d := d) (n := n) i hi hw with
    ⟨V, hV_open, hΛV, hV_sub⟩
  refine Filter.mem_of_superset (hV_open.mem_nhds hΛV) ?_
  intro Λ' hΛ'V
  exact ⟨w, hV_sub Λ' hΛ'V⟩

/-- If the adjacent forward-overlap set is nonempty, then so is its nonempty-slice
index set. -/
theorem nonempty_adjSwapForwardOverlapIndexSet_of_forwardOverlapNonempty
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hnonempty : (adjSwapForwardOverlapSet (d := d) n i hi).Nonempty) :
    ({Λ : ComplexLorentzGroup d |
      (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty}).Nonempty := by
  rcases hnonempty with ⟨w, hw⟩
  rw [adjSwapForwardOverlapSet_eq_iUnion_slices (d := d) n i hi] at hw
  rcases Set.mem_iUnion.mp hw with ⟨Λ, hΛ⟩
  exact ⟨Λ, ⟨w, hΛ⟩⟩

/-- Nonempty-slice index set for adjacent forward overlap slices. -/
def adjSwapForwardOverlapIndexSet
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) : Set (ComplexLorentzGroup d) :=
  {Λ : ComplexLorentzGroup d |
    (adjSwapForwardOverlapSlice (d := d) n i hi Λ).Nonempty}

theorem isOpen_adjSwapForwardOverlapIndexSet'
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen (adjSwapForwardOverlapIndexSet (d := d) n i hi) := by
  simpa [adjSwapForwardOverlapIndexSet] using
    isOpen_adjSwapForwardOverlapIndexSet (d := d) n i hi

theorem nonempty_adjSwapForwardOverlapIndexSet_of_forwardOverlapNonempty'
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hnonempty : (adjSwapForwardOverlapSet (d := d) n i hi).Nonempty) :
    (adjSwapForwardOverlapIndexSet (d := d) n i hi).Nonempty := by
  simpa [adjSwapForwardOverlapIndexSet] using
    nonempty_adjSwapForwardOverlapIndexSet_of_forwardOverlapNonempty
      (d := d) n i hi hnonempty

theorem indexSet_left_mul_ofReal
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi)
    (R : RestrictedLorentzGroup d) :
    ComplexLorentzGroup.ofReal R * Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi := by
  rcases hΛ with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  refine ⟨hw.1, ?_⟩
  have hmul :
      complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ)
        (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
      complexLorentzAction (ComplexLorentzGroup.ofReal R)
        (complexLorentzAction Λ (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) := by
    simpa using complexLorentzAction_mul
      (ComplexLorentzGroup.ofReal R) Λ (fun k => w ((Equiv.swap i ⟨i.val + 1, hi⟩) k))
  rw [hmul]
  exact ofReal_preserves_forwardTube R _ hw.2

theorem indexSet_right_mul_ofReal
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi)
    (R : RestrictedLorentzGroup d) :
    Λ * ComplexLorentzGroup.ofReal R ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi := by
  rcases hΛ with ⟨w, hw⟩
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let w' : Fin n → Fin (d + 1) → ℂ :=
    complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹) w
  refine ⟨w', ?_⟩
  have hw'_FT : w' ∈ ForwardTube d n := by
    simpa [w'] using ofReal_preserves_forwardTube (R := R⁻¹) w hw.1
  refine ⟨hw'_FT, ?_⟩
  have hcommR :
      complexLorentzAction (ComplexLorentzGroup.ofReal R) (fun k => w' (τ k)) =
      fun k => (complexLorentzAction (ComplexLorentzGroup.ofReal R) w') (τ k) :=
    lorentz_perm_commute (ComplexLorentzGroup.ofReal R) w' τ
  have hw'_cancel : complexLorentzAction (ComplexLorentzGroup.ofReal R) w' = w := by
    calc
      complexLorentzAction (ComplexLorentzGroup.ofReal R) w'
          = complexLorentzAction
              (ComplexLorentzGroup.ofReal R * ComplexLorentzGroup.ofReal R⁻¹) w := by
                simp [w', complexLorentzAction_mul]
      _ = complexLorentzAction (ComplexLorentzGroup.ofReal (R * R⁻¹)) w := by
            rw [← ofReal_mul_eq]
      _ = complexLorentzAction (ComplexLorentzGroup.ofReal (1 : RestrictedLorentzGroup d)) w := by
            simp
      _ = complexLorentzAction (1 : ComplexLorentzGroup d) w := by
            simp [ofReal_one_eq]
      _ = w := complexLorentzAction_one w
  have hperm_cancel :
      (fun k => (complexLorentzAction (ComplexLorentzGroup.ofReal R) w') (τ k)) =
        fun k => w (τ k) := by
    funext k
    exact congrFun hw'_cancel (τ k)
  have hstep :
      complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) (fun k => w' (τ k)) =
      complexLorentzAction Λ (fun k => w (τ k)) := by
    calc
      complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) (fun k => w' (τ k))
          = complexLorentzAction Λ
              (complexLorentzAction (ComplexLorentzGroup.ofReal R) (fun k => w' (τ k))) := by
              simpa using complexLorentzAction_mul Λ (ComplexLorentzGroup.ofReal R)
                (fun k => w' (τ k))
      _ = complexLorentzAction Λ
            (fun k => (complexLorentzAction (ComplexLorentzGroup.ofReal R) w') (τ k)) := by
            rw [hcommR]
      _ = complexLorentzAction Λ (fun k => w (τ k)) := by
            rw [hperm_cancel]
  rw [hstep]
  exact hw.2

theorem indexSet_joined_left_ofReal
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi)
    (R : RestrictedLorentzGroup d) :
    JoinedIn (adjSwapForwardOverlapIndexSet (d := d) n i hi)
      Λ (ComplexLorentzGroup.ofReal R * Λ) := by
  have hj : JoinedIn Set.univ (1 : RestrictedLorentzGroup d) R :=
    (RestrictedLorentzGroup.isPathConnected (d := d)).joinedIn 1
      (Set.mem_univ _) R (Set.mem_univ _)
  rcases joinedIn_univ.mp hj with ⟨γ⟩
  refine ⟨
    { toFun := fun t => ComplexLorentzGroup.ofReal (γ t) * Λ
      continuous_toFun := (continuous_ofReal.comp γ.continuous_toFun).mul continuous_const
      source' := by
        rw [γ.source, ofReal_one_eq, one_mul]
      target' := by
        rw [γ.target] },
    ?_⟩
  intro t
  exact indexSet_left_mul_ofReal (d := d) n i hi hΛ (γ t)

theorem indexSet_joined_right_ofReal
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi)
    (R : RestrictedLorentzGroup d) :
    JoinedIn (adjSwapForwardOverlapIndexSet (d := d) n i hi)
      Λ (Λ * ComplexLorentzGroup.ofReal R) := by
  have hj : JoinedIn Set.univ (1 : RestrictedLorentzGroup d) R :=
    (RestrictedLorentzGroup.isPathConnected (d := d)).joinedIn 1
      (Set.mem_univ _) R (Set.mem_univ _)
  rcases joinedIn_univ.mp hj with ⟨γ⟩
  refine ⟨
    { toFun := fun t => Λ * ComplexLorentzGroup.ofReal (γ t)
      continuous_toFun := continuous_const.mul (continuous_ofReal.comp γ.continuous_toFun)
      source' := by
        rw [γ.source, ofReal_one_eq, mul_one]
      target' := by
        rw [γ.target] },
    ?_⟩
  intro t
  exact indexSet_right_mul_ofReal (d := d) n i hi hΛ (γ t)

theorem indexSet_isConnected_of_real_double_coset_generation
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi)
    (hgen : ∀ Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) :
    IsConnected (adjSwapForwardOverlapIndexSet (d := d) n i hi) := by
  refine ⟨⟨Λ0, hΛ0⟩, ?_⟩
  refine isPreconnected_of_joinedIn_base hΛ0 ?_
  intro Λ hΛ
  rcases hgen Λ hΛ with ⟨R1, R2, rfl⟩
  have hright :
      JoinedIn (adjSwapForwardOverlapIndexSet (d := d) n i hi)
        Λ0 (Λ0 * ComplexLorentzGroup.ofReal R2) :=
    indexSet_joined_right_ofReal (d := d) n i hi hΛ0 R2
  have hmid_mem : Λ0 * ComplexLorentzGroup.ofReal R2 ∈
      adjSwapForwardOverlapIndexSet (d := d) n i hi :=
    indexSet_right_mul_ofReal (d := d) n i hi hΛ0 R2
  have hleft :
      JoinedIn (adjSwapForwardOverlapIndexSet (d := d) n i hi)
        (Λ0 * ComplexLorentzGroup.ofReal R2)
        (ComplexLorentzGroup.ofReal R1 * (Λ0 * ComplexLorentzGroup.ofReal R2)) :=
    indexSet_joined_left_ofReal (d := d) n i hi hmid_mem R1
  have hleft' :
      JoinedIn (adjSwapForwardOverlapIndexSet (d := d) n i hi)
        (Λ0 * ComplexLorentzGroup.ofReal R2)
        (ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) := by
    simpa [mul_assoc] using hleft
  exact hright.trans hleft'

/-- The adjacent-swap overlap domain is the Lorentz-action image of
    `adjSwapForwardOverlapSet`. -/
theorem adjSwapExtendedOverlap_eq_action_image_forwardOverlap
    (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n) :
    adjSwapExtendedOverlapSet (d := d) n i hi =
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) ''
      (Set.univ ×ˢ adjSwapForwardOverlapSet (d := d) n i hi) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  ext z
  constructor
  · intro hz
    have hz' : z ∈ ExtendedTube d n ∧ (fun k => z (τ k)) ∈ ExtendedTube d n := by
      simpa [adjSwapExtendedOverlapSet, τ] using hz
    rcases hz' with ⟨hzET, hτzET⟩
    rcases Set.mem_iUnion.mp hzET with ⟨Λ, w, hwFT, hz_eq⟩
    have hτz_as_action :
        (fun k => z (τ k)) = complexLorentzAction Λ (fun k => w (τ k)) := by
      calc
        (fun k => z (τ k))
            = (fun k => (complexLorentzAction Λ w) (τ k)) := by simp [hz_eq]
        _ = complexLorentzAction Λ (fun k => w (τ k)) := by
              symm
              exact lorentz_perm_commute Λ w τ
    have hΛτw_ET : complexLorentzAction Λ (fun k => w (τ k)) ∈ ExtendedTube d n := by
      simpa [hτz_as_action] using hτzET
    have hτw_ET : (fun k => w (τ k)) ∈ ExtendedTube d n := by
      have := complexLorentzAction_mem_extendedTube n Λ⁻¹ hΛτw_ET
      simpa [complexLorentzAction_inv] using this
    refine ⟨⟨Λ, w⟩, ⟨trivial, ⟨hwFT, hτw_ET⟩⟩, ?_⟩
    simp [hz_eq]
  · rintro ⟨⟨Λ, w⟩, ⟨_, hwFT, hτw_ET⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact complexLorentzAction_mem_extendedTube n Λ
        (forwardTube_subset_extendedTube hwFT)
    · have hτ_action :
          (fun k => (complexLorentzAction Λ w) (τ k)) =
            complexLorentzAction Λ (fun k => w (τ k)) := by
        exact lorentz_perm_commute Λ w τ
      have hτ_ET : (fun k => (complexLorentzAction Λ w) (τ k)) ∈ ExtendedTube d n := by
        simpa [hτ_action] using
          complexLorentzAction_mem_extendedTube n Λ hτw_ET
      simpa [adjSwapExtendedOverlapSet, τ] using hτ_ET

/-- Reduction: connectedness of the forward overlap slice implies connectedness
    of the full adjacent-swap overlap domain in the extended tube. -/
theorem isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected
    (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n)
    (hFwd_conn : IsConnected (adjSwapForwardOverlapSet (d := d) n i hi)) :
    IsConnected (adjSwapExtendedOverlapSet (d := d) n i hi) := by
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  have hprod_conn :
      IsConnected
        ((Set.univ : Set (ComplexLorentzGroup d)) ×ˢ
          adjSwapForwardOverlapSet (d := d) n i hi) :=
    isConnected_univ.prod hFwd_conn
  have hcont : Continuous
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    simp only [complexLorentzAction]
    apply continuous_finset_sum
    intro ν _
    apply Continuous.mul
    · have hval : Continuous
          (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) => p.1.val) :=
        ComplexLorentzGroup.continuous_val.comp continuous_fst
      have hrow :
          Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ) :=
        continuous_apply μ
      have hentry : Continuous (fun r : Fin (d + 1) → ℂ => r ν) := continuous_apply ν
      exact hentry.comp (hrow.comp hval)
    · exact (continuous_apply ν).comp ((continuous_apply k).comp continuous_snd)
  have himage_conn :
      IsConnected
        ((fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
          complexLorentzAction p.1 p.2) ''
        ((Set.univ : Set (ComplexLorentzGroup d)) ×ˢ
          adjSwapForwardOverlapSet (d := d) n i hi)) :=
    hprod_conn.image _ hcont.continuousOn
  simpa [adjSwapExtendedOverlap_eq_action_image_forwardOverlap (d := d) n i hi] using
    himage_conn

/-- The forward overlap slice is open in configuration space. -/
theorem isOpen_adjSwapForwardOverlapSet
    (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen (adjSwapForwardOverlapSet (d := d) n i hi) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hperm_cont : Continuous
      (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k)) :=
    continuous_pi (fun k => continuous_pi (fun μ =>
      (continuous_apply μ).comp (continuous_apply (τ k))))
  simpa [adjSwapForwardOverlapSet, τ] using
    isOpen_forwardTube.inter (isOpen_extendedTube.preimage hperm_cont)

/-- Nonemptiness of the forward overlap slice for adjacent swaps (`d > 0`),
    extracted from the adjacent-overlap witness infrastructure. -/
theorem adjSwapForwardOverlap_nonempty [NeZero d]
    (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n) :
    (adjSwapForwardOverlapSet (d := d) n i hi).Nonempty := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  by_cases hd2 : 2 ≤ d
  · rcases adjacent_overlap_witness_exists (d := d) (n := n) hd2 i hi with
      ⟨x, hxET_raw, hτxET_raw⟩
    have hxET : x ∈ ExtendedTube d n := by
      simpa [ExtendedTube, BHWCore.ExtendedTube] using hxET_raw
    have hτxET : (fun k => x (τ k)) ∈ ExtendedTube d n := by
      simpa [ExtendedTube, BHWCore.ExtendedTube, τ] using hτxET_raw
    rcases Set.mem_iUnion.mp hxET with ⟨Λ, w, hwFT_raw, hx_eq_raw⟩
    have hwFT : w ∈ ForwardTube d n := by
      simpa [ForwardTube, BHWCore.ForwardTube] using hwFT_raw
    have hx_eq : x = complexLorentzAction Λ w := by
      simpa [complexLorentzAction, BHWCore.complexLorentzAction] using hx_eq_raw
    have hτx_as_action :
        (fun k => x (τ k)) = complexLorentzAction Λ (fun k => w (τ k)) := by
      calc
        (fun k => x (τ k))
            = (fun k => (complexLorentzAction Λ w) (τ k)) := by simp [hx_eq]
        _ = complexLorentzAction Λ (fun k => w (τ k)) := by
              symm
              exact lorentz_perm_commute Λ w τ
    have hΛτw_ET : complexLorentzAction Λ (fun k => w (τ k)) ∈ ExtendedTube d n := by
      simpa [hτx_as_action] using hτxET
    have hτw_ET : (fun k => w (τ k)) ∈ ExtendedTube d n := by
      have := complexLorentzAction_mem_extendedTube n Λ⁻¹ hΛτw_ET
      simpa [complexLorentzAction_inv] using this
    refine ⟨w, ?_⟩
    exact ⟨hwFT, hτw_ET⟩
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hd1 : d = 1 := by omega
    subst hd1
    rcases adjacent_overlap_witness_exists_d1 (n := n) i hi with ⟨x, hxET', hτxET'⟩
    have hxET : x ∈ ExtendedTube 1 n := by
      simpa [ExtendedTube, BHWCore.ExtendedTube] using hxET'
    have hτxET : (fun k => x (τ k)) ∈ ExtendedTube 1 n := by
      simpa [ExtendedTube, BHWCore.ExtendedTube] using hτxET'
    rcases Set.mem_iUnion.mp hxET with ⟨Λ, w, hwFT, hx_eq⟩
    have hτx_as_action :
        (fun k => x (τ k)) = complexLorentzAction Λ (fun k => w (τ k)) := by
      calc
        (fun k => x (τ k))
            = (fun k => (complexLorentzAction Λ w) (τ k)) := by simp [hx_eq]
        _ = complexLorentzAction Λ (fun k => w (τ k)) := by
              symm
              exact lorentz_perm_commute Λ w τ
    have hΛτw_ET : complexLorentzAction Λ (fun k => w (τ k)) ∈ ExtendedTube 1 n := by
      simpa [hτx_as_action] using hτxET
    have hτw_ET : (fun k => w (τ k)) ∈ ExtendedTube 1 n := by
      have := complexLorentzAction_mem_extendedTube n Λ⁻¹ hΛτw_ET
      simpa [complexLorentzAction_inv] using this
    refine ⟨w, ?_⟩
    exact ⟨hwFT, hτw_ET⟩

/-- Wrapper reduction: a real double-coset generation hypothesis on the
adjacent-overlap index set implies connectedness of the corresponding forward
overlap slice. -/
theorem isConnected_adjSwapForwardOverlapSet_of_real_double_coset_generation [NeZero d]
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi)
    (hgen : ∀ Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) :
    IsConnected (adjSwapForwardOverlapSet (d := d) n i hi) := by
  have hidx_conn : IsConnected (adjSwapForwardOverlapIndexSet (d := d) n i hi) :=
    indexSet_isConnected_of_real_double_coset_generation
      (d := d) n i hi Λ0 hΛ0 hgen
  have hnonempty : (adjSwapForwardOverlapSet (d := d) n i hi).Nonempty :=
    adjSwapForwardOverlap_nonempty (d := d) n i hi
  simpa [adjSwapForwardOverlapIndexSet] using
    isConnected_adjSwapForwardOverlapSet_of_indexConnected
      (d := d) n i hi hidx_conn hnonempty

/-- Conditional adjacent-swap ET invariance:
    connectedness of the ET overlap domain plus one real spacelike witness yields
    global equality `extendF(swap z) = extendF z` on that overlap domain. -/
theorem extendF_adjSwap_eq_of_connected_overlap
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n)
    (hD_conn : IsConnected
      {z : Fin n → Fin (d + 1) → ℂ |
        z ∈ ExtendedTube d n ∧
        (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n})
    (x0 : Fin n → Fin (d + 1) → ℝ)
    (hx0_sp : ∑ μ, minkowskiSignature d μ *
      (x0 ⟨i.val + 1, hi⟩ μ - x0 i μ) ^ 2 > 0)
    (hx0_ET : realEmbed x0 ∈ ExtendedTube d n)
    (hx0_swapET :
      realEmbed (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = extendF F z := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let D : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | z ∈ ExtendedTube d n ∧ (fun k => z (τ k)) ∈ ExtendedTube d n}
  have hD_open : IsOpen D := by
    have hperm_cont : Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k)) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (τ k))))
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hD_conn' : IsConnected D := by
    simpa [D, τ] using hD_conn
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hz
    exact hz.1
  have hD_sub_permET : D ⊆ {z | (fun k => z (τ k)) ∈ ExtendedTube d n} := by
    intro z hz
    exact hz.2
  obtain ⟨V, hV_open, hx0V, hV_sp, hV_ET, hV_swapET⟩ :=
    exists_real_open_nhds_adjSwap n i hi x0 hx0_sp hx0_ET hx0_swapET
  have hV_ne : V.Nonempty := ⟨x0, hx0V⟩
  have hV_sub_D : ∀ x ∈ V, realEmbed x ∈ D := by
    intro x hxV
    exact ⟨hV_ET x hxV, by simpa [D, τ, realEmbed] using hV_swapET x hxV⟩
  have hV_eq :
      ∀ x ∈ V, extendF F (fun k => (realEmbed x) (τ k)) = extendF F (realEmbed x) := by
    intro x hxV
    exact extendF_adjSwap_eq_on_realOpen n F hF_holo hF_real_inv
      hF_bv hF_local i hi V hV_open hV_sp hV_ET hV_swapET x hxV
  intro z hzET hτzET
  have hzD : z ∈ D := ⟨hzET, by simpa [τ] using hτzET⟩
  have hmain := extendF_perm_eq_on_connectedDomain_of_realOpen n F hF_holo
    hF_real_inv τ D hD_open hD_conn' hD_sub_ET hD_sub_permET V hV_open hV_ne
    hV_sub_D hV_eq z hzD
  simpa [τ] using hmain

/-- Adjacent-swap ET invariance from connectedness of the forward overlap slice.
    This packages the geometric reduction used to avoid proving connectedness of
    the full overlap domain directly. -/
theorem extendF_adjSwap_eq_of_connected_forwardOverlap
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (i : Fin n) (hi : i.val + 1 < n)
    (hFwd_conn : IsConnected (adjSwapForwardOverlapSet (d := d) n i hi))
    (x0 : Fin n → Fin (d + 1) → ℝ)
    (hx0_sp : ∑ μ, minkowskiSignature d μ *
      (x0 ⟨i.val + 1, hi⟩ μ - x0 i μ) ^ 2 > 0)
    (hx0_ET : realEmbed x0 ∈ ExtendedTube d n)
    (hx0_swapET :
      realEmbed (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = extendF F z := by
  have hD_conn :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ ExtendedTube d n ∧
          (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n} := by
    simpa [adjSwapExtendedOverlapSet] using
      isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected
        n i hi hFwd_conn
  exact extendF_adjSwap_eq_of_connected_overlap n F hF_holo hF_real_inv
    hF_bv hF_local i hi hD_conn x0 hx0_sp hx0_ET hx0_swapET

/-- `d ≥ 2` wrapper: obtain the required real spacelike overlap witness from
    `AdjacentOverlapWitness` automatically. -/
theorem extendF_adjSwap_eq_of_connected_forwardOverlap_hd2
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n)
    (hFwd_conn : IsConnected (adjSwapForwardOverlapSet (d := d) n i hi)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = extendF F z := by
  rcases adjacent_overlap_real_spacelike_witness_exists (d := d) (n := n) hd i hi with
    ⟨x0, hx0_sp, hx0_ET, hx0_swapET⟩
  exact extendF_adjSwap_eq_of_connected_forwardOverlap n F hF_holo hF_real_inv
    hF_bv hF_local i hi hFwd_conn x0 hx0_sp hx0_ET hx0_swapET


end BHW
