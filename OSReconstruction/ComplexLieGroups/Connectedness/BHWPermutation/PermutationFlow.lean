import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-- Permutation action on particle indices. -/
private def permAct (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k => z (σ k)

/-- One adjacent-swap step in permutation space that preserves ET-membership
for the fixed configuration `z`. -/
private def etAdjStep (z : Fin n → Fin (d + 1) → ℂ)
    (π₁ π₂ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (i : Fin n) (hi : i.val + 1 < n),
    π₂ = π₁ * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      permAct (d := d) π₁ z ∈ ExtendedTube d n ∧
      permAct (d := d) π₂ z ∈ ExtendedTube d n

/-- ET-preserving adjacent-chain existence from a one-step backward closure
condition in permutation space. -/
private theorem etAdj_chain_of_midCond
    (y : Fin n → Fin (d + 1) → ℂ)
    (hmidCond :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        permAct (d := d) σ y ∈ ExtendedTube d n)
    (τ : Equiv.Perm (Fin n))
    (_hy : y ∈ ExtendedTube d n)
    (hτy : permAct (d := d) τ y ∈ ExtendedTube d n) :
    Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ := by
  revert hτy
  refine Fin.Perm.adjSwap_induction_right (n := n)
    (motive := fun τ =>
      permAct (d := d) τ y ∈ ExtendedTube d n →
      Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ)
    ?base ?step τ
  · intro h1
    simpa [permAct] using Relation.ReflTransGen.refl
  · intro σ i hi ih hσswap
    have hσ : permAct (d := d) σ y ∈ ExtendedTube d n :=
      hmidCond σ i hi hσswap
    have hchainσ :
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 σ := ih hσ
    have htail :
        etAdjStep (d := d) (n := n) y σ (σ * Equiv.swap i ⟨i.val + 1, hi⟩) :=
      ⟨i, hi, rfl, hσ, hσswap⟩
    exact Relation.ReflTransGen.tail hchainσ htail

/-- Chain reduction for ET permutation invariance of `extendF`.
If adjacent-swap ET invariance is known and `σ` is linked to `1` by an
ET-preserving adjacent chain at `z`, then `extendF` is `σ`-invariant at `z`. -/
private theorem extendF_perm_of_etAdj_chain
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ ExtendedTube d n →
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y) = extendF F y)
    (z : Fin n → Fin (d + 1) → ℂ)
    (σ : Equiv.Perm (Fin n))
    (hchain : Relation.ReflTransGen (etAdjStep (d := d) (n := n) z) 1 σ) :
    extendF F (permAct (d := d) σ z) = extendF F z := by
  refine Relation.ReflTransGen.rec
    (motive := fun π _ => extendF F (permAct (d := d) π z) = extendF F z)
    ?_ ?_ hchain
  · change extendF F (fun k => z ((1 : Equiv.Perm (Fin n)) k)) = extendF F z
    simp
  · intro b c hbc hstep ih
    rcases hstep with ⟨i, hi, hmul, hbET, hcET⟩
    subst hmul
    have hperm_comp :
        permAct (d := d) (b * Equiv.swap i ⟨i.val + 1, hi⟩) z =
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) (permAct (d := d) b z) := by
      ext k μ
      simp [permAct, Equiv.Perm.mul_apply]
    have hcET' :
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) (permAct (d := d) b z)
          ∈ ExtendedTube d n := by
      simpa [hperm_comp] using hcET
    have hadj' :
        extendF F
            (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
              (permAct (d := d) b z)) =
          extendF F (permAct (d := d) b z) :=
      hAdj i hi (permAct (d := d) b z) hbET hcET'
    have hadj :
        extendF F (permAct (d := d) (b * Equiv.swap i ⟨i.val + 1, hi⟩) z) =
          extendF F (permAct (d := d) b z) := by
      simpa [hperm_comp] using hadj'
    exact hadj.trans ih

/-- Globalized chain reduction:
adjacent ET invariance plus ET-preserving adjacent-chain existence implies
full ET-overlap permutation invariance of `extendF`. -/
private theorem extendF_perm_of_etAdj_chain_exists
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ ExtendedTube d n →
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y) = extendF F y)
    (hChain :
      ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) z) 1 σ) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  intro σ z hz hσz
  exact extendF_perm_of_etAdj_chain (d := d) (n := n) F hAdj z σ
    (hChain σ z hz hσz)

/-- Adjacent-swap ET invariance for all adjacent indices, assuming connectedness
    of all corresponding forward-overlap slices (`d ≥ 2`). -/
private theorem extendF_adjSwap_all_of_connected_forwardOverlap_hd2
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
    (hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi)) :
    ∀ (i : Fin n) (hi : i.val + 1 < n) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = extendF F z := by
  intro i hi z hz hswap
  exact extendF_adjSwap_eq_of_connected_forwardOverlap_hd2 n F hF_holo hF_real_inv
    hF_bv hF_local hd i hi (hFwd_conn i hi) z hz hswap

/-- `d ≥ 2` packaged reduction:
adjacent-swap ET invariance plus ET-preserving adjacent-chain existence imply
full ET-overlap permutation invariance of `extendF`. -/
private theorem extendF_perm_overlap_of_adjSwap_connected_and_chain_hd2
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
    (hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi))
    (hChain :
      ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) z) 1 σ) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  apply extendF_perm_of_etAdj_chain_exists (d := d) (n := n) F
  · exact extendF_adjSwap_all_of_connected_forwardOverlap_hd2
      n F hF_holo hF_real_inv hF_bv hF_local hd hFwd_conn
  · exact hChain

/-- Alternative packaged reduction:
if one can prove the one-step ET backward-closure condition
`permAct (σ * swap) y ∈ ET → permAct σ y ∈ ET`, then chain existence follows
via `etAdj_chain_of_midCond`. -/
private theorem extendF_perm_overlap_of_adjSwap_connected_and_midCond_hd2
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
    (hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi))
    (hmidCond :
      ∀ (y : Fin n → Fin (d + 1) → ℂ)
        (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        permAct (d := d) σ y ∈ ExtendedTube d n) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hChain :
      ∀ (τ : Equiv.Perm (Fin n)) (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ ExtendedTube d n →
        permAct (d := d) τ y ∈ ExtendedTube d n →
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ := by
    intro τ y hy hτy
    have hmidCond_y :
        ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
          permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
          permAct (d := d) σ y ∈ ExtendedTube d n := by
      intro σ i hi h
      exact hmidCond y σ i hi h
    exact etAdj_chain_of_midCond (d := d) (n := n) y hmidCond_y τ hy hτy
  exact extendF_perm_overlap_of_adjSwap_connected_and_chain_hd2
    (d := d) (n := n) F hF_holo hF_real_inv hF_bv hF_local hd hFwd_conn hChain

/-- Packaged `d ≥ 2` reduction via index-set generation:
if each adjacent-overlap forward slice is connected by a real double-coset
generation hypothesis and one has the ET one-step backward closure condition,
then full ET-overlap permutation invariance of `extendF` follows. -/
private theorem extendF_perm_overlap_of_real_double_coset_generation_and_midCond_hd2
    [NeZero d]
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
    (hgen :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ (Λ0 : ComplexLorentzGroup d),
          Λ0 ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi ∧
          (∀ Λ ∈ adjSwapForwardOverlapIndexSet (d := d) n i hi,
            ∃ R1 R2 : RestrictedLorentzGroup d,
              Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2))
    (hmidCond :
      ∀ (y : Fin n → Fin (d + 1) → ℂ)
        (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        permAct (d := d) σ y ∈ ExtendedTube d n) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi) := by
    intro i hi
    rcases hgen i hi with ⟨Λ0, hΛ0, hgen_i⟩
    exact isConnected_adjSwapForwardOverlapSet_of_real_double_coset_generation
      (d := d) n i hi Λ0 hΛ0 hgen_i
  exact extendF_perm_overlap_of_adjSwap_connected_and_midCond_hd2
    (d := d) (n := n) F hF_holo hF_real_inv hF_bv hF_local hd hFwd_conn hmidCond

/-- Build a holomorphic extension domain for a fixed permutation `σ` from
    the corresponding permutation-invariance hypothesis.

    If `hperm` says
      `F (Γ·(σ·w)) = F(w)` whenever `w ∈ FT` and `Γ·(σ·w) ∈ FT`,
    then on `U_σ := FT ∪ {z | σ·z ∈ FT}` the piecewise function
      `F_σ z := if z ∈ FT then F z else F (σ·z)`
    is holomorphic, agrees with `F` on `FT`, agrees with `F∘σ` on `σFT`,
    and is complex-Lorentz invariant on `U_σ`.

    This packages the exact extension data needed in EOW chain arguments. -/
private theorem permutation_extension_from_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hperm : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (σ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (σ k))) = F w) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  set σFT : Set (Fin n → Fin (d + 1) → ℂ) := {z | (fun k => z (σ k)) ∈ ForwardTube d n}
  set U_σ : Set (Fin n → Fin (d + 1) → ℂ) := ForwardTube d n ∪ σFT
  set F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => if z ∈ ForwardTube d n then F z else F (fun k => z (σ k))
  have hFσ_eq_on_σFT :
      ∀ z, z ∈ σFT → F_σ z = F (fun k => z (σ k)) := by
    intro z hzσ
    by_cases hzFT : z ∈ ForwardTube d n
    · have h1 : F (fun k => z (σ k)) = F z := by
        simpa [complexLorentzAction_one] using
          (hperm z hzFT 1 (by
            simpa [σFT, complexLorentzAction_one] using hzσ))
      simp [F_σ, hzFT, h1]
    · simp [F_σ, hzFT]
  refine ⟨U_σ, F_σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_forwardTube.union (isOpen_permutedForwardTube σ)
  · intro z hz
    exact Or.inl hz
  · intro z hz
    exact Or.inr hz
  · intro z hzU
    rcases hzU with hzFT | hzσ
    · have hFz : DifferentiableAt ℂ F z :=
        (hF_holo z hzFT).differentiableAt (isOpen_forwardTube.mem_nhds hzFT)
      have h_eq : F_σ =ᶠ[𝓝 z] F := by
        filter_upwards [isOpen_forwardTube.mem_nhds hzFT] with w hw
        simp [F_σ, hw]
      exact (h_eq.differentiableAt_iff.mpr hFz).differentiableWithinAt
    · have hFσz : DifferentiableAt ℂ F (fun k => z (σ k)) :=
        (hF_holo _ (by simpa [σFT] using hzσ)).differentiableAt
          (isOpen_forwardTube.mem_nhds (by simpa [σFT] using hzσ))
      have hperm_diff : Differentiable ℂ
          (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (σ k)) :=
        differentiable_pi.mpr (fun k => differentiable_apply (σ k))
      have hcomp : DifferentiableAt ℂ (fun w => F (fun k => w (σ k))) z :=
        DifferentiableAt.comp z hFσz (hperm_diff z)
      have h_eq : F_σ =ᶠ[𝓝 z] (fun w => F (fun k => w (σ k))) := by
        filter_upwards [(isOpen_permutedForwardTube σ).mem_nhds hzσ] with w hw
        exact hFσ_eq_on_σFT w hw
      exact (h_eq.differentiableAt_iff.mpr hcomp).differentiableWithinAt
  · intro z hz
    exact if_pos hz.2
  · intro Λ z hzU hΛzU
    rcases hzU with hzFT | hzσ
    · rcases hΛzU with hΛzFT | hΛzσ
      · simp [F_σ, hzFT, hΛzFT]
        exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hzFT hΛzFT
      · have hstep :
            F (complexLorentzAction Λ (fun k => z (σ k))) = F z :=
          hperm z hzFT Λ (by
            simpa [σFT, lorentz_perm_commute] using hΛzσ)
        have hlhs : F_σ (complexLorentzAction Λ z) =
            F (complexLorentzAction Λ (fun k => z (σ k))) := by
          exact (hFσ_eq_on_σFT (complexLorentzAction Λ z) hΛzσ).trans (by
            simp [lorentz_perm_commute])
        simp [F_σ, hzFT]
        exact hlhs.trans hstep
    · rcases hΛzU with hΛzFT | hΛzσ
      · have hzσFT : (fun k => z (σ k)) ∈ ForwardTube d n := by
          simpa [σFT] using hzσ
        have hrewrite : complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (σ k)) =
            (fun k => z (σ k)) := by
          calc
            complexLorentzAction Λ⁻¹
              (fun k => (complexLorentzAction Λ z) (σ k))
                = complexLorentzAction Λ⁻¹
                    (complexLorentzAction Λ (fun k => z (σ k))) := by
                      simp [lorentz_perm_commute]
            _ = (fun k => z (σ k)) := by
                  rw [complexLorentzAction_inv]
        have hcond :
            complexLorentzAction Λ⁻¹
              (fun k => (complexLorentzAction Λ z) (σ k)) ∈ ForwardTube d n := by
          simpa [hrewrite] using hzσFT
        have hstep :
            F (complexLorentzAction Λ⁻¹
              (fun k => (complexLorentzAction Λ z) (σ k))) =
            F (complexLorentzAction Λ z) :=
          hperm (complexLorentzAction Λ z) hΛzFT Λ⁻¹ hcond
        have hright : F_σ z = F (fun k => z (σ k)) := hFσ_eq_on_σFT z hzσ
        have hleft : F_σ (complexLorentzAction Λ z) = F (complexLorentzAction Λ z) := by
          simp [F_σ, hΛzFT]
        have hstep' : F (fun k => z (σ k)) = F (complexLorentzAction Λ z) := by
          simpa [hrewrite] using hstep
        exact hleft.trans (hstep'.symm.trans hright.symm)
      · have hzσFT : (fun k => z (σ k)) ∈ ForwardTube d n := by
          simpa [σFT] using hzσ
        have hΛzσFT : (fun k => (complexLorentzAction Λ z) (σ k)) ∈ ForwardTube d n := by
          simpa [σFT] using hΛzσ
        have hstep : F (complexLorentzAction Λ (fun k => z (σ k))) =
            F (fun k => z (σ k)) :=
          complex_lorentz_invariance n F hF_holo hF_lorentz Λ
            (fun k => z (σ k)) hzσFT (by
              simpa [lorentz_perm_commute] using hΛzσFT)
        have hleft : F_σ (complexLorentzAction Λ z) =
            F (complexLorentzAction Λ (fun k => z (σ k))) := by
          exact (hFσ_eq_on_σFT (complexLorentzAction Λ z) hΛzσ).trans (by
            simp [lorentz_perm_commute])
        have hright : F_σ z = F (fun k => z (σ k)) := hFσ_eq_on_σFT z hzσ
        exact hleft.trans (hstep.trans hright.symm)
  · intro z hz
    exact hFσ_eq_on_σFT z hz.2

/-- If `extendF` is permutation-invariant on the extended-tube overlap for `τ`,
    then `F` satisfies the corresponding forward-tube permutation invariance. -/
private theorem permutation_invariance_from_extendF_on_extendedTube (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n))
    (hExtPerm :
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (τ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (τ k)) = extendF F z) :
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  intro w hw Γ hΓτw
  set z : Fin n → Fin (d + 1) → ℂ := complexLorentzAction Γ w
  have hcomm : complexLorentzAction Γ (fun k => w (τ k)) = fun k => z (τ k) := by
    simpa [z] using (lorentz_perm_commute Γ w τ)
  have hτz_FT : (fun k => z (τ k)) ∈ ForwardTube d n := by
    simpa [hcomm] using hΓτw
  have hz_ET : z ∈ ExtendedTube d n := by
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Γ, ?_⟩
    exact ⟨w, hw, by simp [z]⟩
  have hτz_ET : (fun k => z (τ k)) ∈ ExtendedTube d n :=
    forwardTube_subset_extendedTube hτz_FT
  have hperm_ext : extendF F (fun k => z (τ k)) = extendF F z :=
    hExtPerm z hz_ET hτz_ET
  have hLorentz_ext : extendF F z = extendF F w := by
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
    _ = extendF F z := hperm_ext
    _ = extendF F w := hLorentz_ext
    _ = F w := hright

/-- If `z = Λ·w` with `w ∈ FT`, then `extendF F z = F w`.
    This packages the witness-based unfolding used in overlap arguments. -/
private theorem extendF_eq_of_explicit_witness (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n)
    (Λ : ComplexLorentzGroup d)
    (hz : z = complexLorentzAction Λ w) :
    extendF F z = F w := by
  simp only [extendF]
  have hex : ∃ (w' : Fin n → Fin (d + 1) → ℂ),
      w' ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d), z = complexLorentzAction Λ' w' :=
    ⟨w, hw, Λ, hz⟩
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  have hwc : hex.choose ∈ ForwardTube d n := hspec.1
  rcases hspec.2 with ⟨Λc, hzc⟩
  have h_eq : complexLorentzAction Λc hex.choose = complexLorentzAction Λ w := by
    exact hzc.symm.trans hz
  exact extendF_preimage_eq n F hF_holo hF_real_inv hwc hw h_eq

/-- Forward-tube permutation invariance implies permutation invariance of `extendF`
    on the extended-tube overlap for the same permutation. -/
private theorem extendF_perm_overlap_from_forwardTube_permInvariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n))
    (hperm : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (τ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (τ k)) = extendF F z := by
  intro z hz hzτ
  rcases Set.mem_iUnion.mp hz with ⟨Γ, w, hw, rfl⟩
  have hcomm : complexLorentzAction Γ (fun k => w (τ k)) =
      (fun k => (complexLorentzAction Γ w) (τ k)) := by
    ext k μ
    simp [complexLorentzAction]
  rcases Set.mem_iUnion.mp hzτ with ⟨Δ, u, hu, hu_eq⟩
  have hu_eq' : complexLorentzAction Γ (fun k => w (τ k)) =
      complexLorentzAction Δ u := by
    simpa [hcomm] using hu_eq
  have hcond : complexLorentzAction (Δ⁻¹ * Γ) (fun k => w (τ k)) ∈ ForwardTube d n := by
    rw [complexLorentzAction_mul, hu_eq', complexLorentzAction_inv]
    exact hu
  have hperm_w : F (complexLorentzAction (Δ⁻¹ * Γ) (fun k => w (τ k))) = F w :=
    hperm w hw (Δ⁻¹ * Γ) hcond
  have hu_eq_w : F u = F w := by
    have : complexLorentzAction (Δ⁻¹ * Γ) (fun k => w (τ k)) = u := by
      rw [complexLorentzAction_mul, hu_eq', complexLorentzAction_inv]
    simpa [this] using hperm_w
  have hleft : extendF F (fun k => (complexLorentzAction Γ w) (τ k)) = F u := by
    exact extendF_eq_of_explicit_witness n F hF_holo hF_real_inv
      _ u hu Δ hu_eq
  have hright : extendF F (complexLorentzAction Γ w) = F w := by
    exact extendF_eq_of_explicit_witness n F hF_holo hF_real_inv
      _ w hw Γ rfl
  calc
    extendF F (fun k => (complexLorentzAction Γ w) (τ k)) = F u := hleft
    _ = F w := hu_eq_w
    _ = extendF F (complexLorentzAction Γ w) := hright.symm

/-- `extendF` overlap-invariance and forward-tube permutation-invariance are equivalent
    formulations for a fixed permutation `τ`. -/
private theorem permInvariance_forwardTube_iff_extendF_overlap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n)) :
    (∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (τ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (τ k)) = extendF F z) ↔
    (∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w) := by
  constructor
  · intro hExtPerm
    exact permutation_invariance_from_extendF_on_extendedTube n F hF_holo hF_real_inv τ hExtPerm
  · intro hperm
    exact extendF_perm_overlap_from_forwardTube_permInvariance n F hF_holo hF_real_inv τ hperm

/-- Reduced form of `iterated_eow_permutation_extension`: it is enough to prove
    permutation invariance of `extendF` on the extended-tube overlap for each `σ`. -/
private theorem iterated_eow_permutation_extension_of_extendF_perm (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (_hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (_hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hExtPerm :
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (σ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (σ k)) = extendF F z) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  have hperm :
      ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
        ∀ (Γ : ComplexLorentzGroup d),
          complexLorentzAction Γ (fun k => w (σ k)) ∈ ForwardTube d n →
          F (complexLorentzAction Γ (fun k => w (σ k))) = F w := by
    exact permutation_invariance_from_extendF_on_extendedTube n F hF_holo hF_lorentz σ hExtPerm
  exact permutation_extension_from_invariance n F hF_holo hF_lorentz σ hperm

/-- **Iterated EOW extension for permutations.**
    For any permutation σ of Fin n (decomposed as a product of adjacent swaps),
    the iterated application of eow_adj_swap_extension produces a holomorphic
    function F_σ on an open domain U_σ ⊇ FT ∪ σ·FT such that:
    1. F_σ agrees with F on U_σ ∩ FT
    2. F_σ is complex Lorentz-invariant on U_σ
    3. F_σ(σ·w) = F_σ(w) for w ∈ FT with σ·w ∈ U_σ

    The construction proceeds by induction on the adjacent swap decomposition:
    - Base: F₁ = F, U₁ = FT (for the identity permutation)
    - Step: given F_σ on U_σ, apply eow_adj_swap_extension to F_σ with the
      next swap, obtaining F_{swap·σ} on U_{swap·σ} ⊇ U_σ ∪ swap·U_σ.
      The identity theorem ensures consistency.

    Infrastructure gap: this requires eow_adj_swap_extension to work on
    general holomorphic domains (not just FT), which needs a generalization
    of the EOW theorem to tube-like subsets of the extended domain. -/
private theorem iterated_eow_permutation_extension (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
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
    (σ : Equiv.Perm (Fin n)) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  by_cases hσ : σ = 1
  · subst hσ
    refine ⟨ForwardTube d n, F, isOpen_forwardTube, ?_, ?_, hF_holo, ?_, ?_, ?_⟩
    · intro z hz
      exact hz
    · intro z hz
      simpa using hz
    · intro z hz
      exact rfl
    · intro Λ z hzU hΛzU
      exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hzU hΛzU
    · intro z hz
      simp
  · by_cases hn : n ≤ 1
    · have hsub : Subsingleton (Fin n) := by
        refine ⟨?_⟩
        intro a b
        apply Fin.ext
        have ha0 : a.val = 0 := by omega
        have hb0 : b.val = 0 := by omega
        omega
      haveI : Subsingleton (Fin n) := hsub
      exfalso
      exact hσ (Subsingleton.elim σ 1)
    · -- Remaining blocker: nontrivial permutation iteration (`n ≥ 2` and σ ≠ 1)
      -- reduced to proving `extendF` permutation-invariance on the ET overlap.
      have hExtPerm :
          ∀ (z : Fin n → Fin (d + 1) → ℂ),
            z ∈ ExtendedTube d n →
            (fun k => z (σ k)) ∈ ExtendedTube d n →
            extendF F (fun k => z (σ k)) = extendF F z := by
        by_cases hd0 : d = 0
        · subst hd0
          intro z hz hσz
          have hσ1 : σ = 1 :=
            coreExtendedTube_perm_overlap_d0_forces_perm_one_general n σ
              (by simpa [ExtendedTube, BHWCore.ExtendedTube] using hz)
              (by simpa [ExtendedTube, BHWCore.ExtendedTube] using hσz)
          exact (hσ hσ1).elim
        · -- Equivalently (by `permInvariance_forwardTube_iff_extendF_overlap`):
          -- prove the forward-tube permutation invariance statement for `σ`.
          -- This is the exact remaining gap in the nontrivial permutation step.
          sorry
      exact iterated_eow_permutation_extension_of_extendF_perm n F hF_holo hF_lorentz
        hF_bv hF_local σ hExtPerm

/-- Any extension data of the shape produced by
    `iterated_eow_permutation_extension` yields the corresponding
    permutation-invariance statement. -/
private theorem permInvariance_of_extensionData (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (τ : Equiv.Perm (Fin n))
    (U_τ : Set (Fin n → Fin (d + 1) → ℂ))
    (F_τ : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hFT_sub : ForwardTube d n ⊆ U_τ)
    (hτFT_sub : {z | (fun k => z (τ k)) ∈ ForwardTube d n} ⊆ U_τ)
    (hF_τ_eq_F : ∀ z ∈ U_τ ∩ ForwardTube d n, F_τ z = F z)
    (hF_τ_inv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ U_τ → complexLorentzAction Λ z ∈ U_τ →
      F_τ (complexLorentzAction Λ z) = F_τ z)
    (hF_τ_eq_Fτ : ∀ z ∈ U_τ ∩ {z | (fun k => z (τ k)) ∈ ForwardTube d n},
      F_τ z = F (fun k => z (τ k)))
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  have comm : complexLorentzAction Γ (fun k => w (τ k)) =
      fun k => (complexLorentzAction Γ w) (τ k) :=
    lorentz_perm_commute Γ w τ
  rw [comm] at h ⊢
  have hΓw_τFT : complexLorentzAction Γ w ∈ {z | (fun k => z (τ k)) ∈ ForwardTube d n} := h
  have hw_U : w ∈ U_τ := hFT_sub hw
  have hΓw_U : complexLorentzAction Γ w ∈ U_τ := hτFT_sub hΓw_τFT
  have h_inv : F_τ (complexLorentzAction Γ w) = F_τ w :=
    hF_τ_inv Γ w hw_U hΓw_U
  have h1 : F_τ w = F w := hF_τ_eq_F w ⟨hw_U, hw⟩
  have h2 : F_τ (complexLorentzAction Γ w) =
      F (fun k => (complexLorentzAction Γ w) (τ k)) :=
    hF_τ_eq_Fτ (complexLorentzAction Γ w) ⟨hΓw_U, hΓw_τFT⟩
  exact h2.symm.trans (h_inv.trans h1)

/-- If `extendF` is permutation-invariant on the extended-tube overlap for `τ`,
    then the corresponding forward-tube permutation-invariance statement follows
    via extension data packaging. -/
private theorem permInvariance_of_extendF_overlap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
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
    (τ : Equiv.Perm (Fin n))
    (hExtPerm :
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (τ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (τ k)) = extendF F z) :
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  obtain ⟨U_τ, F_τ, hU_open, hFT_sub, hτFT_sub, hF_τ_holo,
    hF_τ_eq_F, hF_τ_inv, hF_τ_eq_Fτ⟩ :=
    iterated_eow_permutation_extension_of_extendF_perm n F hF_holo hF_lorentz
      hF_bv hF_local τ hExtPerm
  intro w hw Γ h
  exact permInvariance_of_extensionData n F τ U_τ F_τ hFT_sub hτFT_sub
    hF_τ_eq_F hF_τ_inv hF_τ_eq_Fτ hw h

/-- **Inductive step for permutation invariance: one more adjacent swap.**
    Given that F is invariant under σ (i.e., for all w in FT and Gamma with
    Gamma(sigma w) in FT, F(Gamma(sigma w)) = F(w)), prove the same for swap(i,i+1) * sigma.

    The proof uses iterated_eow_permutation_extension to obtain a holomorphic
    Lorentz-invariant extension F_σ on U_σ ⊇ FT ∪ σ·FT. Then:
    1. Rewrite (swap * σ)·w as swap·(σ·w)
    2. By Lorentz-perm commutation: Γ·(swap·(σ·w)) = swap·(Γ·(σ·w))
    3. Since swap·(Γ·(σ·w)) ∈ FT, Γ·(σ·w) ∈ swap·FT ⊆ U_{swap·σ}
    4. The Lorentz-invariant extension F_{swap·σ} bridges the gap -/
private theorem eow_chain_adj_swap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
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
    (σ₀ : Equiv.Perm (Fin n)) (i₀ : Fin n) (hi₀ : i₀.val + 1 < n)
    (_ih_σ : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (σ₀ k))) = F w)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ
      (fun k => w ((Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩ * σ₀) k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ
      (fun k => w ((Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩ * σ₀) k))) = F w := by
  -- Set τ = swap * σ₀
  set τ := Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩ * σ₀
  -- Obtain the iterated EOW extension for τ
  obtain ⟨U_τ, F_τ, hU_open, hFT_sub, hτFT_sub, hF_τ_holo,
    hF_τ_eq_F, hF_τ_inv, hF_τ_eq_Fτ⟩ :=
    iterated_eow_permutation_extension n F hF_holo hF_lorentz hF_bv hF_local τ
  exact permInvariance_of_extensionData n F τ U_τ F_τ hFT_sub hτFT_sub
    hF_τ_eq_F hF_τ_inv hF_τ_eq_Fτ hw h

private theorem F_permutation_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
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
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  -- Induction on τ via adjacent transposition decomposition.
  -- The motive universally quantifies over w and Γ.
  revert w Γ
  apply Fin.Perm.adjSwap_induction (motive := fun τ =>
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
    ∀ (Γ : ComplexLorentzGroup d),
      complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
      F (complexLorentzAction Γ (fun k => w (τ k))) = F w)
  -- Base case: τ = 1. Goal reduces to F(Γ·w) = F(w), which is complex_lorentz_invariance.
  · intro w₀ hw₀ Γ₀ h₀
    simp only [Equiv.Perm.one_apply] at h₀ ⊢
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Γ₀ w₀ hw₀ h₀
  -- Inductive step: τ = swap(i, i+1) * σ.
  -- Given: motive holds for σ (for all w, Γ).
  -- Goal: motive holds for swap * σ (for all w, Γ).
  -- We have w ∈ FT and Γ·((swap * σ)·w) ∈ FT.
  -- (swap * σ)·w(k) = w(σ(swap(k))), so Γ·(fun k => w(σ(swap(k)))) ∈ FT.
  --
  -- The crux: σ·w := (fun k => w(σ(k))) may NOT lie in FT, so we cannot
  -- directly apply a single-swap overlap invariance argument to σ·w.
  -- The correct argument requires the EOW-iterated holomorphic extension:
  -- at each step in the transposition decomposition, the EOW theorem extends
  -- F to a larger domain. The induction hypothesis gives this extension
  -- implicitly via the universally quantified Γ.
  --
  -- Specifically: by Lorentz-perm commutation,
  -- Γ·((swap*σ)·w) = Γ·(swap·(σ·w)) = swap·(Γ·(σ·w))  (*)
  -- If Γ·(σ·w) ∈ FT, a local swap step plus ih_σ would suffice.
  -- If Γ·(σ·w) ∉ FT, the domain extension argument is needed.
  -- This is the fundamental blocker for the induction approach.
  · intro σ₀ i₀ hi₀ ih_σ w₀ hw₀ Γ₀ h₀
    -- Blocked: the intermediate point Γ₀·(σ₀·w₀) may not lie in FT.
    -- The resolution requires extending F holomorphically across permuted
    -- tubes via iterated EOW, which is a substantial infrastructure gap.
    -- Bootstrap with a helper capturing this gap.
    exact eow_chain_adj_swap n F hF_holo hF_lorentz hF_bv hF_local
      σ₀ i₀ hi₀ ih_σ hw₀ h₀

/-- Well-definedness: any two preimages of the same point give the same F-value.
    Reduces to `F_permutation_invariance` via the Lorentz-permutation commutation
    identity `Λ·(π·w) = π·(Λ·w)`.

    From Λ₁·(π₁·w₁) = Λ₂·(π₂·w₂), applying Λ₁⁻¹ and using the commutation:
    w₁ = (Λ₁⁻¹Λ₂)·((π₂π₁⁻¹)·w₂), then `F_permutation_invariance` gives
    F(w₁) = F(w₂). -/
private theorem fullExtendF_well_defined (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
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
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {π₁ π₂ : Equiv.Perm (Fin n)} {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ (fun k => w₁ (π₁ k)) =
         complexLorentzAction Λ₂ (fun k => w₂ (π₂ k))) :
    F w₁ = F w₂ := by
  -- Step 1: Derive w₁ = Γ·(τ·w₂) where Γ = Λ₁⁻¹Λ₂, τ = π₂π₁⁻¹.
  -- Key fact: Lorentz action commutes with particle-index permutation:
  --   complexLorentzAction Λ (fun k => z (σ k)) = fun k => (complexLorentzAction Λ z) (σ k)
  -- (holds definitionally since Λ acts only on the μ-index)
  have step1 := congr_arg (complexLorentzAction Λ₁⁻¹) h
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one,
      ← complexLorentzAction_mul] at step1
  -- step1 : (fun k => w₁ (π₁ k)) = complexLorentzAction (Λ₁⁻¹ * Λ₂) (fun k => w₂ (π₂ k))
  -- Extract pointwise: w₁(m) = (Γ·(π₂·w₂))(π₁⁻¹ m) = (Γ·(τ·w₂))(m)
  have hw₁_eq : w₁ = complexLorentzAction (Λ₁⁻¹ * Λ₂) (fun k => w₂ ((π₂ * π₁⁻¹) k)) := by
    ext m μ
    have := congr_fun (congr_fun step1 (π₁⁻¹ m)) μ
    rw [show π₁ (π₁⁻¹ m) = m from Equiv.apply_symm_apply π₁ m] at this
    rw [this]
    simp only [complexLorentzAction, Equiv.Perm.mul_apply]
  -- Step 2: Apply F_permutation_invariance
  rw [hw₁_eq]
  exact F_permutation_invariance n F hF_holo hF_lorentz hF_bv hF_local hw₂ (hw₁_eq ▸ hw₁)

theorem bargmann_hall_wightman_theorem [NeZero d] (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    -- F extends continuously to the real boundary of the forward tube.
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    -- Local commutativity: at spacelike-separated pairs, the boundary values
    -- of F and F∘swap agree.
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- F_ext is holomorphic on the permuted extended tube
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      -- F_ext restricts to F on the forward tube
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      -- F_ext is invariant under the complex Lorentz group
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (complexLorentzAction Λ z) = F_ext z) ∧
      -- F_ext is symmetric under permutations
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) ∧
      -- Uniqueness: any holomorphic function on PermutedExtendedTube agreeing with F
      -- on ForwardTube must equal F_ext.
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z) := by
  -- === Construct F_ext ===
  -- Pre-prove Properties 1 and 2 so they can be referenced in Property 5.
  have hProp1 : DifferentiableOn ℂ (fullExtendF F) (PermutedExtendedTube d n) := by
    intro z₀ hz₀
    obtain ⟨π₀, Λ₀, w₀, hw₀, hz₀_eq⟩ := Set.mem_iUnion.mp hz₀
    have hw_ft : (fun k => w₀ (π₀ k)) ∈ ForwardTube d n := hw₀
    set ψ := fun z : Fin n → Fin (d + 1) → ℂ =>
      fun k => (complexLorentzAction (Λ₀⁻¹ : ComplexLorentzGroup d) z) (π₀ k) with hψ_def
    have hψ_diff : Differentiable ℂ ψ := by
      apply differentiable_pi.mpr; intro k
      exact (differentiable_apply (π₀ k)).comp (differentiable_complexLorentzAction_snd Λ₀⁻¹)
    have hψz₀ : ψ z₀ = fun k => w₀ (π₀ k) := by
      simp only [ψ, hz₀_eq]
      rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]
    have hV_open : IsOpen {z | ψ z ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage hψ_diff.continuous
    have hz₀_V : ψ z₀ ∈ ForwardTube d n := hψz₀ ▸ hw_ft
    have hfeq : fullExtendF F =ᶠ[nhds z₀] fun z => F (ψ z) := by
      apply Filter.eventuallyEq_of_mem (hV_open.mem_nhds hz₀_V)
      intro z (hz_V : ψ z ∈ ForwardTube d n)
      have hz_chart : z = complexLorentzAction Λ₀ (fun k => (ψ z) (π₀⁻¹ k)) := by
        have h1 : (fun k => (ψ z) (π₀⁻¹ k)) = complexLorentzAction Λ₀⁻¹ z := by
          ext k μ; simp only [ψ]
          rw [show π₀ (π₀⁻¹ k) = k from Equiv.apply_symm_apply π₀ k]
        rw [h1, ← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one]
      simp only [fullExtendF]
      have hex : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
          (w : Fin n → Fin (d + 1) → ℂ),
          w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k)) :=
        ⟨π₀⁻¹, Λ₀, ψ z, hz_V, hz_chart⟩
      rw [dif_pos hex]
      exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
        hex.choose_spec.choose_spec.choose_spec.1 hz_V
        (hex.choose_spec.choose_spec.choose_spec.2.symm.trans hz_chart)
    have hFψ_diff : DifferentiableAt ℂ (fun z => F (ψ z)) z₀ :=
      ((hF_holo _ hz₀_V).differentiableAt (isOpen_forwardTube.mem_nhds hz₀_V)).comp
        z₀ (hψ_diff z₀)
    exact (hfeq.differentiableAt_iff.mpr hFψ_diff).differentiableWithinAt
  have hProp2 : ∀ z ∈ ForwardTube d n, fullExtendF F z = F z := by
    intro z hz
    simp only [fullExtendF]
    have hex : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k)) :=
      ⟨Equiv.refl _, 1, z, hz, by simp [complexLorentzAction_one, Equiv.refl_apply]⟩
    rw [dif_pos hex]
    set w_c := hex.choose_spec.choose_spec.choose with hw_c_def
    have hw_c : w_c ∈ ForwardTube d n := hex.choose_spec.choose_spec.choose_spec.1
    have hz_eq := hex.choose_spec.choose_spec.choose_spec.2
    have h_eq : complexLorentzAction hex.choose_spec.choose
        (fun k => w_c (hex.choose k)) =
        complexLorentzAction 1 (fun k => z ((Equiv.refl (Fin n)) k)) := by
      rw [← hz_eq, complexLorentzAction_one]; rfl
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local hw_c hz h_eq
  refine ⟨fullExtendF F, hProp1, hProp2, ?_, ?_, ?_⟩
  -- === Property 3: Complex Lorentz invariance ===
  -- If z = Λ'·w_p with w_p ∈ PermutedForwardTube π, then Λz = (ΛΛ')·w_p.
  -- Convert w_p to w_ft ∈ ForwardTube via w_ft = fun k => w_p (π k),
  -- then both fullExtendF(Λz) and fullExtendF(z) reduce to the same FT preimage.
  · intro Λ z hz
    simp only [fullExtendF]
    obtain ⟨π, Λ', w_p, hw_p, hzw⟩ := Set.mem_iUnion.mp hz
    -- w_p ∈ PermutedForwardTube means w_ft := (fun k => w_p (π k)) ∈ ForwardTube
    set w_ft := fun k => w_p (π k) with hw_ft_def
    have hw_ft : w_ft ∈ ForwardTube d n := hw_p
    -- z = Λ'·w_p = Λ'·(fun k => w_ft (π⁻¹ k))
    have hw_p_eq : w_p = fun k => w_ft (π⁻¹ k) := by
      ext k; simp [hw_ft_def]
    have hex_z : ∃ (π' : Equiv.Perm (Fin n)) (Λ'' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ z = complexLorentzAction Λ'' (fun k => w' (π' k)) :=
      ⟨π⁻¹, Λ', w_ft, hw_ft, by rw [hzw, hw_p_eq]⟩
    have hex_Λz : ∃ (π' : Equiv.Perm (Fin n)) (Λ'' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧
        complexLorentzAction Λ z =
          complexLorentzAction Λ'' (fun k => w' (π' k)) :=
      ⟨π⁻¹, Λ * Λ', w_ft, hw_ft, by rw [hzw, hw_p_eq, complexLorentzAction_mul]⟩
    rw [dif_pos hex_Λz, dif_pos hex_z]
    -- Both choices lead to FT preimages related by Lorentz + permutation.
    -- By fullExtendF_well_defined, F-values agree.
    have hΛz_eq := hex_Λz.choose_spec.choose_spec.choose_spec.2
    -- hΛz_eq : Λ·z = Λ_Λz·(π_Λz·w_Λz)
    have hz_eq' := hex_z.choose_spec.choose_spec.choose_spec.2
    -- hz_eq' : z = Λ_z·(π_z·w_z)
    have h_eq : complexLorentzAction hex_Λz.choose_spec.choose
        (fun k => hex_Λz.choose_spec.choose_spec.choose (hex_Λz.choose k)) =
        complexLorentzAction (Λ * hex_z.choose_spec.choose)
        (fun k => hex_z.choose_spec.choose_spec.choose (hex_z.choose k)) := by
      rw [complexLorentzAction_mul, ← hz_eq']
      exact hΛz_eq.symm
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
      hex_Λz.choose_spec.choose_spec.choose_spec.1
      hex_z.choose_spec.choose_spec.choose_spec.1 h_eq
  -- === Property 4: Permutation symmetry ===
  -- fullExtendF F (z∘π) = fullExtendF F z follows from fullExtendF_well_defined:
  -- both chosen preimages yield representations of z∘π.
  · intro π z hz
    simp only [fullExtendF]
    obtain ⟨π₀, Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
    set w_ft := fun k => w₀ (π₀ k) with hw_ft_def
    have hw_ft : w_ft ∈ ForwardTube d n := hw₀
    have hw₀_eq : w₀ = fun k => w_ft (π₀⁻¹ k) := by ext k; simp [hw_ft_def]
    have hex_z : ∃ (π' : Equiv.Perm (Fin n)) (Λ' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ z = complexLorentzAction Λ' (fun k => w' (π' k)) :=
      ⟨π₀⁻¹, Λ₀, w_ft, hw_ft, by rw [hzw₀, hw₀_eq]⟩
    have hex_πz : ∃ (π' : Equiv.Perm (Fin n)) (Λ' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ (fun k => z (π k)) =
          complexLorentzAction Λ' (fun k => w' (π' k)) := by
      refine ⟨π₀⁻¹ * π, Λ₀, w_ft, hw_ft, ?_⟩
      rw [hzw₀, hw₀_eq]; ext k μ
      simp only [complexLorentzAction, Equiv.Perm.mul_apply]
    rw [dif_pos hex_πz, dif_pos hex_z]
    have hπz_eq := hex_πz.choose_spec.choose_spec.choose_spec.2
    have hz_eq' := hex_z.choose_spec.choose_spec.choose_spec.2
    -- Build: both chosen representations equal z∘π
    -- From hz_eq': z = Λ_z·(π_z·w_z), so z∘π = Λ_z·((π_z*π)·w_z)
    have h_zperm : (fun k => z (π k)) =
        complexLorentzAction hex_z.choose_spec.choose
        (fun k => hex_z.choose_spec.choose_spec.choose ((hex_z.choose * π) k)) := by
      ext k μ
      have := congr_fun (congr_fun hz_eq' (π k)) μ
      simp only [complexLorentzAction, Equiv.Perm.mul_apply] at this ⊢
      exact this
    have h_eq : complexLorentzAction hex_πz.choose_spec.choose
        (fun k => hex_πz.choose_spec.choose_spec.choose (hex_πz.choose k)) =
        complexLorentzAction hex_z.choose_spec.choose
        (fun k => hex_z.choose_spec.choose_spec.choose ((hex_z.choose * π) k)) :=
      hπz_eq.symm.trans h_zperm
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
      hex_πz.choose_spec.choose_spec.choose_spec.1
      hex_z.choose_spec.choose_spec.choose_spec.1 h_eq
  -- === Property 5: Uniqueness ===
  -- By the identity theorem for product types (`identity_theorem_product`):
  -- G and fullExtendF are holomorphic on PET (open, connected) and agree on FT
  -- (open, nonempty subset of PET), so they agree on all of PET.
  · intro G hG_holo hG_eq
    -- fullExtendF F is differentiable on PET (Property 1)
    have hF_ext_holo : DifferentiableOn ℂ (fullExtendF F) (PermutedExtendedTube d n) :=
      hProp1
    -- PET is open
    have hPET_open := @isOpen_permutedExtendedTube d n
    -- PET is connected: different permutation sectors don't directly overlap;
    -- connectedness requires applying the (proved) edge-of-the-wedge theorem to
    -- glue sectors at Jost point boundaries via local commutativity.
    have hPET_conn : IsConnected (PermutedExtendedTube d n) := by
      constructor
      · exact (forwardTube_nonempty (d := d) (n := n)).mono
          forwardTube_subset_permutedExtendedTube
      · -- PET = ⋃_π ⋃_Λ Λ·(π·FT). Each orbit Λ·(π·FT) is connected (image of
        -- convex FT under continuous maps). Adjacent permutation sectors (differing
        -- by one swap(i,i+1)) have overlapping Lorentz orbits by the EOW theorem:
        -- the glued holomorphic extension from FT ∪ σ·FT lives on an open connected
        -- domain that intersects both sectors' Lorentz orbits. Iterating over all
        -- adjacent swaps (which generate S_n) connects all sectors.
        exact permutedExtendedTube_isPreconnected
    -- Pick z₀ ∈ FT ⊆ PET
    obtain ⟨z₀, hz₀⟩ := forwardTube_nonempty (d := d) (n := n)
    have hz₀_PET := forwardTube_subset_permutedExtendedTube hz₀
    -- G and fullExtendF agree on FT, which is an open neighborhood of z₀
    have hagree : G =ᶠ[nhds z₀] fullExtendF F := by
      apply Filter.eventuallyEq_of_mem (isOpen_forwardTube.mem_nhds hz₀)
      intro w hw
      rw [hG_eq w hw, hProp2 w hw]
    -- By identity theorem on product types
    have h_eq := identity_theorem_product hPET_open hPET_conn hG_holo hF_ext_holo hz₀_PET hagree
    intro z hz
    exact h_eq hz


end BHW
