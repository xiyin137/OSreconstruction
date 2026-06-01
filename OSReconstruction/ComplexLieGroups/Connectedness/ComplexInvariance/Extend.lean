import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-- The Lorentz-invariance set used in the global clopen argument:
`Λ ∈ lorentzInvarianceSet` iff `F (Λ·w) = F w` for every `w ∈ FT`
with `Λ·w ∈ FT`. -/
private def lorentzInvarianceSet (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) : Set (ComplexLorentzGroup d) :=
  { Λ | ∀ w, w ∈ ForwardTube d n → complexLorentzAction Λ w ∈ ForwardTube d n →
      F (complexLorentzAction Λ w) = F w }

/-- Left multiplication by real Lorentz elements preserves
`lorentzInvarianceSet`. -/
private lemma lorentzInvarianceSet_left_mul_ofReal (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {Λ : ComplexLorentzGroup d}
    (hΛT : Λ ∈ lorentzInvarianceSet (d := d) n F)
    (R : RestrictedLorentzGroup d) :
    ComplexLorentzGroup.ofReal R * Λ ∈ lorentzInvarianceSet (d := d) n F := by
  intro w hw hRw
  have hΛw : complexLorentzAction Λ w ∈ ForwardTube d n := by
    have hmul :
        complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹)
          (complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ) w) =
        complexLorentzAction Λ w := by
      calc
        complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹)
            (complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ) w)
            = complexLorentzAction
                (ComplexLorentzGroup.ofReal R⁻¹ * (ComplexLorentzGroup.ofReal R * Λ)) w := by
                symm
                exact complexLorentzAction_mul (ComplexLorentzGroup.ofReal R⁻¹)
                  (ComplexLorentzGroup.ofReal R * Λ) w
        _ = complexLorentzAction
              ((ComplexLorentzGroup.ofReal R⁻¹ * ComplexLorentzGroup.ofReal R) * Λ) w := by
              simp [mul_assoc]
        _ = complexLorentzAction
              (ComplexLorentzGroup.ofReal (R⁻¹ * R) * Λ) w := by
              rw [← ofReal_mul_eq]
        _ = complexLorentzAction
              (ComplexLorentzGroup.ofReal (1 : RestrictedLorentzGroup d) * Λ) w := by
              simp
        _ = complexLorentzAction Λ w := by
              simp [ofReal_one_eq]
    have hback :
        complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹)
          (complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ) w) ∈ ForwardTube d n :=
      ofReal_preserves_forwardTube (R := R⁻¹)
        (complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ) w) hRw
    simpa [hmul] using hback
  have hcore : F (complexLorentzAction Λ w) = F w := hΛT w hw hΛw
  have hreal :
      F (complexLorentzAction (ComplexLorentzGroup.ofReal R)
        (complexLorentzAction Λ w)) = F (complexLorentzAction Λ w) :=
    hF_real_inv R (complexLorentzAction Λ w) hΛw
  have hmul :
      complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ) w =
        complexLorentzAction (ComplexLorentzGroup.ofReal R) (complexLorentzAction Λ w) := by
    simpa using complexLorentzAction_mul (ComplexLorentzGroup.ofReal R) Λ w
  calc
    F (complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ) w)
        = F (complexLorentzAction (ComplexLorentzGroup.ofReal R) (complexLorentzAction Λ w)) := by
            rw [hmul]
    _ = F (complexLorentzAction Λ w) := hreal
    _ = F w := hcore

/-- Right multiplication by real Lorentz elements preserves
`lorentzInvarianceSet`. -/
private lemma lorentzInvarianceSet_right_mul_ofReal (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {Λ : ComplexLorentzGroup d}
    (hΛT : Λ ∈ lorentzInvarianceSet (d := d) n F)
    (R : RestrictedLorentzGroup d) :
    Λ * ComplexLorentzGroup.ofReal R ∈ lorentzInvarianceSet (d := d) n F := by
  intro w hw hΛRw
  have hRw : complexLorentzAction (ComplexLorentzGroup.ofReal R) w ∈ ForwardTube d n :=
    ofReal_preserves_forwardTube (R := R) w hw
  have hcore :
      F (complexLorentzAction Λ (complexLorentzAction (ComplexLorentzGroup.ofReal R) w)) =
      F (complexLorentzAction (ComplexLorentzGroup.ofReal R) w) :=
    hΛT (complexLorentzAction (ComplexLorentzGroup.ofReal R) w) hRw
      (by
        have hmul :
            complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) w =
              complexLorentzAction Λ (complexLorentzAction (ComplexLorentzGroup.ofReal R) w) := by
          simpa using complexLorentzAction_mul Λ (ComplexLorentzGroup.ofReal R) w
        simpa [hmul] using hΛRw)
  have hreal : F (complexLorentzAction (ComplexLorentzGroup.ofReal R) w) = F w :=
    hF_real_inv R w hw
  have hmul :
      complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) w =
        complexLorentzAction Λ (complexLorentzAction (ComplexLorentzGroup.ofReal R) w) := by
    simpa using complexLorentzAction_mul Λ (ComplexLorentzGroup.ofReal R) w
  calc
    F (complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) w)
        = F (complexLorentzAction Λ (complexLorentzAction (ComplexLorentzGroup.ofReal R) w)) := by
            rw [hmul]
    _ = F (complexLorentzAction (ComplexLorentzGroup.ofReal R) w) := hcore
    _ = F w := hreal

theorem complex_lorentz_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  -- === Define T = {Λ : ∀ w ∈ FT, Λ·w ∈ FT → F(Λ·w) = F(w)} ===
  set T : Set (ComplexLorentzGroup d) := lorentzInvarianceSet (d := d) n F with hT_def
  -- Suffices: T = univ
  suffices hT_univ : T = Set.univ by
    intro Λ z hz hΛz; exact (Set.eq_univ_iff_forall.mp hT_univ Λ) z hz hΛz
  -- === G is connected ===
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  -- === 1 ∈ T ===
  have h1T : (1 : ComplexLorentzGroup d) ∈ T := by
    intro w hw _; rw [complexLorentzAction_one]
  -- === Define U = {Λ : D_Λ ≠ ∅} ===
  set U : Set (ComplexLorentzGroup d) :=
    { Λ | ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n } with hU_def
  -- === Tᶜ ⊆ U (if Λ ∉ T, the witness w₀ shows D_Λ ≠ ∅) ===
  have hTc_sub_U : Tᶜ ⊆ U := by
    intro Λ hΛ
    simp [hT_def, lorentzInvarianceSet] at hΛ
    push_neg at hΛ
    obtain ⟨w, hw, hΛw, _⟩ := hΛ
    exact ⟨w, hw, hΛw⟩
  -- === T is closed ===
  have hT_closed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro Λ₀ hΛ₀
    simp [hT_def, lorentzInvarianceSet] at hΛ₀
    push_neg at hΛ₀
    obtain ⟨w₀, hw₀, hΛ₀w₀, hne⟩ := hΛ₀
    have hV_open : IsOpen {Λ : ComplexLorentzGroup d |
        complexLorentzAction Λ w₀ ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage (continuous_complexLorentzAction_fst w₀)
    have hcomp : ContinuousOn (fun Λ => F (complexLorentzAction Λ w₀))
        {Λ | complexLorentzAction Λ w₀ ∈ ForwardTube d n} :=
      hF_holo.continuousOn.comp (continuous_complexLorentzAction_fst w₀).continuousOn
        fun Λ hΛ => hΛ
    refine ⟨{Λ | complexLorentzAction Λ w₀ ∈ ForwardTube d n} ∩
        (fun Λ => F (complexLorentzAction Λ w₀)) ⁻¹' {F w₀}ᶜ,
      fun Λ ⟨hΛw₀, hΛne⟩ => ?_,
      hcomp.isOpen_inter_preimage hV_open isOpen_compl_singleton,
      ⟨hΛ₀w₀, hne⟩⟩
    intro hΛT
    exact hΛne (hΛT w₀ hw₀ hΛw₀)
  -- === T ∩ U is open (identity theorem argument at Λ₀ ∈ T ∩ U) ===
  have hTU_open : IsOpen (T ∩ U) := by
    rw [isOpen_iff_forall_mem_open]
    intro Λ₀ ⟨hΛ₀, hΛ₀_U⟩
    -- Get z₀ ∈ D_{Λ₀} from Λ₀ ∈ U
    obtain ⟨z₀, hz₀, hΛ₀z₀⟩ := hΛ₀_U
    -- Near-identity invariance at z₀ gives nhd V of 1 where F(Λ'·z₀) = F(z₀)
    have h_near_z₀ := BHW.near_identity_invariance n F hF_holo hF_real_inv z₀ hz₀
    -- Left multiplication by Λ₀⁻¹ is continuous and maps Λ₀ to 1
    have h_left_mul : Continuous (fun Λ : ComplexLorentzGroup d => Λ₀⁻¹ * Λ) := by
      have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      change Continuous (fun x : ComplexLorentzGroup d => Λ₀⁻¹.val * x.val)
      exact continuous_const.mul ComplexLorentzGroup.continuous_val
    have h_tend : Tendsto (fun Λ => Λ₀⁻¹ * Λ) (𝓝 Λ₀) (𝓝 (1 : ComplexLorentzGroup d)) := by
      rw [show (1 : ComplexLorentzGroup d) = Λ₀⁻¹ * Λ₀ from (inv_mul_cancel Λ₀).symm]
      exact h_left_mul.continuousAt.tendsto
    -- Pull back BHW.near_identity_invariance through Λ ↦ Λ₀⁻¹Λ
    have h_near_pullback : ∀ᶠ Λ in 𝓝 Λ₀,
        complexLorentzAction (Λ₀⁻¹ * Λ) z₀ ∈ ForwardTube d n →
        F (complexLorentzAction (Λ₀⁻¹ * Λ) z₀) = F z₀ :=
      h_tend.eventually h_near_z₀
    -- z₀ ∈ D_Λ eventually (since Λ·z₀ → Λ₀·z₀ ∈ FT)
    have h_ev_DΛ : ∀ᶠ Λ in 𝓝 Λ₀,
        complexLorentzAction Λ z₀ ∈ ForwardTube d n :=
      (continuous_complexLorentzAction_fst z₀).continuousAt.preimage_mem_nhds
        (isOpen_forwardTube.mem_nhds hΛ₀z₀)
    -- z₀ ∈ D_{Λ'} eventually (since (Λ₀⁻¹Λ)·z₀ → z₀ ∈ FT)
    have h_ev_DΛ' : ∀ᶠ Λ in 𝓝 Λ₀,
        complexLorentzAction (Λ₀⁻¹ * Λ) z₀ ∈ ForwardTube d n := by
      have : (fun Λ : ComplexLorentzGroup d => complexLorentzAction (Λ₀⁻¹ * Λ) z₀) =
          (fun Λ' => complexLorentzAction Λ' z₀) ∘ (fun Λ => Λ₀⁻¹ * Λ) := rfl
      have hcont : Continuous (fun Λ : ComplexLorentzGroup d =>
          complexLorentzAction (Λ₀⁻¹ * Λ) z₀) := by
        rw [this]; exact (continuous_complexLorentzAction_fst z₀).comp h_left_mul
      have h1z₀ : complexLorentzAction (Λ₀⁻¹ * Λ₀) z₀ ∈ ForwardTube d n := by
        rw [inv_mul_cancel, complexLorentzAction_one]; exact hz₀
      exact hcont.continuousAt.preimage_mem_nhds (isOpen_forwardTube.mem_nhds h1z₀)
    -- Uniform near-identity invariance at z₀
    obtain ⟨U_unif, hU_nhd, h_unif_inv⟩ :=
      BHW.uniform_near_identity_invariance n F hF_holo hF_real_inv z₀ hz₀
    -- Pull back through Λ ↦ Λ₀⁻¹Λ
    have h_uniform_pullback : ∀ᶠ Λ in 𝓝 Λ₀,
        ∀ w ∈ U_unif, w ∈ ForwardTube d n →
          complexLorentzAction (Λ₀⁻¹ * Λ) w ∈ ForwardTube d n →
          F (complexLorentzAction (Λ₀⁻¹ * Λ) w) = F w :=
      h_tend.eventually h_unif_inv
    -- Combine all eventually conditions: Λ ∈ T ∩ U
    have h_eventually : ∀ᶠ Λ in 𝓝 Λ₀, Λ ∈ T ∩ U := by
      filter_upwards [h_near_pullback, h_ev_DΛ, h_ev_DΛ', h_uniform_pullback]
        with Λ h_near hΛz₀ hΛ'z₀ h_unif
      refine ⟨?_, z₀, hz₀, hΛz₀⟩
      intro w hw hΛw
      -- Set Λ' := Λ₀⁻¹ * Λ
      set Λ' := Λ₀⁻¹ * Λ with hΛ'_def
      have hΛ_eq : Λ = Λ₀ * Λ' := by rw [hΛ'_def, ← mul_assoc, mul_inv_cancel, one_mul]
      -- === Step 1: g ≡ 0 on D_{Λ'} by identity theorem ===
      have hg_holo : DifferentiableOn ℂ (fun z => F (complexLorentzAction Λ' z) - F z)
          {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ' z ∈ ForwardTube d n} :=
        (hF_holo.comp (differentiable_complexLorentzAction_snd Λ').differentiableOn
          (fun z hz => hz.2)).sub (hF_holo.mono fun z hz => hz.1)
      have hg_zero_near : (fun z => F (complexLorentzAction Λ' z) - F z) =ᶠ[𝓝 z₀] 0 := by
        apply Filter.eventuallyEq_iff_exists_mem.mpr
        exact ⟨U_unif ∩ {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ' z ∈ ForwardTube d n},
          Filter.inter_mem hU_nhd ((isOpen_d_lambda Λ').mem_nhds ⟨hz₀, hΛ'z₀⟩),
          fun z ⟨hz_U, hz_FT, hz_Λ'⟩ => sub_eq_zero.mpr (h_unif z hz_U hz_FT hz_Λ')⟩
      have hg_zero : ∀ z, z ∈ ForwardTube d n →
          complexLorentzAction Λ' z ∈ ForwardTube d n →
          F (complexLorentzAction Λ' z) = F z := by
        intro z hz hΛ'z
        exact sub_eq_zero.mp (BHW.eq_zero_on_convex_of_eventuallyEq_zero (isOpen_d_lambda Λ')
          (d_lambda_convex Λ') hg_holo ⟨hz₀, hΛ'z₀⟩ hg_zero_near z ⟨hz, hΛ'z⟩)
      -- === Step 2: f ≡ 0 on D_Λ by identity theorem ===
      have hf_holo' : DifferentiableOn ℂ (fun z => F (complexLorentzAction Λ z) - F z)
          {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} :=
        (hF_holo.comp (differentiable_complexLorentzAction_snd Λ).differentiableOn
          (fun z hz => hz.2)).sub (hF_holo.mono fun z hz => hz.1)
      have hf_zero_near : (fun z => F (complexLorentzAction Λ z) - F z) =ᶠ[𝓝 z₀] 0 := by
        apply Filter.eventuallyEq_iff_exists_mem.mpr
        refine ⟨{z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} ∩
            {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ' z ∈ ForwardTube d n},
          Filter.inter_mem ((isOpen_d_lambda Λ).mem_nhds ⟨hz₀, hΛz₀⟩)
            ((isOpen_d_lambda Λ').mem_nhds ⟨hz₀, hΛ'z₀⟩),
          fun z ⟨⟨hz_FT, hz_Λ⟩, _, hz_Λ'⟩ => ?_⟩
        show F (complexLorentzAction Λ z) - F z = 0
        have h_action : complexLorentzAction Λ z =
            complexLorentzAction Λ₀ (complexLorentzAction Λ' z) := by
          rw [← complexLorentzAction_mul, ← hΛ_eq]
        rw [h_action, hΛ₀ _ hz_Λ' (by rwa [← h_action]), hg_zero z hz_FT hz_Λ', sub_self]
      exact sub_eq_zero.mp (BHW.eq_zero_on_convex_of_eventuallyEq_zero (isOpen_d_lambda Λ)
        (d_lambda_convex Λ) hf_holo' ⟨hz₀, hΛz₀⟩ hf_zero_near w ⟨hw, hΛw⟩)
    -- Extract open set from filter
    obtain ⟨W, hW_nhd, hW_sub⟩ := Filter.Eventually.exists_mem h_eventually
    obtain ⟨V, hV_sub, hV_open, hΛ₀V⟩ := mem_nhds_iff.mp hW_nhd
    exact ⟨V, fun x hx => hW_sub x (hV_sub hx), hV_open, hΛ₀V⟩
  -- === U is connected ===
  have hU_conn : IsPreconnected U := BHW.nonemptyDomain_isPreconnected
  -- === Conclude T = univ via IsPreconnected on U ===
  -- Key: U = (T ∩ U) ⊔ (Tᶜ ∩ U). Both are open. U preconnected + T ∩ U ≠ ∅ → Tᶜ ∩ U = ∅.
  -- Since Tᶜ ⊆ U, we get Tᶜ = ∅, hence T = univ.
  by_contra hT_ne
  have hT_ne' : ∃ a, a ∉ T := (Set.ne_univ_iff_exists_notMem T).mp hT_ne
  obtain ⟨Λ_bad, hΛ_bad⟩ := hT_ne'
  -- Λ_bad ∉ T → Λ_bad ∈ Tᶜ ⊆ U → (Tᶜ ∩ U).Nonempty
  have hTcU_ne : (U ∩ Tᶜ).Nonempty := ⟨Λ_bad, hTc_sub_U hΛ_bad, hΛ_bad⟩
  -- 1 ∈ T ∩ U
  obtain ⟨w₀, hw₀⟩ := forwardTube_nonempty (d := d) (n := n)
  have h1U : (1 : ComplexLorentzGroup d) ∈ U :=
    ⟨w₀, hw₀, (complexLorentzAction_one w₀).symm ▸ hw₀⟩
  have hTU_ne : (U ∩ (T ∩ U)).Nonempty := ⟨1, h1U, h1T, h1U⟩
  -- U ⊆ (T ∩ U) ∪ Tᶜ
  have hU_cover : U ⊆ (T ∩ U) ∪ Tᶜ := by
    intro Λ hΛU
    by_cases hΛT : Λ ∈ T
    · exact Or.inl ⟨hΛT, hΛU⟩
    · exact Or.inr hΛT
  -- Apply IsPreconnected: U ∩ ((T ∩ U) ∩ Tᶜ) is nonempty
  have h_absurd := hU_conn (T ∩ U) Tᶜ hTU_open (isOpen_compl_iff.mpr hT_closed)
    hU_cover hTU_ne hTcU_ne
  -- But (T ∩ U) ∩ Tᶜ = ∅
  obtain ⟨Λ, _, hΛ_TU, hΛ_Tc⟩ := h_absurd
  exact hΛ_Tc hΛ_TU.1

/-! ### The permuted extended tube -/


/-! ### Extension to the extended tube -/

/-- F extends to the extended tube via complex Lorentz transformations:
    F_ext(Λ·w) = F(w) for w ∈ FT. Well-defined by `complex_lorentz_invariance`.

    For z ∈ ExtendedTube, choose a preimage w ∈ FT with z = Λ·w for some Λ,
    and define extendF(z) = F(w). The choice doesn't matter by
    `complex_lorentz_invariance`. For z ∉ ExtendedTube, define extendF(z) = 0. -/
def extendF (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w
    then F h.choose
    else 0

/-- `extendF` agrees with F on the forward tube. -/
theorem extendF_eq_on_forwardTube (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    extendF F z = F z := by
  simp only [extendF]
  -- The existential is satisfied: z ∈ FT, take w = z and Λ = 1.
  have hex : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w :=
    ⟨z, hz, 1, (complexLorentzAction_one z).symm⟩
  rw [dif_pos hex]
  -- The chosen w satisfies w ∈ FT and z = Λ·w for some Λ.
  -- Need: F(chosen_w) = F(z).
  have hspec := hex.choose_spec
  have hw : hex.choose ∈ ForwardTube d n := hspec.1
  obtain ⟨Λ, hzΛw⟩ := hspec.2
  -- z = Λ·w, so Λ·w ∈ FT (since z ∈ FT)
  have hΛw : complexLorentzAction Λ hex.choose ∈ ForwardTube d n := hzΛw ▸ hz
  -- By complex_lorentz_invariance: F(Λ·w) = F(w), and z = Λ·w, so F(w) = F(z).
  have key := complex_lorentz_invariance n F hF_holo hF_real_inv Λ hex.choose hw hΛw
  -- key : F(Λ·w) = F(w).  congr_arg F hzΛw.symm : F(Λ·w) = F(z).
  exact key.symm.trans (congr_arg F hzΛw.symm)

/-- Any two forward-tube preimages of the same extended-tube point give the same F-value.
    This is the key well-definedness lemma for `extendF`. -/
theorem extendF_preimage_eq (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ} (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ w₁ = complexLorentzAction Λ₂ w₂) :
    F w₁ = F w₂ := by
  -- From Λ₁·w₁ = Λ₂·w₂, apply Λ₂⁻¹: (Λ₂⁻¹*Λ₁)·w₁ = w₂
  have hrel : complexLorentzAction (Λ₂⁻¹ * Λ₁) w₁ = w₂ := by
    have := congr_arg (complexLorentzAction Λ₂⁻¹) h
    rwa [← complexLorentzAction_mul, complexLorentzAction_inv] at this
  -- w₂ = (Λ₂⁻¹*Λ₁)·w₁ ∈ FT, so by complex_lorentz_invariance: F(w₂) = F(w₁)
  have := complex_lorentz_invariance n F hF_holo hF_real_inv (Λ₂⁻¹ * Λ₁) w₁ hw₁ (hrel ▸ hw₂)
  rw [hrel] at this; exact this.symm

/-- Any two forward-tube preimages of the same extended-tube point give the
same value when direct complex-Lorentz invariance on the forward tube is
already available.  This is the `hF_cinv` version of
`extendF_preimage_eq`; it is used by source-descent branch-law proofs so they
do not have to rederive complex invariance from real Lorentz invariance. -/
theorem extendF_preimage_eq_of_cinv (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ w₁ = complexLorentzAction Λ₂ w₂) :
    F w₁ = F w₂ := by
  have hrel : complexLorentzAction (Λ₂⁻¹ * Λ₁) w₁ = w₂ := by
    have := congr_arg (complexLorentzAction Λ₂⁻¹) h
    rwa [← complexLorentzAction_mul, complexLorentzAction_inv] at this
  have hcinv := hF_cinv (Λ₂⁻¹ * Λ₁) w₁ hw₁ (hrel ▸ hw₂)
  rw [hrel] at hcinv
  exact hcinv.symm

/-- `extendF` is invariant under complex Lorentz transformations on the extended tube. -/
theorem extendF_complex_lorentz_invariant (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n) :
    extendF F (complexLorentzAction Λ z) = extendF F z := by
  -- z ∈ ExtendedTube: ∃ Λ₀, w₀ with z = Λ₀·w₀, w₀ ∈ FT
  obtain ⟨Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
  simp only [extendF]
  -- The existential is satisfied for z
  have hex_z : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d), z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ₀, hzw₀⟩
  -- The existential is satisfied for Λ·z (since Λ·z = (Λ*Λ₀)·w₀)
  have hex_Λz : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d),
        complexLorentzAction Λ z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ * Λ₀, by rw [hzw₀, complexLorentzAction_mul]⟩
  rw [dif_pos hex_Λz, dif_pos hex_z]
  -- hex_Λz.choose and hex_z.choose are both in FT.
  -- They are preimages of Λ·z and z respectively, related by Λ.
  obtain ⟨hw_Λz, Λ₃, hΛz_eq⟩ := hex_Λz.choose_spec
  obtain ⟨hw_z, Λ₂, hz_eq⟩ := hex_z.choose_spec
  -- Both preimages map to the same point (up to Lorentz transformations):
  -- Λ₃·hex_Λz.choose = Λ·z = Λ·(Λ₂·hex_z.choose) = (Λ*Λ₂)·hex_z.choose
  -- By extendF_preimage_eq, F values agree.
  exact extendF_preimage_eq n F hF_holo hF_real_inv hw_Λz hw_z
    (hΛz_eq.symm.trans ((congr_arg (complexLorentzAction Λ) hz_eq).trans
      (complexLorentzAction_mul Λ Λ₂ hex_z.choose).symm))

/-- Direct complex-Lorentz invariance of `extendF` on the extended tube.

This version consumes the already-upgraded forward-tube complex invariance
hypothesis directly.  It is the lower support bridge used by the
Hall-Wightman source branch-law route; it does not use PET, EOW, locality, or
any scalar-representative data. -/
theorem extendF_complexLorentzInvariant_of_cinv (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z)
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n) :
    extendF F (complexLorentzAction Λ z) = extendF F z := by
  obtain ⟨Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
  simp only [extendF]
  have hex_z : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d),
        z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ₀, hzw₀⟩
  have hex_Λz : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d),
        complexLorentzAction Λ z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ * Λ₀, by rw [hzw₀, complexLorentzAction_mul]⟩
  rw [dif_pos hex_Λz, dif_pos hex_z]
  obtain ⟨hw_Λz, Λ₃, hΛz_eq⟩ := hex_Λz.choose_spec
  obtain ⟨hw_z, Λ₂, hz_eq⟩ := hex_z.choose_spec
  exact extendF_preimage_eq_of_cinv n F hF_cinv hw_Λz hw_z
    (hΛz_eq.symm.trans ((congr_arg (complexLorentzAction Λ) hz_eq).trans
      (complexLorentzAction_mul Λ Λ₂ hex_z.choose).symm))


end BHW
