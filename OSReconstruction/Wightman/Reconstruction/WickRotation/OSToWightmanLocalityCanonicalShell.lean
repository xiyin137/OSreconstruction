import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Compact

/-!
# Canonical-Shell Transport for Theorem-2 Locality

This file contains the local boundary-approach step used by the OS I §4.5
locality route.  A real-edge equality of the BHW `extendF` branch, on compact
tests whose real support lies in the extended tube, is transported to the
canonical forward-shell boundary limit consumed by the final Wightman locality
transfer.
-/

noncomputable section

open scoped Classical NNReal
open BigOperators Filter MeasureTheory Matrix LorentzLieGroup

namespace BHW

variable {d : ℕ} [NeZero d]

private theorem local_bhw_inOpenForwardCone_iff
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

private theorem shell_mem_forwardTube_of_inForwardCone {n : ℕ}
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    (x : NPointDomain d n) (ε : ℝ) (hε : 0 < ε) :
    (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) ∈
      BHW.ForwardTube d n := by
  intro k
  have hk := hη k
  let diff : Fin (d + 1) → ℝ := fun μ => η k μ -
    (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
  suffices hsuff : BHW.InOpenForwardCone d (fun μ => ε * diff μ) by
    convert hsuff using 1
    ext μ
    simp only [diff]
    split_ifs with h
    · simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      ring_nf
  have hkBHW : BHW.InOpenForwardCone d diff := by
    exact (local_bhw_inOpenForwardCone_iff (d := d) diff).2 hk
  obtain ⟨hk0, hkneg⟩ := hkBHW
  refine ⟨mul_pos hε hk0, ?_⟩
  show ∑ i : Fin (d + 1),
      LorentzLieGroup.minkowskiSignature d i * (ε * diff i) ^ 2 < 0
  have hsq :
      ∑ i : Fin (d + 1),
          LorentzLieGroup.minkowskiSignature d i * (ε * diff i) ^ 2 =
        ε ^ 2 *
          ∑ i : Fin (d + 1), LorentzLieGroup.minkowskiSignature d i * diff i ^ 2 := by
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring_nf
  rw [hsq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (ne_of_gt hε)) hkneg

/-- Transport a compact real-edge `extendF` pairing equality to the canonical
forward-shell boundary limit.

This is the local DCT/collar step in the OS/Jost locality argument.  It does
not assume finite-height equality of the canonical shell; it only uses the
distributional boundary value of the forward-tube function at real extended
tube points and uniqueness of the resulting limit. -/
theorem canonicalShell_difference_tendsto_zero_of_extendF_pairing_eq
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.ForwardTube d n →
      BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
      F (BHW.complexLorentzAction Λ z) = F z)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ))
    (hf_ET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hg_ET : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hreal_eq :
      (∫ x : NPointDomain d n, BHW.extendF F (BHW.realEmbed x) * g x) =
        ∫ x : NPointDomain d n, BHW.extendF F (BHW.realEmbed x) * f x) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
            F (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * g x) -
          ∫ x : NPointDomain d n,
            F (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hη_FT :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) ∈
          BHW.ForwardTube d n := by
    intro x ε hε
    exact shell_mem_forwardTube_of_inForwardCone (d := d) η hη x ε hε
  have hg_tendsto :=
    BHW.tendsto_extendF_boundary_integral_of_hasCompactSupport_ET
      (d := d) n F hF_holo hF_cinv g hg_compact η hη_FT hg_ET
  have hf_tendsto :=
    BHW.tendsto_extendF_boundary_integral_of_hasCompactSupport_ET
      (d := d) n F hF_holo hF_cinv f hf_compact η hη_FT hf_ET
  have hsub :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d n,
              F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * g x) -
            ∫ x : NPointDomain d n,
              F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((∫ x : NPointDomain d n, BHW.extendF F (BHW.realEmbed x) * g x) -
            ∫ x : NPointDomain d n, BHW.extendF F (BHW.realEmbed x) * f x)) :=
    hg_tendsto.sub hf_tendsto
  have htarget :
      ((∫ x : NPointDomain d n, BHW.extendF F (BHW.realEmbed x) * g x) -
        ∫ x : NPointDomain d n, BHW.extendF F (BHW.realEmbed x) * f x) = 0 := by
    rw [hreal_eq, sub_self]
  simpa [η, htarget] using hsub

omit [NeZero d] in
private theorem local_integral_perm_eq_self {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (σ k)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- A local Figure-2-4 compact packet supplies the canonical forward-shell
pairing limit for compact tests supported in its identity real patch.

This is the first checked production bridge from the OS45 real-patch equality
surface to the canonical-shell boundary-value surface used by theorem 2. -/
theorem canonicalShell_difference_tendsto_zero_of_compactFigure24Patch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hCompact : BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc)
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_tsupport :
      tsupport (f : NPointDomain d n → ℂ) ⊆ hCompact.realPatch 1) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * g x) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  classical
  intro τ eτ g
  have hF_holo_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv_BHW :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ) := by
    simpa [g, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hf_compact.comp_homeomorph eτ.toHomeomorph
  have hf_ET :
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    have hxpatch : x ∈ hCompact.realPatch 1 := hf_tsupport hx
    have hxsector := hCompact.realPatch_left_sector 1 x hxpatch
    simpa [BHW.permutedExtendedTubeSector] using hxsector
  have hg_tsupport :
      tsupport (g : NPointDomain d n → ℂ) =
        eτ.toHomeomorph ⁻¹' tsupport (f : NPointDomain d n → ℂ) := by
    simpa [g, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage
        (g := (f : NPointDomain d n → ℂ)) eτ.toHomeomorph)
  have hg_ET :
      ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
        BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    have hxτ : (fun k => x (τ k)) ∈ tsupport (f : NPointDomain d n → ℂ) := by
      simpa [hg_tsupport, eτ] using hx
    have hxpatch : (fun k => x (τ k)) ∈ hCompact.realPatch 1 := hf_tsupport hxτ
    have hxsector := hCompact.realPatch_right_sector 1 (fun k => x (τ k)) hxpatch
    have hxsector' :
        (fun k => BHW.realEmbed (fun k => x (τ k)) (τ k)) ∈
          BHW.ExtendedTube d n := by
      simpa [BHW.permutedExtendedTubeSector, Equiv.Perm.mul_apply] using hxsector
    convert hxsector' using 1
    ext k μ
    simp [BHW.realEmbed, τ]
  have hleft_g_eq_right_f :
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * g x) =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.realEmbed x (τ k)) * f x := by
    let H : NPointDomain d n → ℂ := fun x =>
      BHW.extendF (bvt_F OS lgc n) (fun k => BHW.realEmbed x (τ k)) * f x
    have hperm := local_integral_perm_eq_self (d := d) τ H
    calc
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * g x)
          = ∫ x : NPointDomain d n, H (fun k => x (τ k)) := by
              congr 1
              ext x
              have hxperm :
                  (fun k => BHW.realEmbed (fun k => x (τ k)) (τ k)) =
                    BHW.realEmbed x := by
                ext k μ
                simp [BHW.realEmbed, τ]
              simp [H, g, eτ, hxperm]
      _ = ∫ x : NPointDomain d n, H x := hperm
      _ = ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.realEmbed x (τ k)) * f x := rfl
  have hpatch_eq :
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * f x) =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.realEmbed x (τ k)) * f x := by
    simpa [τ, Equiv.Perm.mul_apply] using
      hCompact.compact_branch_eq 1 f hf_compact hf_tsupport
  have hreal_eq :
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * g x) =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * f x :=
    hleft_g_eq_right_f.trans hpatch_eq.symm
  exact
    BHW.canonicalShell_difference_tendsto_zero_of_extendF_pairing_eq
      (d := d) (n := n) (bvt_F OS lgc n)
      hF_holo_BHW hF_cinv_BHW f g hf_compact hg_compact hf_ET hg_ET hreal_eq

private theorem exists_finite_schwartz_partitionOfUnity_on_compact_openCover
    {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K)
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ χ : α → SchwartzMap E ℂ,
      (∀ i, HasCompactSupport (χ i : E → ℂ)) ∧
      (∀ i, tsupport (χ i : E → ℂ) ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  let V : α → Set E := fun i => U i ∩ Metric.ball (0 : E) (R + 1)
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    exact (hU_open i).inter Metric.isOpen_ball
  have hV_relcompact : ∀ i, ∃ c r, V i ⊆ Metric.closedBall c r := by
    intro i
    refine ⟨(0 : E), R + 1, ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx.2
  have hV_cover : K ⊆ ⋃ i, V i := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    have hxR : dist x (0 : E) ≤ R := by
      simpa [dist_comm] using Metric.mem_closedBall.mp (hR hx)
    have hxball : x ∈ Metric.ball (0 : E) (R + 1) := by
      rw [Metric.mem_ball]
      linarith
    exact Set.mem_iUnion.mpr ⟨i, ⟨hxi, hxball⟩⟩
  obtain ⟨χ, hχ_compact, hχ_sub, hχ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      (E := E) hK hV_open hV_relcompact hV_cover
  refine ⟨χ, hχ_compact, ?_, hχ_sum⟩
  intro i
  exact (hχ_sub i).trans Set.inter_subset_left

/-- Finite-cover assembly for the canonical forward-shell difference limit.

If the compact support of `f` is covered by finitely many identity real
patches carrying Figure-2-4 Wick-pairing packets, a partition of unity reduces
the canonical-shell branch-difference limit to the one-patch theorem.  This is
the compact boundary-limit form consumed by the final boundary-value transfer;
it keeps the support collar explicit instead of replacing it by a finite-height
equality. -/
theorem canonicalShell_difference_tendsto_zero_of_finite_compactFigure24Patch_cover
    {α : Type*} [Fintype α]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hCompact : α → BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc)
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        ⋃ a : α, (hCompact a).realPatch 1) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * g x) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  classical
  intro τ eτ g
  obtain ⟨χ, _hχ_compact, hχ_sub, hχ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := NPointDomain d n)
      (K := tsupport (f : NPointDomain d n → ℂ))
      hf_compact.isCompact
      (fun a => (hCompact a).realPatch_open 1)
      hcover
  let piece : α → SchwartzNPoint d n := fun a =>
    SchwartzMap.smulLeftCLM ℂ (χ a : NPointDomain d n → ℂ) f
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ
  have hpiece_compact :
      ∀ a, HasCompactSupport (piece a : NPointDomain d n → ℂ) := by
    intro a
    refine hf_compact.mono' ?_
    intro x hx
    have hx_ts : x ∈ tsupport (piece a : NPointDomain d n → ℂ) :=
      subset_closure hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (χ a : NPointDomain d n → ℂ))
        (f := f)) hx_ts).1
  have hpiece_patch :
      ∀ a, tsupport (piece a : NPointDomain d n → ℂ) ⊆
        (hCompact a).realPatch 1 := by
    intro a x hx
    exact
      hχ_sub a
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (χ a : NPointDomain d n → ℂ))
          (f := f)) hx).2
  have hf_sum : f = ∑ a, piece a := by
    simpa [piece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) χ f
        (by
          intro x hx
          simpa using hχ_sum x hx)
  have hg_sum : g = ∑ a, P (piece a) := by
    simpa [g, P] using congrArg P hf_sum
  have hPpiece_compact :
      ∀ a, HasCompactSupport ((P (piece a)) : NPointDomain d n → ℂ) := by
    intro a
    simpa [P, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (hpiece_compact a).comp_homeomorph eτ.toHomeomorph
  have hpiece_tendsto :
      ∀ a,
        Filter.Tendsto
          (fun ε : ℝ =>
            (∫ x : NPointDomain d n,
                bvt_F OS lgc n (fun k μ =>
                  (x k μ : ℂ) +
                    ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                      Complex.I) * (P (piece a)) x) -
              ∫ x : NPointDomain d n,
                bvt_F OS lgc n (fun k μ =>
                  (x k μ : ℂ) +
                    ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                      Complex.I) * (piece a) x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
    intro a
    simpa [P, τ, eτ] using
      BHW.canonicalShell_difference_tendsto_zero_of_compactFigure24Patch
        (d := d) OS lgc n i hi (hCompact a) (piece a)
        (hpiece_compact a) (hpiece_patch a)
  let I : ℝ → SchwartzNPoint d n → ℂ := fun ε ψ =>
    ∫ x : NPointDomain d n,
      bvt_F OS lgc n (fun k μ =>
        (x k μ : ℂ) +
          ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
            Complex.I) * ψ x
  let diff : α → ℝ → ℂ := fun a ε => I ε (P (piece a)) - I ε (piece a)
  have hsum_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => ∑ a, diff a ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [diff, I] using
      tendsto_finset_sum (s := Finset.univ)
        (fun a _ha => hpiece_tendsto a)
  refine Filter.Tendsto.congr' ?_ hsum_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let H : NPointDomain d n → ℂ := fun x =>
    bvt_F OS lgc n (fun k μ =>
      (x k μ : ℂ) +
        ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
          Complex.I)
  have harg_cont : Continuous
      (fun x : NPointDomain d n =>
        fun k μ =>
          (x k μ : ℂ) +
            ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
              Complex.I) := by
    fun_prop
  have harg_mem :
      ∀ x : NPointDomain d n,
        (fun k μ =>
          (x k μ : ℂ) +
            ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
              Complex.I) ∈ ForwardTube d n := by
    intro x
    exact shell_mem_forwardTube_of_inForwardCone
      (d := d) (canonicalForwardConeDirection (d := d) n)
      (canonicalForwardConeDirection_mem (d := d) n)
      x ε (Set.mem_Ioi.mp hε)
  have hH_cont : ContinuousOn H Set.univ := by
    refine (bvt_F_holomorphic OS lgc n).continuousOn.comp
      harg_cont.continuousOn ?_
    intro x _hx
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using harg_mem x
  have hIntP :
      ∀ a ∈ (Finset.univ : Finset α),
        Integrable (fun x : NPointDomain d n => H x * (P (piece a)) x) := by
    intro a _ha
    exact
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
        (H := H) (ψ := P (piece a)) (U := Set.univ)
        isOpen_univ hH_cont ⟨hPpiece_compact a, by intro x hx; trivial⟩
  have hIntPiece :
      ∀ a ∈ (Finset.univ : Finset α),
        Integrable (fun x : NPointDomain d n => H x * (piece a) x) := by
    intro a _ha
    exact
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
        (H := H) (ψ := piece a) (U := Set.univ)
        isOpen_univ hH_cont ⟨hpiece_compact a, by intro x hx; trivial⟩
  simp only [diff, I]
  rw [hf_sum, hg_sum]
  change
    (∑ a,
        ((∫ x : NPointDomain d n, H x * (P (piece a)) x) -
          ∫ x : NPointDomain d n, H x * (piece a) x)) =
      (∫ x : NPointDomain d n,
          H x * ((∑ a, P (piece a) : SchwartzNPoint d n) x)) -
        ∫ x : NPointDomain d n,
          H x * ((∑ a, piece a : SchwartzNPoint d n) x)
  have hmulP :
      (fun x : NPointDomain d n =>
          H x * ((∑ a, P (piece a) : SchwartzNPoint d n) x)) =
        fun x : NPointDomain d n => ∑ a, H x * (P (piece a)) x := by
    funext x
    simp [Finset.mul_sum]
  have hmulPiece :
      (fun x : NPointDomain d n =>
          H x * ((∑ a, piece a : SchwartzNPoint d n) x)) =
        fun x : NPointDomain d n => ∑ a, H x * (piece a) x := by
    funext x
    simp [Finset.mul_sum]
  rw [hmulP, hmulPiece]
  rw [integral_finset_sum (s := Finset.univ) hIntP,
    integral_finset_sum (s := Finset.univ) hIntPiece]
  simp [Finset.sum_sub_distrib]

/-- A local adjacent EOW branch-difference envelope supplies the canonical
forward-shell difference limit for compact tests supported in the real slice
`V`.

This is the identity-patch version of the compact Figure-2-4 consumer: for the
boundary-value transport step, the identity real slice, its adjacent swapped
extended-tube membership, and the adjacent real-edge equality are enough. -/
theorem canonicalShell_difference_tendsto_zero_of_adjacentEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_left_ET :
      ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_right_ET :
      ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
    (E : BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) V)
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_tsupport : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * g x) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              (x k μ : ℂ) +
                ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                  Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  classical
  intro τ eτ g
  have hF_holo_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv_BHW :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ) := by
    simpa [g, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hf_compact.comp_homeomorph eτ.toHomeomorph
  have hf_ET :
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    exact hV_left_ET x (hf_tsupport hx)
  have hg_tsupport :
      tsupport (g : NPointDomain d n → ℂ) =
        eτ.toHomeomorph ⁻¹' tsupport (f : NPointDomain d n → ℂ) := by
    simpa [g, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage
        (g := (f : NPointDomain d n → ℂ)) eτ.toHomeomorph)
  have hg_ET :
      ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
        BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    have hxτ : (fun k => x (τ k)) ∈ tsupport (f : NPointDomain d n → ℂ) := by
      simpa [hg_tsupport, eτ] using hx
    have hxV : (fun k => x (τ k)) ∈ V := hf_tsupport hxτ
    have hxright := hV_right_ET (fun k => x (τ k)) hxV
    convert hxright using 1
    ext k μ
    simp [BHW.realEmbed, τ]
  have hleft_g_eq_right_f :
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * g x) =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (τ k))) * f x := by
    let H : NPointDomain d n → ℂ := fun x =>
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k))) * f x
    have hperm := local_integral_perm_eq_self (d := d) τ H
    calc
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * g x)
          = ∫ x : NPointDomain d n, H (fun k => x (τ k)) := by
              congr 1
              ext x
              have hxperm :
                  BHW.realEmbed (fun k => (fun j => x (τ j)) (τ k)) =
                    BHW.realEmbed x := by
                ext k μ
                simp [BHW.realEmbed, τ]
              simp [H, g, eτ, hxperm]
      _ = ∫ x : NPointDomain d n, H x := hperm
      _ = ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (τ k))) * f x := rfl
  have hpatch_eq :
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * f x) =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (τ k))) * f x := by
    have h :=
      BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope
        (d := d) OS lgc n i hi V hV_open hV_nonempty E
        f hf_compact hf_tsupport
    simpa [τ] using h.symm
  have hreal_eq :
      (∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * g x) =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * f x :=
    hleft_g_eq_right_f.trans hpatch_eq.symm
  exact
    BHW.canonicalShell_difference_tendsto_zero_of_extendF_pairing_eq
      (d := d) (n := n) (bvt_F OS lgc n)
      hF_holo_BHW hF_cinv_BHW f g hf_compact hg_compact hf_ET hg_ET hreal_eq

/-- Local Wightman adjacent equality from a compact Figure-2-4 packet.

This closes the local Stage-E consumer for tests supported in one identity
Figure-2-4 real patch: the packet gives real-edge equality, the previous
theorem transports it to the canonical shell, and the standard boundary values
identify the two Wightman distribution pairings. -/
theorem bvt_W_eq_swapped_of_compactFigure24Patch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hCompact : BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc)
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_tsupport :
      tsupport (f : NPointDomain d n → ℂ) ⊆ hCompact.realPatch 1) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  intro τ eτ g
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf_bv := bvt_boundary_values (d := d) OS lgc n f η hη
  have hg_bv := bvt_boundary_values (d := d) OS lgc n g η hη
  have hdiff_limit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * g x) -
            ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n g - bvt_W OS lgc n f)) :=
    hg_bv.sub hf_bv
  have hdiff_zero :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * g x) -
            ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [η, τ, eτ, g] using
      BHW.canonicalShell_difference_tendsto_zero_of_compactFigure24Patch
        (d := d) OS lgc n i hi hCompact f hf_compact hf_tsupport
  have hzero : bvt_W OS lgc n g - bvt_W OS lgc n f = 0 :=
    tendsto_nhds_unique hdiff_limit hdiff_zero
  exact (sub_eq_zero.mp hzero).symm

/-- Local Wightman adjacent equality from a local adjacent EOW envelope. -/
theorem bvt_W_eq_swapped_of_adjacentEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_left_ET :
      ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_right_ET :
      ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
    (E : BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) V)
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_tsupport : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  intro τ eτ g
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf_bv := bvt_boundary_values (d := d) OS lgc n f η hη
  have hg_bv := bvt_boundary_values (d := d) OS lgc n g η hη
  have hdiff_limit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * g x) -
            ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n g - bvt_W OS lgc n f)) :=
    hg_bv.sub hf_bv
  have hdiff_zero :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * g x) -
            ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [η, τ, eτ, g] using
      BHW.canonicalShell_difference_tendsto_zero_of_adjacentEnvelope
        (d := d) OS lgc n i hi V hV_open hV_nonempty
        hV_left_ET hV_right_ET E f hf_compact hf_tsupport
  have hzero : bvt_W OS lgc n g - bvt_W OS lgc n f = 0 :=
    tendsto_nhds_unique hdiff_limit hdiff_zero
  exact (sub_eq_zero.mp hzero).symm

/-- Finite-cover assembly for the local Figure-2-4 compact packets.

If the compact support of `f` is covered by finitely many identity real
patches, partition `f` subordinate to those patches, apply the local compact
packet comparison to each piece, and re-sum with linearity of the reconstructed
Wightman functional. -/
theorem bvt_W_eq_swapped_of_finite_compactFigure24Patch_cover
    {α : Type*} [Fintype α]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hCompact : α → BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc)
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        ⋃ a : α, (hCompact a).realPatch 1) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  intro τ eτ g
  obtain ⟨χ, _hχ_compact, hχ_sub, hχ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := NPointDomain d n)
      (K := tsupport (f : NPointDomain d n → ℂ))
      hf_compact.isCompact
      (fun a => (hCompact a).realPatch_open 1)
      hcover
  let piece : α → SchwartzNPoint d n := fun a =>
    SchwartzMap.smulLeftCLM ℂ (χ a : NPointDomain d n → ℂ) f
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ
  have hpiece_compact :
      ∀ a, HasCompactSupport (piece a : NPointDomain d n → ℂ) := by
    intro a
    refine hf_compact.mono' ?_
    intro x hx
    have hx_ts : x ∈ tsupport (piece a : NPointDomain d n → ℂ) :=
      subset_closure hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (χ a : NPointDomain d n → ℂ))
        (f := f)) hx_ts).1
  have hpiece_patch :
      ∀ a, tsupport (piece a : NPointDomain d n → ℂ) ⊆
        (hCompact a).realPatch 1 := by
    intro a x hx
    exact
      hχ_sub a
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (χ a : NPointDomain d n → ℂ))
          (f := f)) hx).2
  have hf_sum : f = ∑ a, piece a := by
    simpa [piece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) χ f
        (by
          intro x hx
          simpa using hχ_sum x hx)
  have hg_sum : g = ∑ a, P (piece a) := by
    simpa [g, P] using congrArg P hf_sum
  have hpiece_eq :
      ∀ a, bvt_W OS lgc n (piece a) = bvt_W OS lgc n (P (piece a)) := by
    intro a
    simpa [P, τ, eτ] using
      BHW.bvt_W_eq_swapped_of_compactFigure24Patch
        (d := d) OS lgc n i hi (hCompact a) (piece a)
        (hpiece_compact a) (hpiece_patch a)
  have hW_f_sum :
      bvt_W OS lgc n f = ∑ a, bvt_W OS lgc n (piece a) := by
    rw [hf_sum]
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty =>
        simp [(bvt_W_linear (d := d) OS lgc n).map_zero]
    | insert a s has ih =>
        rw [Finset.sum_insert has, Finset.sum_insert has]
        rw [(bvt_W_linear (d := d) OS lgc n).map_add, ih]
  have hW_g_sum :
      bvt_W OS lgc n g = ∑ a, bvt_W OS lgc n (P (piece a)) := by
    rw [hg_sum]
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty =>
        simp [(bvt_W_linear (d := d) OS lgc n).map_zero]
    | insert a s has ih =>
        rw [Finset.sum_insert has, Finset.sum_insert has]
        rw [(bvt_W_linear (d := d) OS lgc n).map_add, ih]
  calc
    bvt_W OS lgc n f = ∑ a, bvt_W OS lgc n (piece a) := hW_f_sum
    _ = ∑ a, bvt_W OS lgc n (P (piece a)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact hpiece_eq a
    _ = bvt_W OS lgc n g := hW_g_sum.symm

/-- Finite-cover assembly for local adjacent EOW envelopes.

This is the compact partition-of-unity assembly for the smaller local
boundary-value datum: each member of the finite cover supplies an
`AdjacentOSEOWDifferenceEnvelope` and left/right extended-tube membership, and
the local envelope equality is applied to the subordinate test piece. -/
theorem bvt_W_eq_swapped_of_finite_adjacentEnvelope_cover
    {α : Type*} [Fintype α]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : α → Set (NPointDomain d n))
    (hV_open : ∀ a, IsOpen (V a))
    (hV_nonempty : ∀ a, (V a).Nonempty)
    (hV_left_ET :
      ∀ a x, x ∈ V a → BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_right_ET :
      ∀ a x, x ∈ V a →
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
    (E : ∀ a, BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) (V a))
    (f : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆ ⋃ a : α, V a) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let g : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  intro τ eτ g
  obtain ⟨χ, _hχ_compact, hχ_sub, hχ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := NPointDomain d n)
      (K := tsupport (f : NPointDomain d n → ℂ))
      hf_compact.isCompact
      hV_open
      hcover
  let piece : α → SchwartzNPoint d n := fun a =>
    SchwartzMap.smulLeftCLM ℂ (χ a : NPointDomain d n → ℂ) f
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ
  have hpiece_compact :
      ∀ a, HasCompactSupport (piece a : NPointDomain d n → ℂ) := by
    intro a
    refine hf_compact.mono' ?_
    intro x hx
    have hx_ts : x ∈ tsupport (piece a : NPointDomain d n → ℂ) :=
      subset_closure hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (χ a : NPointDomain d n → ℂ))
        (f := f)) hx_ts).1
  have hpiece_patch :
      ∀ a, tsupport (piece a : NPointDomain d n → ℂ) ⊆ V a := by
    intro a x hx
    exact
      hχ_sub a
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (χ a : NPointDomain d n → ℂ))
          (f := f)) hx).2
  have hf_sum : f = ∑ a, piece a := by
    simpa [piece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) χ f
        (by
          intro x hx
          simpa using hχ_sum x hx)
  have hg_sum : g = ∑ a, P (piece a) := by
    simpa [g, P] using congrArg P hf_sum
  have hpiece_eq :
      ∀ a, bvt_W OS lgc n (piece a) = bvt_W OS lgc n (P (piece a)) := by
    intro a
    simpa [P, τ, eτ] using
      BHW.bvt_W_eq_swapped_of_adjacentEnvelope
        (d := d) OS lgc n i hi (V a) (hV_open a) (hV_nonempty a)
        (hV_left_ET a) (hV_right_ET a) (E a) (piece a)
        (hpiece_compact a) (hpiece_patch a)
  have hW_f_sum :
      bvt_W OS lgc n f = ∑ a, bvt_W OS lgc n (piece a) := by
    rw [hf_sum]
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty =>
        simp [(bvt_W_linear (d := d) OS lgc n).map_zero]
    | insert a s has ih =>
        rw [Finset.sum_insert has, Finset.sum_insert has]
        rw [(bvt_W_linear (d := d) OS lgc n).map_add, ih]
  have hW_g_sum :
      bvt_W OS lgc n g = ∑ a, bvt_W OS lgc n (P (piece a)) := by
    rw [hg_sum]
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty =>
        simp [(bvt_W_linear (d := d) OS lgc n).map_zero]
    | insert a s has ih =>
        rw [Finset.sum_insert has, Finset.sum_insert has]
        rw [(bvt_W_linear (d := d) OS lgc n).map_add, ih]
  calc
    bvt_W OS lgc n f = ∑ a, bvt_W OS lgc n (piece a) := hW_f_sum
    _ = ∑ a, bvt_W OS lgc n (P (piece a)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact hpiece_eq a
    _ = bvt_W OS lgc n g := hW_g_sum.symm

/-- Finite-cover assembly, with the swapped test supplied in the standard
pointwise form used by Wightman locality. -/
theorem bvt_W_eq_of_finite_compactFigure24Patch_cover
    {α : Type*} [Fintype α]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hCompact : α → BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        ⋃ a : α, (hCompact a).realPatch 1)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
  let g0 : SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
  have hlocal : bvt_W OS lgc n f = bvt_W OS lgc n g0 := by
    simpa [τ, eτ, g0] using
      BHW.bvt_W_eq_swapped_of_finite_compactFigure24Patch_cover
        (d := d) OS lgc n i hi hCompact f hf_compact hcover
  have hg0 : g0 = g := by
    ext x
    change f (fun k => x (τ k)) = g x
    simpa [τ] using (hswap x).symm
  simpa [hg0] using hlocal

/-- Finite adjacent-envelope cover assembly, with the swapped test supplied in
the standard pointwise form used by Wightman locality. -/
theorem bvt_W_eq_of_finite_adjacentEnvelope_cover
    {α : Type*} [Fintype α]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : α → Set (NPointDomain d n))
    (hV_open : ∀ a, IsOpen (V a))
    (hV_nonempty : ∀ a, (V a).Nonempty)
    (hV_left_ET :
      ∀ a x, x ∈ V a → BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_right_ET :
      ∀ a x, x ∈ V a →
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
    (E : ∀ a, BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) (V a))
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆ ⋃ a : α, V a)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
  let g0 : SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ f
  have hlocal : bvt_W OS lgc n f = bvt_W OS lgc n g0 := by
    simpa [τ, eτ, g0] using
      BHW.bvt_W_eq_swapped_of_finite_adjacentEnvelope_cover
        (d := d) OS lgc n i hi V hV_open hV_nonempty
        hV_left_ET hV_right_ET E f hf_compact hcover
  have hg0 : g0 = g := by
    ext x
    change f (fun k => x (τ k)) = g x
    simpa [τ] using (hswap x).symm
  simpa [hg0] using hlocal

/-- Compact-test adjacent locality from pointwise local adjacent EOW envelopes
along the topological support.

If every support point has an open real slice carrying left/right
extended-tube membership and an adjacent EOW difference envelope, compactness
extracts a finite cover consumed by
`bvt_W_eq_of_finite_adjacentEnvelope_cover`. -/
theorem bvt_W_eq_of_adjacentEnvelope_at_tsupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hEnvelopeAt :
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        ∃ V : Set (NPointDomain d n),
          IsOpen V ∧
          V.Nonempty ∧
          x ∈ V ∧
          (∀ y ∈ V, BHW.realEmbed y ∈ BHW.ExtendedTube d n) ∧
          (∀ y ∈ V,
            BHW.realEmbed
              (fun k => y (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
              BHW.ExtendedTube d n) ∧
          Nonempty
            (BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
              (Equiv.swap i ⟨i.val + 1, hi⟩) V))
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let K : Set (NPointDomain d n) := tsupport (f : NPointDomain d n → ℂ)
  let β := {x : NPointDomain d n // x ∈ K}
  let Vβ : β → Set (NPointDomain d n) :=
    fun a => Classical.choose (hEnvelopeAt a a.property)
  have hVβ_spec :
      ∀ a : β,
        IsOpen (Vβ a) ∧
        (Vβ a).Nonempty ∧
        (a : NPointDomain d n) ∈ Vβ a ∧
        (∀ y ∈ Vβ a, BHW.realEmbed y ∈ BHW.ExtendedTube d n) ∧
        (∀ y ∈ Vβ a,
          BHW.realEmbed
            (fun k => y (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        Nonempty
          (BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
            (Equiv.swap i ⟨i.val + 1, hi⟩) (Vβ a)) := by
    intro a
    exact Classical.choose_spec (hEnvelopeAt a a.property)
  have hK_cover : K ⊆ ⋃ a : β, Vβ a := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact (hVβ_spec ⟨x, hx⟩).2.2.1
  obtain ⟨t, htcover⟩ :=
    hf_compact.isCompact.elim_finite_subcover Vβ
      (fun a => (hVβ_spec a).1) hK_cover
  let α := {a : β // a ∈ t}
  let Vα : α → Set (NPointDomain d n) := fun a => Vβ a.1
  have hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆ ⋃ a : α, Vα a := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (htcover (by simpa [K] using hx)) with
      ⟨a, hat, hxa⟩
    exact Set.mem_iUnion.mpr ⟨⟨a, hat⟩, hxa⟩
  exact
    BHW.bvt_W_eq_of_finite_adjacentEnvelope_cover
      (d := d) (α := α) OS lgc n i hi Vα
      (fun a => (hVβ_spec a.1).1)
      (fun a => (hVβ_spec a.1).2.1)
      (fun a => (hVβ_spec a.1).2.2.2.1)
      (fun a => (hVβ_spec a.1).2.2.2.2.1)
      (fun a => Classical.choice ((hVβ_spec a.1).2.2.2.2.2))
      f g hf_compact hcover hswap

/-- Strict `tsupport` adjacent locality from pointwise local adjacent EOW
envelopes on an open region.

This is the support-boundary lane after the compact consumer: if the
topological support of `f` is already inside a region where every point has a
local adjacent envelope, radial compact approximants preserve that inclusion
and continuity of `bvt_W` passes the compact result to `f`. -/
theorem bvt_W_adjacent_swap_of_strict_adjacentEnvelope_provider
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    {U : Set (NPointDomain d n)}
    (hEnvelopeOn :
      ∀ x ∈ U,
        ∃ V : Set (NPointDomain d n),
          IsOpen V ∧
          V.Nonempty ∧
          x ∈ V ∧
          (∀ y ∈ V, BHW.realEmbed y ∈ BHW.ExtendedTube d n) ∧
          (∀ y ∈ V,
            BHW.realEmbed
              (fun k => y (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
              BHW.ExtendedTube d n) ∧
          Nonempty
            (BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
              (Equiv.swap i ⟨i.val + 1, hi⟩) V))
    (f g : SchwartzNPoint d n)
    (hf_tsupport : tsupport (f : NPointDomain d n → ℂ) ⊆ U)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  obtain ⟨fN, hfN_compact, hfN_tsupport, hfN_tendsto⟩ :=
    exists_compactSupportApprox_tsupport_subset_npoint
      (d := d) f hf_tsupport
  let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ
  let gN : ℕ → SchwartzNPoint d n := fun N => P (fN N)
  have hcompact_eq :
      ∀ N, bvt_W OS lgc n (fN N) = bvt_W OS lgc n (gN N) := by
    intro N
    have hswapN :
        ∀ x : NPointDomain d n,
          (gN N).toFun x =
            (fN N).toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
      intro x
      change P (fN N) x = (fN N).toFun (fun k => x (τ k))
      rfl
    exact
      BHW.bvt_W_eq_of_adjacentEnvelope_at_tsupport
        (d := d) OS lgc n i hi (fN N) (gN N)
        (hfN_compact N)
        (fun x hx => hEnvelopeOn x (hfN_tsupport N hx))
        hswapN
  have hleft :
      Filter.Tendsto (fun N => bvt_W OS lgc n (fN N))
        Filter.atTop (nhds (bvt_W OS lgc n f)) :=
    ((bvt_W_continuous (d := d) OS lgc n).tendsto f).comp hfN_tendsto
  have hP_tendsto :
      Filter.Tendsto (fun N => P (fN N)) Filter.atTop (nhds (P f)) :=
    (P.continuous.tendsto f).comp hfN_tendsto
  have hP_f : P f = g := by
    ext x
    change f (fun k => x (τ k)) = g x
    simpa [τ] using (hswap x).symm
  have hgN_tendsto :
      Filter.Tendsto gN Filter.atTop (nhds g) := by
    simpa [gN, hP_f] using hP_tendsto
  have hright :
      Filter.Tendsto (fun N => bvt_W OS lgc n (gN N))
        Filter.atTop (nhds (bvt_W OS lgc n g)) :=
    ((bvt_W_continuous (d := d) OS lgc n).tendsto g).comp hgN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => bvt_W OS lgc n (fN N))
        Filter.atTop (nhds (bvt_W OS lgc n g)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N => (hcompact_eq N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right

/-- Compact-test adjacent locality from pointwise local Figure-2-4 packets
along the topological support.

If each point of the compact support has a local
`OS45CompactFigure24WickPairingEq` packet whose identity real patch contains
that point, compactness extracts the finite packet family consumed by
`bvt_W_eq_of_finite_compactFigure24Patch_cover`. -/
theorem bvt_W_eq_of_compactFigure24Patch_at_tsupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hPatchAt :
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        ∃ P : BHW.OS45CompactFigure24WickPairingEq
            (d := d) n i hi OS lgc,
          x ∈ P.realPatch 1)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let K : Set (NPointDomain d n) := tsupport (f : NPointDomain d n → ℂ)
  let β := {x : NPointDomain d n // x ∈ K}
  let hCompactβ : β → BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
    fun a => Classical.choose (hPatchAt a a.property)
  let Uβ : β → Set (NPointDomain d n) := fun a => (hCompactβ a).realPatch 1
  have hUβ_open : ∀ a : β, IsOpen (Uβ a) := by
    intro a
    exact (hCompactβ a).realPatch_open 1
  have hK_cover : K ⊆ ⋃ a : β, Uβ a := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact Classical.choose_spec (hPatchAt x hx)
  obtain ⟨t, htcover⟩ :=
    hf_compact.isCompact.elim_finite_subcover Uβ hUβ_open hK_cover
  let α := {a : β // a ∈ t}
  let hCompact : α → BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc := fun a => hCompactβ a.1
  have hcover :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        ⋃ a : α, (hCompact a).realPatch 1 := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (htcover (by simpa [K] using hx)) with
      ⟨a, hat, hxa⟩
    exact Set.mem_iUnion.mpr ⟨⟨a, hat⟩, hxa⟩
  exact
    BHW.bvt_W_eq_of_finite_compactFigure24Patch_cover
      (d := d) (α := α) OS lgc n i hi hCompact f g hf_compact hcover hswap

omit [NeZero d] in
/-- The adjacent-spacelike condition is open on real `n`-point configurations. -/
theorem isOpen_adjacentSpacelikeSet
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen
      {x : NPointDomain d n |
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)} := by
  have hquad : Continuous
      (fun x : NPointDomain d n =>
        MinkowskiSpace.minkowskiNormSq d
          (x i - x ⟨i.val + 1, hi⟩)) := by
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    fun_prop
  simpa [MinkowskiSpace.AreSpacelikeSeparated, MinkowskiSpace.IsSpacelike]
    using isOpen_lt continuous_const hquad

/-- Compact adjacent locality from local Figure-2-4 packets at every point of
an open set containing the topological support.

This is the strict-support compact consumer.  It separates the genuine
pointwise OS45/Jost packet construction from the later support-boundary
approximation needed when the nonzero support only lies in the spacelike set. -/
theorem bvt_W_eq_of_open_local_compactFigure24Packet_provider
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    {U : Set (NPointDomain d n)}
    (hPatchOn :
      ∀ x ∈ U,
        ∃ P : BHW.OS45CompactFigure24WickPairingEq
            (d := d) n i hi OS lgc,
          x ∈ P.realPatch 1)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_tsupport : tsupport (f : NPointDomain d n → ℂ) ⊆ U)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  exact
    BHW.bvt_W_eq_of_compactFigure24Patch_at_tsupport
      (d := d) OS lgc n i hi f g hf_compact
      (fun x hx => hPatchOn x (hf_tsupport hx))
      hswap

/-- Strict adjacent-spacelike compact-support consumer.

The remaining non-wrapper input is pointwise and geometric: every real
adjacent-spacelike configuration must carry a local
`OS45CompactFigure24WickPairingEq` packet whose identity real patch contains
that configuration. -/
theorem bvt_W_eq_of_adjacentSpacelike_local_compactFigure24Packet_provider
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (hPatchAtSpacelike :
      ∀ x : NPointDomain d n,
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩) →
        ∃ P : BHW.OS45CompactFigure24WickPairingEq
            (d := d) n i hi OS lgc,
          x ∈ P.realPatch 1)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_tsupport :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x | MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)})
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  exact
    BHW.bvt_W_eq_of_open_local_compactFigure24Packet_provider
      (d := d) OS lgc i hi
      (fun x hx => hPatchAtSpacelike x hx)
      f g hf_compact hf_tsupport hswap

/-- Strict adjacent-spacelike all-Schwartz consumer from pointwise local
Figure-2-4 packets.

This is the support-boundary density step after the compact packet consumer:
compact approximants keep their topological support in the spacelike open set,
so compact Figure-2-4 locality passes to the original Schwartz test by
continuity of `bvt_W`. -/
theorem bvt_W_adjacent_swap_of_strict_local_compactFigure24Packet_provider
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (hPatchAtSpacelike :
      ∀ x : NPointDomain d n,
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩) →
        ∃ P : BHW.OS45CompactFigure24WickPairingEq
            (d := d) n i hi OS lgc,
          x ∈ P.realPatch 1)
    (f g : SchwartzNPoint d n)
    (hf_tsupport :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x | MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)})
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  obtain ⟨fN, hfN_compact, hfN_tsupport, hfN_tendsto⟩ :=
    exists_compactSupportApprox_tsupport_subset_npoint
      (d := d) f hf_tsupport
  let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ
  let gN : ℕ → SchwartzNPoint d n := fun N => P (fN N)
  have hcompact_eq :
      ∀ N, bvt_W OS lgc n (fN N) = bvt_W OS lgc n (gN N) := by
    intro N
    have hswapN :
        ∀ x : NPointDomain d n,
          (gN N).toFun x =
            (fN N).toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
      intro x
      change P (fN N) x = (fN N).toFun (fun k => x (τ k))
      rfl
    exact
      BHW.bvt_W_eq_of_adjacentSpacelike_local_compactFigure24Packet_provider
        (d := d) OS lgc i hi hPatchAtSpacelike
        (fN N) (gN N) (hfN_compact N) (hfN_tsupport N) hswapN
  have hleft :
      Filter.Tendsto (fun N => bvt_W OS lgc n (fN N))
        Filter.atTop (nhds (bvt_W OS lgc n f)) :=
    ((bvt_W_continuous (d := d) OS lgc n).tendsto f).comp hfN_tendsto
  have hP_tendsto :
      Filter.Tendsto (fun N => P (fN N)) Filter.atTop (nhds (P f)) :=
    (P.continuous.tendsto f).comp hfN_tendsto
  have hP_f : P f = g := by
    ext x
    change f (fun k => x (τ k)) = g x
    simpa [τ] using (hswap x).symm
  have hgN_tendsto :
      Filter.Tendsto gN Filter.atTop (nhds g) := by
    simpa [gN, hP_f] using hP_tendsto
  have hright :
      Filter.Tendsto (fun N => bvt_W OS lgc n (gN N))
        Filter.atTop (nhds (bvt_W OS lgc n g)) :=
    ((bvt_W_continuous (d := d) OS lgc n).tendsto g).comp hgN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => bvt_W OS lgc n (fN N))
        Filter.atTop (nhds (bvt_W OS lgc n g)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N => (hcompact_eq N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right

/-- Adjacent boundary locality from a compact Figure-2-4 patch-cover
provider.

The finite-cover theorem above handles one compact cover.  This theorem adds
the final density step for arbitrary Schwartz tests, leaving the remaining
OS-I/Jost producer in its concrete form: compact adjacent-spacelike supports
must have a finite cover by identity real patches carrying
`OS45CompactFigure24WickPairingEq`. -/
theorem bvt_W_adjacent_swap_of_compactFigure24Patch_cover_provider
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hCover :
      ∀ f : SchwartzNPoint d n,
        HasCompactSupport (f : NPointDomain d n → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d
            (x i) (x ⟨i.val + 1, hi⟩)) →
        ∃ (α : Type) (_ : Fintype α),
          ∃ hCompact : α → BHW.OS45CompactFigure24WickPairingEq
              (d := d) n i hi OS lgc,
            tsupport (f : NPointDomain d n → ℂ) ⊆
              ⋃ a : α, (hCompact a).realPatch 1) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  intro f g hsp hswap
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let U : Set (NPointDomain d n) :=
    {x | MinkowskiSpace.AreSpacelikeSeparated d
      (x i) (x ⟨i.val + 1, hi⟩)}
  have hf_zero : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    by_contra hfx
    exact hxU (hsp x hfx)
  obtain ⟨fN, hfN_compact, hfN_zero, hfN_tendsto⟩ :=
    exists_compactSupportApprox_zeroOff_npoint (d := d) U f hf_zero
  let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ
  let gN : ℕ → SchwartzNPoint d n := fun N => P (fN N)
  have hcompact_eq :
      ∀ N, bvt_W OS lgc n (fN N) = bvt_W OS lgc n (gN N) := by
    intro N
    have hspN :
        ∀ x, (fN N).toFun x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d
            (x i) (x ⟨i.val + 1, hi⟩) := by
      intro x hfx
      by_contra hxU
      exact hfx (hfN_zero N x hxU)
    obtain ⟨α, hα, hCompact, hcover⟩ :=
      hCover (fN N) (hfN_compact N) hspN
    letI : Fintype α := hα
    have hswapN :
        ∀ x : NPointDomain d n,
          (gN N).toFun x =
            (fN N).toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
      intro x
      change P (fN N) x = (fN N).toFun (fun k => x (τ k))
      rfl
    exact
      BHW.bvt_W_eq_of_finite_compactFigure24Patch_cover
        (d := d) (α := α) OS lgc n i hi hCompact
        (fN N) (gN N) (hfN_compact N) hcover hswapN
  have hleft :
      Filter.Tendsto (fun N => bvt_W OS lgc n (fN N))
        Filter.atTop (nhds (bvt_W OS lgc n f)) :=
    ((bvt_W_continuous (d := d) OS lgc n).tendsto f).comp hfN_tendsto
  have hP_tendsto :
      Filter.Tendsto (fun N => P (fN N)) Filter.atTop (nhds (P f)) :=
    (P.continuous.tendsto f).comp hfN_tendsto
  have hP_f : P f = g := by
    ext x
    change f (fun k => x (τ k)) = g x
    simpa [τ] using (hswap x).symm
  have hgN_tendsto :
      Filter.Tendsto gN Filter.atTop (nhds g) := by
    simpa [gN, hP_f] using hP_tendsto
  have hright :
      Filter.Tendsto (fun N => bvt_W OS lgc n (gN N))
        Filter.atTop (nhds (bvt_W OS lgc n g)) :=
    ((bvt_W_continuous (d := d) OS lgc n).tendsto g).comp hgN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => bvt_W OS lgc n (fN N))
        Filter.atTop (nhds (bvt_W OS lgc n g)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N => (hcompact_eq N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right

end BHW
