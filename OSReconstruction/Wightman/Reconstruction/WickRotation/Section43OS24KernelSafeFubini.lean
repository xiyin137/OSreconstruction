import Mathlib.Topology.UrysohnsLemma
import OSReconstruction.SCV.PaleyWienerCompact
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OS24KernelFubini

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

private theorem isOpen_TubeDomainSetPi_forwardConeAbs
    (d N : ℕ) [NeZero d] :
    IsOpen (TubeDomainSetPi (ForwardConeAbs d N)) := by
  simpa [TubeDomainSetPi] using
    (forwardConeAbs_isOpen d N).preimage
      (by
        apply continuous_pi
        intro k
        apply continuous_pi
        intro μ
        exact Complex.continuous_im.comp
          ((continuous_apply μ).comp (continuous_apply k)))

/-- Urysohn cutoff for the support-localized forward-tube Fubini packet.

The cutoff is `1` on the topological support of the OS tensor product and has
ordinary support contained in the open set where the forward-tube lift is known
to be tube-valued. -/
theorem exists_section43OSForwardTubeCutoff_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    {t : ℝ} (ht : 0 < t) :
    ∃ ρ : NPointDomain d (n + (m + 1)) → ℝ,
      Continuous ρ ∧
      HasCompactSupport ρ ∧
      (∀ y, ρ y ∈ Icc (0 : ℝ) 1) ∧
      EqOn ρ 1
        (tsupport
          ((f.1.osConjTensorProduct g.1) :
            NPointDomain d (n + (m + 1)) → ℂ)) ∧
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))} := by
  let Kfg : Set (NPointDomain d (n + (m + 1))) :=
    tsupport
      ((f.1.osConjTensorProduct g.1) :
        NPointDomain d (n + (m + 1)) → ℂ)
  let Ufg : Set (NPointDomain d (n + (m + 1))) :=
    {y | section43OSForwardTubeLift_succRight d t y ∈
      TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))}
  have hK_compact : IsCompact Kfg := by
    simpa [Kfg] using
      (hasCompactSupport_osConjTensorProduct_of_hasCompactSupport
        (d := d) f.1 g.1 hf_compact hg_compact).isCompact
  have hU_open : IsOpen Ufg := by
    exact (isOpen_TubeDomainSetPi_forwardConeAbs d (n + (m + 1))).preimage
      (continuous_section43OSForwardTubeLift_succRight (d := d) (n := n) (m := m) t)
  have hK_sub_U : Kfg ⊆ Ufg := by
    intro y hy
    exact section43OSForwardTubeLift_mem_forwardTube_of_osTsupport_succRight
      (d := d) f g ht (by simpa [Kfg] using hy)
  have hdisj : Disjoint Kfg Ufgᶜ := by
    exact disjoint_compl_right_iff_subset.mpr hK_sub_U
  obtain ⟨ρc, hρ_one, hρ_zero, hρ_compact, hρ_range⟩ :=
    exists_continuous_one_zero_of_isCompact hK_compact hU_open.isClosed_compl hdisj
  refine ⟨ρc, ρc.continuous, hρ_compact, hρ_range, ?_, ?_⟩
  · simpa [Kfg] using hρ_one
  · intro y hyρ
    by_contra hyU
    exact hyρ (hρ_zero hyU)

/-- A fixed point of the forward tube, used outside the cutoff support in the
safe lift. -/
def section43OSForwardTubeBasePoint
    (d N : ℕ) [NeZero d] :
    Fin N → Fin (d + 1) → ℂ :=
  fun k μ =>
    ((canonicalForwardConeDirection (d := d) N k μ : ℝ) : ℂ) * Complex.I

theorem section43OSForwardTubeBasePoint_mem_forwardTube
    (d N : ℕ) [NeZero d] :
    section43OSForwardTubeBasePoint d N ∈
      TubeDomainSetPi (ForwardConeAbs d N) := by
  change
    (fun k μ => (section43OSForwardTubeBasePoint d N k μ).im) ∈
      ForwardConeAbs d N
  convert
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := N)
      (canonicalForwardConeDirection (d := d) N)).mp
      (canonicalForwardConeDirection_mem (d := d) N) using 1
  ext k μ
  simp [section43OSForwardTubeBasePoint]

/-- Cutoff-safe version of the successor-right forward-tube lift.  It agrees
with the original lift where `ρ = 1` and collapses to a fixed tube point where
`ρ = 0`. -/
def section43OSForwardTubeSafeLift_succRight
    (d : ℕ) [NeZero d] {n m : ℕ} (t : ℝ)
    (ρ : NPointDomain d (n + (m + 1)) → ℝ) :
    NPointDomain d (n + (m + 1)) →
      Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun y k μ =>
    (ρ y : ℂ) * section43OSForwardTubeLift_succRight d t y k μ +
      ((1 - ρ y : ℝ) : ℂ) *
        section43OSForwardTubeBasePoint d (n + (m + 1)) k μ

theorem section43OSForwardTubeSafeLift_eq_lift_of_rho_eq_one_succRight
    (d : ℕ) [NeZero d] {n m : ℕ} (t : ℝ)
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    {y : NPointDomain d (n + (m + 1))}
    (hρ : ρ y = 1) :
    section43OSForwardTubeSafeLift_succRight d t ρ y =
      section43OSForwardTubeLift_succRight d t y := by
  ext k μ
  simp [section43OSForwardTubeSafeLift_succRight, hρ]

theorem section43OSForwardTubeSafeLift_mem_forwardTube_succRight
    (d : ℕ) [NeZero d] {n m : ℕ} {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))}) :
    ∀ y,
      section43OSForwardTubeSafeLift_succRight d t ρ y ∈
        TubeDomainSetPi (ForwardConeAbs d (n + (m + 1))) := by
  intro y
  let N := n + (m + 1)
  by_cases hρ_zero : ρ y = 0
  · have hsafe :
      section43OSForwardTubeSafeLift_succRight d t ρ y =
        section43OSForwardTubeBasePoint d N := by
      ext k μ
      simp [section43OSForwardTubeSafeLift_succRight, N, hρ_zero]
    rw [hsafe]
    exact section43OSForwardTubeBasePoint_mem_forwardTube d N
  · have hy_support : y ∈ Function.support ρ :=
      Function.mem_support.mpr hρ_zero
    have horig_tube :
        section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d N) := by
      simpa [N] using hρ_support hy_support
    have him_orig :
        (fun k μ => (section43OSForwardTubeLift_succRight d t y k μ).im) ∈
          ForwardConeAbs d N := by
      simpa [TubeDomainSetPi, N] using horig_tube
    have him_base :
        (fun k μ => (section43OSForwardTubeBasePoint d N k μ).im) ∈
          ForwardConeAbs d N := by
      simpa [TubeDomainSetPi] using
        section43OSForwardTubeBasePoint_mem_forwardTube d N
    have hρ_nonneg : 0 ≤ ρ y := (hρ_range y).1
    have hρ_le : ρ y ≤ 1 := (hρ_range y).2
    have h1ρ_nonneg : 0 ≤ 1 - ρ y := sub_nonneg.mpr hρ_le
    have hsum : ρ y + (1 - ρ y) = 1 := by ring
    have hconv :
        ρ y • (fun k μ =>
            (section43OSForwardTubeLift_succRight d t y k μ).im) +
          (1 - ρ y) • (fun k μ =>
            (section43OSForwardTubeBasePoint d N k μ).im) ∈
          ForwardConeAbs d N :=
      (convex_iff_add_mem.mp (forwardConeAbs_convex d N))
        him_orig him_base hρ_nonneg h1ρ_nonneg hsum
    change
      (fun k μ =>
        (section43OSForwardTubeSafeLift_succRight d t ρ y k μ).im) ∈
        ForwardConeAbs d N
    convert hconv using 1
    ext k μ
    simp [section43OSForwardTubeSafeLift_succRight, N, Pi.add_apply, Pi.smul_apply]

theorem continuous_section43OSForwardTubeSafeLift_succRight
    (d : ℕ) [NeZero d] {n m : ℕ} {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ) :
    Continuous (section43OSForwardTubeSafeLift_succRight
      (d := d) (n := n) (m := m) t ρ) := by
  have hLift :
      Continuous (section43OSForwardTubeLift_succRight
        (d := d) (n := n) (m := m) t) :=
    continuous_section43OSForwardTubeLift_succRight
      (d := d) (n := n) (m := m) t
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  have hρC : Continuous fun y => ((ρ y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hρ_cont
  have h1ρC : Continuous fun y => (((1 - ρ y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub hρ_cont)
  have hcoord_lift :
      Continuous fun y =>
        section43OSForwardTubeLift_succRight d t y k μ :=
    (continuous_apply μ).comp ((continuous_apply k).comp hLift)
  have hcoord_base :
      Continuous fun _ : NPointDomain d (n + (m + 1)) =>
        section43OSForwardTubeBasePoint d (n + (m + 1)) k μ :=
    continuous_const
  simpa [section43OSForwardTubeSafeLift_succRight] using
    (hρC.mul hcoord_lift).add (h1ρC.mul hcoord_base)

/-- Safe Paley-Wiener Schwartz family associated to the support-localized
forward-tube lift. -/
def section43OSForwardTubeSafePsiZFamily_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ) :
    (Fin ((n + (m + 1)) * (d + 1)) → ℝ) →
      SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  fun yflat =>
    multiDimPsiZExt
      ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
        ForwardConeAbs d (n + (m + 1)))
      hCflat_open hCflat_conv hCflat_cone hCflat_salient
      (flattenCLEquiv (n + (m + 1)) (d + 1)
        (section43OSForwardTubeSafeLift_succRight d t ρ
          ((flattenCLEquivReal (n + (m + 1)) (d + 1)).symm yflat)))

theorem continuous_section43OSForwardTubeSafePsiZFamily_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))}) :
    Continuous
      (section43OSForwardTubeSafePsiZFamily_succRight
        (d := d) (n := n) (m := m)
        hCflat_open hCflat_conv hCflat_cone hCflat_salient (t := t) ρ) := by
  let N := n + (m + 1)
  let Cflat : Set (Fin (N * (d + 1)) → ℝ) :=
    (flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N
  let zMap : (Fin (N * (d + 1)) → ℝ) → Fin (N * (d + 1)) → ℂ :=
    fun yflat =>
      flattenCLEquiv N (d + 1)
        (section43OSForwardTubeSafeLift_succRight d t ρ
          ((flattenCLEquivReal N (d + 1)).symm yflat))
  have hz_cont : Continuous zMap := by
    exact (flattenCLEquiv N (d + 1)).continuous.comp
      ((continuous_section43OSForwardTubeSafeLift_succRight
        (d := d) (n := n) (m := m) (t := t) ρ hρ_cont).comp
        (flattenCLEquivReal N (d + 1)).symm.continuous)
  have hz_mem : ∀ yflat, zMap yflat ∈ SCV.TubeDomain Cflat := by
    intro yflat
    dsimp [zMap, Cflat]
    exact flattenCLEquiv_mem_tubeDomain_image (n := N) (r := d)
      (section43OSForwardTubeSafeLift_mem_forwardTube_succRight
        (d := d) (n := n) (m := m) (t := t) ρ hρ_range hρ_support
        ((flattenCLEquivReal N (d + 1)).symm yflat))
  simpa [section43OSForwardTubeSafePsiZFamily_succRight, Cflat, zMap, N] using
    continuous_multiDimPsiZExt_comp_of_mem_tube
      Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient zMap hz_cont hz_mem

/-- Polynomial seminorm bound for the support-localized safe forward-tube
Paley-Wiener family.  Since the safe lift is constant off a compact support and
tube-valued everywhere, the image lies in one compact subset of the tube; the
polynomial exponent can therefore be chosen to be `0`. -/
theorem seminorm_section43OSForwardTubeSafePsiZFamily_bound_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ)
    (hρ_compact : HasCompactSupport ρ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))}) :
    ∀ (k l : ℕ), ∃ (C : ℝ) (Npow : ℕ), 0 < C ∧
      ∀ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        SchwartzMap.seminorm ℝ k l
          (section43OSForwardTubeSafePsiZFamily_succRight
            (d := d) (n := n) (m := m)
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (t := t) ρ yflat) ≤
          C * (1 + ‖yflat‖) ^ Npow := by
  intro k l
  let Npts := n + (m + 1)
  let Cflat : Set (Fin (Npts * (d + 1)) → ℝ) :=
    (flattenCLEquivReal Npts (d + 1)) '' ForwardConeAbs d Npts
  let eR := flattenCLEquivReal Npts (d + 1)
  let zMap : (Fin (Npts * (d + 1)) → ℝ) → Fin (Npts * (d + 1)) → ℂ :=
    fun yflat =>
      flattenCLEquiv Npts (d + 1)
        (section43OSForwardTubeSafeLift_succRight d t ρ (eR.symm yflat))
  let z0 : Fin (Npts * (d + 1)) → ℂ :=
    flattenCLEquiv Npts (d + 1)
      (section43OSForwardTubeBasePoint d Npts)
  let Ksafe : Set (Fin (Npts * (d + 1)) → ℂ) :=
    zMap '' (eR '' tsupport ρ) ∪ {z0}
  have hz_cont : Continuous zMap := by
    exact (flattenCLEquiv Npts (d + 1)).continuous.comp
      ((continuous_section43OSForwardTubeSafeLift_succRight
        (d := d) (n := n) (m := m) (t := t) ρ hρ_cont).comp
        eR.symm.continuous)
  have hK_compact : IsCompact Ksafe := by
    have hK_image : IsCompact (zMap '' (eR '' tsupport ρ)) :=
      (hρ_compact.isCompact.image eR.continuous).image hz_cont
    exact hK_image.union isCompact_singleton
  have hK_tube : Ksafe ⊆ SCV.TubeDomain Cflat := by
    intro z hz
    rcases hz with hz | hz
    · rcases hz with ⟨yflat, _hyflat, rfl⟩
      dsimp [zMap, Cflat]
      exact flattenCLEquiv_mem_tubeDomain_image (n := Npts) (r := d)
        (section43OSForwardTubeSafeLift_mem_forwardTube_succRight
          (d := d) (n := n) (m := m) (t := t) ρ hρ_range hρ_support
          (eR.symm yflat))
    · have hz0 : z = z0 := by simpa using hz
      rw [hz0]
      dsimp [z0, Cflat]
      exact flattenCLEquiv_mem_tubeDomain_image (n := Npts) (r := d)
        (section43OSForwardTubeBasePoint_mem_forwardTube d Npts)
  obtain ⟨B, hB_pos, hB_bound⟩ :=
    multiDimPsiZExt_compactTubeSet_seminorm_bound
      Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
      hK_compact hK_tube k l
  refine ⟨B, 0, hB_pos, ?_⟩
  intro yflat
  have hz_mem : zMap yflat ∈ Ksafe := by
    let y := eR.symm yflat
    by_cases hρ_zero : ρ y = 0
    · have hsafe :
          section43OSForwardTubeSafeLift_succRight d t ρ y =
            section43OSForwardTubeBasePoint d Npts := by
        ext a μ
        simp [section43OSForwardTubeSafeLift_succRight, hρ_zero, Npts]
      have hz_eq : zMap yflat = z0 := by
        simpa [zMap, z0, y] using
          congrArg (flattenCLEquiv Npts (d + 1)) hsafe
      exact Or.inr (by simp [hz_eq])
    · have hy_support : y ∈ Function.support ρ :=
        Function.mem_support.mpr hρ_zero
      have hy_tsupport : y ∈ tsupport ρ :=
        subset_tsupport ρ hy_support
      refine Or.inl ?_
      refine ⟨eR y, ⟨y, hy_tsupport, rfl⟩, ?_⟩
      simp [y]
  have hbase :
      SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt Cflat
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (zMap yflat)) ≤ B :=
    hB_bound (zMap yflat) hz_mem
  have hfinal :
      SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt Cflat
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (zMap yflat)) ≤
        B * (1 + ‖yflat‖) ^ (0 : ℕ) := by
    simpa using hbase
  simpa [section43OSForwardTubeSafePsiZFamily_succRight,
    Cflat, zMap, Npts] using hfinal

/-- Flat Fubini packet for the support-localized safe forward-tube
Paley-Wiener family.  This is the safe analogue of the finite-height canonical
shell packet: `schwartz_clm_fubini_exchange` constructs the Schwartz kernel and
exchanges the continuous linear functional with the parameter integral. -/
theorem section43OSForwardTubeSafePsiZFamily_pairing_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ)
    (hρ_compact : HasCompactSupport ρ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))})
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (fFlat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ) :
    ∃ KSafe :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ,
      (∀ ξ : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        KSafe ξ =
          ∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
            (section43OSForwardTubeSafePsiZFamily_succRight
              (d := d) (n := n) (m := m)
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (t := t) ρ yflat) ξ *
              fFlat yflat) ∧
      (∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        Tflat
          (section43OSForwardTubeSafePsiZFamily_succRight
            (d := d) (n := n) (m := m)
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (t := t) ρ yflat) *
          fFlat yflat) =
        Tflat KSafe := by
  let gFamily : (Fin (((n + (m + 1)) * (d + 1))) → ℝ) →
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ :=
    section43OSForwardTubeSafePsiZFamily_succRight
      (d := d) (n := n) (m := m)
      hCflat_open hCflat_conv hCflat_cone hCflat_salient (t := t) ρ
  have hg_cont : Continuous gFamily := by
    simpa [gFamily] using
      continuous_section43OSForwardTubeSafePsiZFamily_succRight
        (d := d) (n := n) (m := m)
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (t := t) ρ hρ_cont hρ_range hρ_support
  have hg_bound :
      ∀ (k l : ℕ), ∃ (C : ℝ) (Npow : ℕ), C > 0 ∧
        ∀ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
          SchwartzMap.seminorm ℝ k l (gFamily yflat) ≤
            C * (1 + ‖yflat‖) ^ Npow := by
    simpa [gFamily] using
      seminorm_section43OSForwardTubeSafePsiZFamily_bound_succRight
        (d := d) (n := n) (m := m)
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (t := t) ρ hρ_cont hρ_compact hρ_range hρ_support
  obtain ⟨KSafe, hKSafe_eval, hKSafe_pair⟩ :=
    schwartz_clm_fubini_exchange Tflat gFamily fFlat hg_cont hg_bound
  refine ⟨KSafe, ?_, ?_⟩
  · intro ξ
    simpa [gFamily] using hKSafe_eval ξ
  · simpa [gFamily] using hKSafe_pair.symm

/-- Safe forward-tube Fubini packet rewritten through the Section 4.3
Fourier-Laplace witness.  The flattened `Tflat` integral produced by
`section43OSForwardTubeSafePsiZFamily_pairing_succRight` is exactly the scalar
configuration-space integral of `bvt_F` along the safe lift. -/
theorem section43OSForwardTubeSafePsiZFamily_pairing_bvt_F_succRight
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ)
    (hρ_compact : HasCompactSupport ρ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))})
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (φ : SchwartzNPoint d (n + (m + 1))) :
    ∃ KSafe :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ,
      (∀ ξ : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        KSafe ξ =
          ∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
            (section43OSForwardTubeSafePsiZFamily_succRight
              (d := d) (n := n) (m := m)
              hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
              hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
              (t := t) ρ yflat) ξ *
              _root_.flattenSchwartzNPoint (d := d) φ yflat) ∧
      (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeSafeLift_succRight d t ρ y) *
        φ y) =
        Tflat KSafe := by
  let Npts := n + (m + 1)
  let Cflat : Set (Fin (Npts * (d + 1)) → ℝ) :=
    (flattenCLEquivReal Npts (d + 1)) '' ForwardConeAbs d Npts
  let gFlat : (Fin (Npts * (d + 1)) → ℝ) → ℂ :=
    fun yflat =>
      Tflat
        (section43OSForwardTubeSafePsiZFamily_succRight
          (d := d) (n := n) (m := m)
          hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
          hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
          (t := t) ρ yflat) *
        _root_.flattenSchwartzNPoint (d := d) φ yflat
  obtain ⟨KSafe, hKSafe_eval, hKSafe_pair⟩ :=
    section43OSForwardTubeSafePsiZFamily_pairing_succRight
      (d := d) (n := n) (m := m)
      hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
      hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
      (t := t) ρ hρ_cont hρ_compact hρ_range hρ_support
      Tflat (_root_.flattenSchwartzNPoint (d := d) φ)
  refine ⟨KSafe, ?_, ?_⟩
  · intro ξ
    simpa using hKSafe_eval ξ
  have hflat_cv :
      ∫ yflat : Fin (Npts * (d + 1)) → ℝ, gFlat yflat =
        ∫ y : NPointDomain d Npts,
          gFlat (flattenCLEquivReal Npts (d + 1) y) :=
    integral_flatten_change_of_variables Npts (d + 1) gFlat
  have htarget_to_flat :
      (∫ y : NPointDomain d Npts,
        bvt_F OS lgc Npts
          (section43OSForwardTubeSafeLift_succRight d t ρ y) *
        φ y) =
        ∫ y : NPointDomain d Npts,
          gFlat (flattenCLEquivReal Npts (d + 1) y) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    let zSafe : Fin Npts → Fin (d + 1) → ℂ :=
      section43OSForwardTubeSafeLift_succRight d t ρ y
    have hzSafe_mem :
        zSafe ∈ TubeDomainSetPi (ForwardConeAbs d Npts) := by
      simpa [zSafe, Npts] using
        section43OSForwardTubeSafeLift_mem_forwardTube_succRight
          (d := d) (n := n) (m := m) (t := t)
          ρ hρ_range hρ_support y
    have hbvt :
        bvt_F OS lgc Npts zSafe =
          Tflat
            (multiDimPsiZExt Cflat
              hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
              hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
              (flattenCLEquiv Npts (d + 1) zSafe)) := by
      calc
        bvt_F OS lgc Npts zSafe
            = fourierLaplaceExtMultiDim Cflat
                hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
                hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
                Tflat (flattenCLEquiv Npts (d + 1) zSafe) := by
              simpa [Cflat, Npts] using hTflat_FL.hFL zSafe hzSafe_mem
        _ = Tflat
              (multiDimPsiZExt Cflat
                hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
                hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
                (flattenCLEquiv Npts (d + 1) zSafe)) := by
              rw [fourierLaplaceExtMultiDim_eq_ext]
    simp [gFlat, Cflat, zSafe, hbvt, Npts,
      section43OSForwardTubeSafePsiZFamily_succRight,
      _root_.flattenSchwartzNPoint_apply]
  calc
    (∫ y : NPointDomain d Npts,
        bvt_F OS lgc Npts
          (section43OSForwardTubeSafeLift_succRight d t ρ y) *
        φ y)
        = ∫ y : NPointDomain d Npts,
            gFlat (flattenCLEquivReal Npts (d + 1) y) := htarget_to_flat
    _ = ∫ yflat : Fin (Npts * (d + 1)) → ℝ, gFlat yflat := hflat_cv.symm
    _ = Tflat KSafe := by
        simpa [gFlat, Npts] using hKSafe_pair

/-- If the cutoff is `1` on the support of the scalar density, then the
support-localized safe lift may be replaced by the original forward-tube lift
inside the scalar `bvt_F` integral. -/
theorem integral_bvt_F_safeLift_eq_lift_of_rho_eq_one_on_tsupport_succRight
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (φ : SchwartzNPoint d (n + (m + 1)))
    (hρ_one :
      EqOn ρ 1
        (tsupport (φ : NPointDomain d (n + (m + 1)) → ℂ))) :
    (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeSafeLift_succRight d t ρ y) *
        φ y) =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight d t y) *
        φ y := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  by_cases hφ_zero : (φ : NPointDomain d (n + (m + 1)) → ℂ) y = 0
  · simp [hφ_zero]
  · have hy_support :
        y ∈ Function.support
          (φ : NPointDomain d (n + (m + 1)) → ℂ) := by
      simpa [Function.mem_support] using hφ_zero
    have hy_tsupport :
        y ∈ tsupport (φ : NPointDomain d (n + (m + 1)) → ℂ) :=
      subset_tsupport _ hy_support
    have hρy : ρ y = 1 := hρ_one hy_tsupport
    rw [section43OSForwardTubeSafeLift_eq_lift_of_rho_eq_one_succRight
      (d := d) (n := n) (m := m) (t := t) ρ hρy]

/-- Safe `bvt_F` Fubini packet after removing the cutoff from the scalar
integral on a density whose topological support lies in the cutoff-one set. -/
theorem section43OSForwardTubeLift_pairing_bvt_F_of_safeCutoff_succRight
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ)
    (hρ_compact : HasCompactSupport ρ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))})
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (φ : SchwartzNPoint d (n + (m + 1)))
    (hρ_one :
      EqOn ρ 1
        (tsupport (φ : NPointDomain d (n + (m + 1)) → ℂ))) :
    ∃ KSafe :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ,
      (∀ ξ : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        KSafe ξ =
          ∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
            (section43OSForwardTubeSafePsiZFamily_succRight
              (d := d) (n := n) (m := m)
              hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
              hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
              (t := t) ρ yflat) ξ *
              _root_.flattenSchwartzNPoint (d := d) φ yflat) ∧
      (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight d t y) *
        φ y) =
        Tflat KSafe := by
  obtain ⟨KSafe, hKSafe_eval, hKSafe_pair⟩ :=
    section43OSForwardTubeSafePsiZFamily_pairing_bvt_F_succRight
      (d := d) OS lgc (n := n) (m := m) (t := t)
      ρ hρ_cont hρ_compact hρ_range hρ_support
      Tflat hTflat_FL φ
  refine ⟨KSafe, hKSafe_eval, ?_⟩
  calc
    (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight d t y) *
        φ y)
        =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeSafeLift_succRight d t ρ y) *
        φ y := by
          exact (integral_bvt_F_safeLift_eq_lift_of_rho_eq_one_on_tsupport_succRight
          (d := d) OS lgc (n := n) (m := m) (t := t) ρ φ hρ_one).symm
    _ = Tflat KSafe := hKSafe_pair

/-- Pointwise kernel-evaluation version of cutoff removal: when the cutoff is
`1` on the support of the scalar density, the flattened safe-family integral
equals the original forward-lift kernel integral. -/
theorem section43OSForwardTubeSafeKernel_eval_eq_liftIntegral_of_rho_eq_one_on_tsupport_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1))))
    {t : ℝ}
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (φ : SchwartzNPoint d (n + (m + 1)))
    (hρ_one :
      EqOn ρ 1
        (tsupport (φ : NPointDomain d (n + (m + 1)) → ℂ)))
    (ξ : Fin (((n + (m + 1)) * (d + 1))) → ℝ) :
    (∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        (section43OSForwardTubeSafePsiZFamily_succRight
          (d := d) (n := n) (m := m)
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (t := t) ρ yflat) ξ *
          _root_.flattenSchwartzNPoint (d := d) φ yflat) =
      ∫ y : NPointDomain d (n + (m + 1)),
        multiDimPsiZExt
          ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
            ForwardConeAbs d (n + (m + 1)))
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        φ y := by
  let Npts := n + (m + 1)
  let Cflat : Set (Fin (Npts * (d + 1)) → ℝ) :=
    (flattenCLEquivReal Npts (d + 1)) '' ForwardConeAbs d Npts
  let gFlat : (Fin (Npts * (d + 1)) → ℝ) → ℂ :=
    fun yflat =>
      (section43OSForwardTubeSafePsiZFamily_succRight
        (d := d) (n := n) (m := m)
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (t := t) ρ yflat) ξ *
        _root_.flattenSchwartzNPoint (d := d) φ yflat
  have hflat_cv :
      ∫ yflat : Fin (Npts * (d + 1)) → ℝ, gFlat yflat =
        ∫ y : NPointDomain d Npts,
          gFlat (flattenCLEquivReal Npts (d + 1) y) :=
    integral_flatten_change_of_variables Npts (d + 1) gFlat
  have htarget_to_flat :
      (∫ y : NPointDomain d Npts,
        multiDimPsiZExt Cflat
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (flattenCLEquiv Npts (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        φ y) =
        ∫ y : NPointDomain d Npts,
          gFlat (flattenCLEquivReal Npts (d + 1) y) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    by_cases hφ_zero : (φ : NPointDomain d Npts → ℂ) y = 0
    · simp [gFlat, Cflat, hφ_zero, Npts, _root_.flattenSchwartzNPoint_apply]
    · have hy_support :
          y ∈ Function.support (φ : NPointDomain d Npts → ℂ) := by
        simpa [Function.mem_support] using hφ_zero
      have hy_tsupport :
          y ∈ tsupport (φ : NPointDomain d Npts → ℂ) :=
        subset_tsupport _ hy_support
      have hρy : ρ y = 1 := hρ_one (by simpa [Npts] using hy_tsupport)
      have hsafe :
          section43OSForwardTubeSafeLift_succRight d t ρ y =
            section43OSForwardTubeLift_succRight d t y :=
        section43OSForwardTubeSafeLift_eq_lift_of_rho_eq_one_succRight
          (d := d) (n := n) (m := m) (t := t) ρ hρy
      simp [gFlat, Cflat, hsafe, Npts,
        section43OSForwardTubeSafePsiZFamily_succRight,
        _root_.flattenSchwartzNPoint_apply]
  calc
    (∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        (section43OSForwardTubeSafePsiZFamily_succRight
          (d := d) (n := n) (m := m)
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (t := t) ρ yflat) ξ *
          _root_.flattenSchwartzNPoint (d := d) φ yflat)
        = ∫ yflat : Fin (Npts * (d + 1)) → ℝ, gFlat yflat := by
          rfl
    _ = ∫ y : NPointDomain d Npts,
          gFlat (flattenCLEquivReal Npts (d + 1) y) := hflat_cv
    _ =
      ∫ y : NPointDomain d Npts,
        multiDimPsiZExt Cflat
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (flattenCLEquiv Npts (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        φ y := htarget_to_flat.symm

/-- Safe forward-tube Fubini kernel specialized to the OS tensor-product
density.  Its pointwise values agree with the OS I `(4.24)` kernel on the
Wightman spectral region, and its `Tflat` pairing is the original forward-lift
`bvt_F` scalar integral. -/
theorem exists_section43OSForwardTubeSafeKernel_pairing_eq_OS24Kernel_on_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (ρ : NPointDomain d (n + (m + 1)) → ℝ)
    (hρ_cont : Continuous ρ)
    (hρ_compact : HasCompactSupport ρ)
    (hρ_range : ∀ y, ρ y ∈ Icc (0 : ℝ) 1)
    (hρ_support :
      Function.support ρ ⊆
        {y | section43OSForwardTubeLift_succRight d t y ∈
          TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))})
    (hρ_one :
      EqOn ρ 1
        (tsupport
          ((f.1.osConjTensorProduct g.1) :
            NPointDomain d (n + (m + 1)) → ℂ)))
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    ∃ KSafe :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ,
      (∀ ξ : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
        KSafe ξ =
          ∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
            (section43OSForwardTubeSafePsiZFamily_succRight
              (d := d) (n := n) (m := m)
              hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
              hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
              (t := t) ρ yflat) ξ *
              _root_.flattenSchwartzNPoint (d := d)
                (f.1.osConjTensorProduct g.1) yflat) ∧
      Set.EqOn
        (fun ξ => KSafe ξ)
        (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
        (section43WightmanSpectralRegion d (n + (m + 1))) ∧
      (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight d t y) *
        (f.1.osConjTensorProduct g.1) y) =
        Tflat KSafe := by
  let φOS : SchwartzNPoint d (n + (m + 1)) :=
    f.1.osConjTensorProduct g.1
  obtain ⟨KSafe, hKSafe_eval, hKSafe_pair⟩ :=
    section43OSForwardTubeLift_pairing_bvt_F_of_safeCutoff_succRight
      (d := d) OS lgc (n := n) (m := m) (t := t)
      ρ hρ_cont hρ_compact hρ_range hρ_support
      Tflat hTflat_FL φOS (by simpa [φOS] using hρ_one)
  refine ⟨KSafe, ?_, ?_, ?_⟩
  · intro ξ
    simpa [φOS] using hKSafe_eval ξ
  · intro ξ hξ
    calc
      KSafe ξ
          =
        ∫ yflat : Fin (((n + (m + 1)) * (d + 1))) → ℝ,
          (section43OSForwardTubeSafePsiZFamily_succRight
            (d := d) (n := n) (m := m)
            hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
            hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
            (t := t) ρ yflat) ξ *
            _root_.flattenSchwartzNPoint (d := d) φOS yflat := hKSafe_eval ξ
      _ =
        ∫ y : NPointDomain d (n + (m + 1)),
          multiDimPsiZExt
            ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
              ForwardConeAbs d (n + (m + 1)))
            hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
            hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
            (flattenCLEquiv (n + (m + 1)) (d + 1)
              (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
          φOS y := by
            exact
              section43OSForwardTubeSafeKernel_eval_eq_liftIntegral_of_rho_eq_one_on_tsupport_succRight
                (d := d) (n := n) (m := m)
                hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
                hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
                (t := t) ρ φOS (by simpa [φOS] using hρ_one) ξ
      _ = section43OS24Kernel_succRight d n m φ ψ t ht ξ := by
            simpa [φOS] using
              section43OSForwardTubeLiftKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight
                (d := d) (n := n) (m := m) (OS := OS) (lgc := lgc)
                (φ := φ) (ψ := ψ) (f := f) (g := g)
                hφ_rep hψ_rep ht Tflat hTflat_FL ξ hξ
  · simpa [φOS] using hKSafe_pair

/-- The OS I `(4.24)` kernel paired with a Wightman-spectrally-supported
flattened distribution is the forward-tube `bvt_F` scalar integral on the
OS tensor-product density.  This is the support-localized safe-Fubini repair of
the formerly forbidden direct Bochner-kernel step. -/
theorem section43OS24Kernel_pairing_eq_forwardTubeLiftIntegral_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight (d := d) t y) *
        (f.1.osConjTensorProduct g.1) y := by
  obtain ⟨ρ, hρ_cont, hρ_compact, hρ_range, hρ_one, hρ_support⟩ :=
    exists_section43OSForwardTubeCutoff_succRight
      (d := d) (n := n) (m := m) f g hf_compact hg_compact ht
  obtain ⟨KSafe, _hKSafe_eval, hKSafe_eqOn, hKSafe_pair⟩ :=
    exists_section43OSForwardTubeSafeKernel_pairing_eq_OS24Kernel_on_spectralRegion_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ f g
      hφ_rep hψ_rep ht ρ hρ_cont hρ_compact hρ_range hρ_support
      hρ_one Tflat hTflat_FL
  calc
    Tflat (section43OS24Kernel_succRight d n m φ ψ t ht)
        = Tflat KSafe := by
          exact hasFourierSupportIn_eqOn hTflat_supp
            (fun ξ hξ => (hKSafe_eqOn hξ).symm)
    _ =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight (d := d) t y) *
        (f.1.osConjTensorProduct g.1) y := hKSafe_pair.symm

/-- The raw successor-right `xiShift` shell is the positive-time OS scalar for
the Euclidean pair `(f, g)` with the right component shifted by `t`. -/
theorem section43_xiShiftShell_eq_osScalar_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t) :
    (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (f.1.osConjTensorProduct g.1) y) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  exact
    (schwinger_simpleTensor_timeShift_eq_xiShift
      (d := d) (OS := OS) (hm := Nat.succ_pos m)
      (Ψ := bvt_F OS lgc (n + (m + 1)))
      (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + (m + 1)))
      (f := f.1) (hf_ord := f.2) (g := g.1) (hg_ord := g.2)
      (t := t) ht).symm

/-- Final S5 scalar-recognition theorem for the OS route: after the compiled
frequency-side bridge has produced the OS I `(4.24)` kernel, pairing it against
a Wightman-spectrally-supported flattened distribution gives exactly the OS
Schwinger scalar of the positive-time Euclidean pair. -/
theorem section43OS24Kernel_pairing_eq_osScalar_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  calc
    Tflat (section43OS24Kernel_succRight d n m φ ψ t ht)
        =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight (d := d) t y) *
        (f.1.osConjTensorProduct g.1) y := by
          exact
            section43OS24Kernel_pairing_eq_forwardTubeLiftIntegral_succRight
              (d := d) (n := n) (m := m) OS lgc φ ψ f g
              hf_compact hg_compact hφ_rep hψ_rep ht
              Tflat hTflat_supp hTflat_FL
    _ =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (f.1.osConjTensorProduct g.1) y := by
          exact
            section43_forwardTubeLiftIntegral_eq_xiShiftShell_succRight
              (d := d) (n := n) (m := m) OS lgc t
              ((f.1.osConjTensorProduct g.1) :
                NPointDomain d (n + (m + 1)) → ℂ)
    _ =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) :=
        section43_xiShiftShell_eq_osScalar_succRight
          (d := d) (n := n) (m := m) OS lgc f g ht

/-- Assembly of the compiled real-time horizontal Wightman bridge with the S5
OS scalar-recognition theorem.  This is the theorem surface that downstream
positivity can consume before reconnecting to `lemma42_matrix_element_time_interchange`. -/
theorem section43TimeShiftKernel_psiZ_pairing_eq_osScalar_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat :
      SchwartzMap (Fin (((n + (m + 1)) * (d + 1))) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap
          (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + (m + 1))
            (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat))
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  calc
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ)
        = Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) := by
          exact
            section43TimeShiftKernel_psiZ_pairing_eq_Tflat_OS24Kernel_succRight
              (d := d) (n := n) (m := m) OS lgc φ ψ ht
              Tflat hTflat_supp hTflat_bv
    _ =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) := by
          exact
            section43OS24Kernel_pairing_eq_osScalar_succRight
              (d := d) (n := n) (m := m) OS lgc φ ψ f g
              hf_compact hg_compact hφ_rep hψ_rep ht
              Tflat hTflat_supp hTflat_FL

/-- Canonical-package version of
`section43TimeShiftKernel_psiZ_pairing_eq_osScalar_succRight`.

This removes the explicit `Tflat` arguments by obtaining the common Wightman
spectral-support, boundary-value, and Fourier-Laplace witness packet from the
public boundary-value construction.  The component Fourier-Laplace
representative hypotheses remain explicit: those are the next genuine
consumer-side seam. -/
theorem section43TimeShiftKernel_psiZ_pairing_eq_osScalar_from_bvt_W_package_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n ⟨f, hf_ord⟩
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) ⟨g, hg_ord⟩
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t) :
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) := by
  obtain ⟨Tflat, hTflat_supp, hTflat_bv, hTflat_FL⟩ :=
    bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion_with_fourierLaplaceWitness
      (d := d) OS lgc (n + (m + 1))
  exact
    section43TimeShiftKernel_psiZ_pairing_eq_osScalar_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ
      ⟨f, hf_ord⟩ ⟨g, hg_ord⟩
      hf_compact hg_compact hφ_rep hψ_rep ht
      Tflat hTflat_supp hTflat_bv hTflat_FL

/-- Quotient-projection version of the canonical-package S5 scalar theorem.

The ambient tests `φ` and `ψ` enter only through their deterministic frequency
representatives.  This theorem derives the required representative predicates
from positive-energy quotient equalities against explicit Fourier-Laplace
representative witnesses. -/
theorem section43TimeShiftKernel_psiZ_pairing_eq_osScalar_from_frequencyProjection_witness_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    (Φφ : SchwartzNPoint d n)
    (Φψ : SchwartzNPoint d (m + 1))
    (hΦφ_rep :
      section43FourierLaplaceRepresentative d n ⟨f, hf_ord⟩ Φφ)
    (hΦψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) ⟨g, hg_ord⟩ Φψ)
    (hφ_proj :
      section43FrequencyProjection (d := d) n φ =
        section43PositiveEnergyQuotientMap (d := d) n Φφ)
    (hψ_proj :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43PositiveEnergyQuotientMap (d := d) (m + 1) Φψ)
    {t : ℝ} (ht : 0 < t) :
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) := by
  have hφ_rep :
      section43FourierLaplaceRepresentative d n ⟨f, hf_ord⟩
        (section43FrequencyRepresentative (d := d) n φ) :=
    section43FrequencyRepresentative_is_fourierLaplaceRepresentative_of_quotient_eq
      (d := d) (n := n) φ ⟨f, hf_ord⟩ Φφ hΦφ_rep hφ_proj
  have hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) ⟨g, hg_ord⟩
        (section43FrequencyRepresentative (d := d) (m + 1) ψ) :=
    section43FrequencyRepresentative_is_fourierLaplaceRepresentative_of_quotient_eq
      (d := d) (n := m + 1) ψ ⟨g, hg_ord⟩ Φψ hΦψ_rep hψ_proj
  exact
    section43TimeShiftKernel_psiZ_pairing_eq_osScalar_from_bvt_W_package_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ f hf_ord hf_compact
      g hg_ord hg_compact hφ_rep hψ_rep ht

end OSReconstruction
