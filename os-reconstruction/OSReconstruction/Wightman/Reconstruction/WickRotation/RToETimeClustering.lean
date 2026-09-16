/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToETimeShiftBounds















noncomputable section
open scoped Topology NNReal
open Set Filter
namespace OSReconstruction
variable {d : ℕ} [NeZero d]

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
attribute [local irreducible] rToEReflectedPairing

/-- The whole positive-time orbit admits finite approximation in the reflected
seminorm, without a compact-support or full OS-record premise. -/
theorem rToE_reflected_timeShift_finite_approximation (Wfn : WightmanFunctions d)
    {n : ℕ} (f : euclideanPositiveTimeSubmodule (d := d) n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Finset ℝ≥0, ∀ s : ℝ≥0, ∃ t ∈ K,
      ‖wickRotatedBoundaryPairing Wfn (n + n)
        ((timeShiftSchwartzNPoint (d := d) s f.1 -
          timeShiftSchwartzNPoint (d := d) t f.1).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s f.1 -
          timeShiftSchwartzNPoint (d := d) t f.1))‖ < ε := by
  classical
  let u := osiiOriginalOSNonnegativeTimeShiftSource f
  let D (s t : ℝ≥0) := ‖rToEReflectedPairing Wfn (u s - u t) (u s - u t)‖
  have hu : Continuous u := continuous_osiiOriginalOSNonnegativeTimeShiftSource f
  have hD (t : ℝ≥0) : Continuous (fun s => D s t) :=
    ((continuous_rToEReflectedPairing Wfn n n).comp
      ((hu.sub continuous_const).prodMk (hu.sub continuous_const))).norm
  have hzero (t : ℝ≥0) : D t t = 0 := by
    simp only [D, sub_self, rToEReflectedPairing_apply]
    simp [wickRotatedBoundaryPairing, SchwartzNPoint.osConjTensorProduct]
  obtain ⟨T, hT, htail⟩ := rToE_reflected_timeShift_cauchy_tail Wfn f ε hε
  let U (t : ℝ≥0) := {s : ℝ≥0 | D s t < ε}
  have hU (t : ℝ≥0) : IsOpen (U t) := isOpen_lt (hD t) continuous_const
  have hcover : Icc (0 : ℝ≥0) ⟨T, hT⟩ ⊆ ⋃ t, U t := by
    intro s _
    refine mem_iUnion.mpr ⟨s, ?_⟩
    change D s s < ε
    rwa [hzero]
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) ⟨T, hT⟩)).elim_finite_subcover U hU hcover
  refine ⟨insert ⟨T, hT⟩ K, fun s => ?_⟩
  by_cases hs : s.1 ≤ T
  · have hsK := hK ⟨s.2, hs⟩
    simp only [mem_iUnion] at hsK
    obtain ⟨t, htK, ht⟩ := hsK
    refine ⟨t, Finset.mem_insert_of_mem htK, ?_⟩
    change ‖rToEReflectedPairing Wfn
      (osiiOriginalOSNonnegativeTimeShiftSource f s -
        osiiOriginalOSNonnegativeTimeShiftSource f t)
      (osiiOriginalOSNonnegativeTimeShiftSource f s -
        osiiOriginalOSNonnegativeTimeShiftSource f t)‖ < ε at ht
    rw [rToEReflectedPairing_apply] at ht
    exact ht
  · exact ⟨⟨T, hT⟩, Finset.mem_insert_self _ _, htail s T (le_of_not_ge hs) le_rfl⟩

private def spatialTranslate {n : ℕ} (a : Fin d → ℝ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨translateSchwartzNPoint (Fin.cons 0 a) f.1,
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (Fin.cons 0 a) (by simp) f.1 f.2⟩

private def timeSpacePair (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (a : Fin d → ℝ) : ℂ :=
  rToEReflectedPairing Wfn (osiiOriginalOSNonnegativeTimeShiftSource f s)
    (spatialTranslate a (osiiOriginalOSNonnegativeTimeShiftSource g t))

private theorem scalar_timeShift (Wfn : WightmanFunctions d) {n : ℕ}
    (f : SchwartzNPoint d n) (t : ℝ) :
    wickRotatedBoundaryPairing Wfn n (timeShiftSchwartzNPoint (d := d) t f) =
      wickRotatedBoundaryPairing Wfn n f := by
  symm
  apply wickRotatedBoundaryPairing_translation_invariant Wfn n (-timeShiftVec d t)
  intro x
  change (timeShiftSchwartzNPoint (d := d) t f) x = f (fun i => x i + -timeShiftVec d t)
  simp only [timeShiftSchwartzNPoint_apply, sub_eq_add_neg]

private theorem timeSpacePair_cluster (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (s t : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : Fin d → ℝ, (∑ i, (a i)^2) > R^2 →
      ‖timeSpacePair Wfn f g s t a -
        starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) *
          wickRotatedBoundaryPairing Wfn m g.1‖ < ε := by
  simpa only [timeSpacePair, rToEReflectedPairing_apply, spatialTranslate,
    osiiOriginalOSNonnegativeTimeShiftSource, scalar_timeShift] using
    rToE_reflected_cluster Wfn (osiiOriginalOSNonnegativeTimeShiftSource f s)
      (osiiOriginalOSNonnegativeTimeShiftSource g t) ε hε

private theorem timeSpacePair_uniform_approximation (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s s' t t' : ℝ≥0,
      ‖rToEReflectedPairing Wfn
        (osiiOriginalOSNonnegativeTimeShiftSource f s -
          osiiOriginalOSNonnegativeTimeShiftSource f s')
        (osiiOriginalOSNonnegativeTimeShiftSource f s -
          osiiOriginalOSNonnegativeTimeShiftSource f s')‖ < δ →
      ‖rToEReflectedPairing Wfn
        (osiiOriginalOSNonnegativeTimeShiftSource g t -
          osiiOriginalOSNonnegativeTimeShiftSource g t')
        (osiiOriginalOSNonnegativeTimeShiftSource g t -
          osiiOriginalOSNonnegativeTimeShiftSource g t')‖ < δ →
      ∀ a : Fin d → ℝ,
        ‖timeSpacePair Wfn f g s t a - timeSpacePair Wfn f g s' t' a‖ < ε := by
  let C := ‖rToEReflectedPairing Wfn f f‖ + ‖rToEReflectedPairing Wfn g g‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := (ε / 2) ^ 2 / C
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (by linarith)) hC
  have hδC : δ * C = (ε / 2) ^ 2 := div_mul_cancel₀ _ (ne_of_gt hC)
  refine ⟨δ, hδ, fun s s' t t' hf hg a => ?_⟩
  let fs := osiiOriginalOSNonnegativeTimeShiftSource f s
  let fs' := osiiOriginalOSNonnegativeTimeShiftSource f s'
  let gt := osiiOriginalOSNonnegativeTimeShiftSource g t
  let gt' := osiiOriginalOSNonnegativeTimeShiftSource g t'
  let df := fs - fs'
  let dg := gt - gt'
  let L := rToEReflectedPairing Wfn df (spatialTranslate a gt)
  let H := rToEReflectedPairing Wfn fs' (spatialTranslate a dg)
  have hL : ‖L‖ ^ 2 ≤
      ‖rToEReflectedPairing Wfn df df‖ * ‖rToEReflectedPairing Wfn g g‖ := by
    have hbound := rToE_reflected_timeSpaceShift_pairing_bound Wfn df g 0 t
      (by norm_num) t.2 a
    rw [osiiOriginalOSTimeShiftSchwartzNPoint_zero] at hbound
    dsimp only [L]
    rw [rToEReflectedPairing_apply]
    set_option backward.isDefEq.respectTransparency false in
      simpa only [spatialTranslate, gt, osiiOriginalOSNonnegativeTimeShiftSource] using hbound
  have hH : ‖H‖ ^ 2 ≤
      ‖rToEReflectedPairing Wfn f f‖ * ‖rToEReflectedPairing Wfn dg dg‖ := by
    have hbound := rToE_reflected_timeSpaceShift_pairing_bound Wfn f dg s' 0 s'.2
      (by norm_num) a
    rw [osiiOriginalOSTimeShiftSchwartzNPoint_zero] at hbound
    dsimp only [H]
    rw [rToEReflectedPairing_apply]
    set_option backward.isDefEq.respectTransparency false in
      simpa only [spatialTranslate, fs', osiiOriginalOSNonnegativeTimeShiftSource] using hbound
  have hsmall (x b : ℝ) (hx0 : 0 ≤ x) (hx : x < δ) (hb : b ≤ C) :
      x * b < (ε / 2) ^ 2 := by
    calc
      x * b ≤ x * C := mul_le_mul_of_nonneg_left hb hx0
      _ < δ * C := mul_lt_mul_of_pos_right hx hC
      _ = _ := hδC
  have hLf := hsmall _ _ (norm_nonneg _) hf
    (show ‖rToEReflectedPairing Wfn g g‖ ≤ C by
      dsimp [C]; linarith [norm_nonneg (rToEReflectedPairing Wfn f f)])
  have hHg := hsmall _ _ (norm_nonneg _) hg
    (show ‖rToEReflectedPairing Wfn f f‖ ≤ C by
      dsimp [C]; linarith [norm_nonneg (rToEReflectedPairing Wfn g g)])
  have hLn : ‖L‖ < ε / 2 := by
    change ‖rToEReflectedPairing Wfn df df‖ * _ < _ at hLf
    nlinarith [norm_nonneg L]
  have hHn : ‖H‖ < ε / 2 := by
    change ‖rToEReflectedPairing Wfn dg dg‖ * _ < _ at hHg
    nlinarith [norm_nonneg H]
  have hsub : spatialTranslate a (gt - gt') =
      spatialTranslate a gt - spatialTranslate a gt' := by
    apply Subtype.ext
    exact map_sub _ _ _
  have heq : timeSpacePair Wfn f g s t a - timeSpacePair Wfn f g s' t' a = L + H := by
    dsimp only [timeSpacePair, L, H, df, dg]
    rw [rToEReflectedPairing_sub_left, hsub, rToEReflectedPairing_sub_right]
    dsimp only [fs, fs', gt, gt']
    ring
  rw [heq]
  exact (norm_add_le L H).trans_lt (by linarith)

/-- Reflected clustering is uniform in both nonnegative time shifts and all
spatial separation directions. The sources remain arbitrary ordered Schwartz
functions; this is not yet the arbitrary-zero-diagonal E4 extension. -/
theorem rToE_reflected_cluster_uniform_time (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ∀ a : Fin d → ℝ, (∑ i, (a i)^2) > R^2 →
        ‖wickRotatedBoundaryPairing Wfn (n + m)
          ((timeShiftSchwartzNPoint (d := d) s f.1).osConjTensorProduct
            (translateSchwartzNPoint (Fin.cons 0 a)
              (timeShiftSchwartzNPoint (d := d) t g.1))) -
          starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) *
            wickRotatedBoundaryPairing Wfn m g.1‖ < ε := by
  classical
  obtain ⟨δ, hδ, happ⟩ := timeSpacePair_uniform_approximation Wfn f g
    (ε / 2) (by linarith)
  obtain ⟨K, hK⟩ := rToE_reflected_timeShift_finite_approximation Wfn f δ hδ
  obtain ⟨L, hL⟩ := rToE_reflected_timeShift_finite_approximation Wfn g δ hδ
  choose r hr hc using fun p : ℝ≥0 × ℝ≥0 =>
    timeSpacePair_cluster Wfn f g p.1 p.2 (ε / 2) (by linarith)
  let radius (p : ℝ≥0 × ℝ≥0) : ℝ≥0 := ⟨r p, (hr p).le⟩
  let M := (K ×ˢ L).sup radius
  let R : ℝ := M + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun s t hs ht a ha => ?_⟩
  let ss : ℝ≥0 := ⟨s, hs⟩
  let tt : ℝ≥0 := ⟨t, ht⟩
  obtain ⟨s', hs'K, hs'⟩ := hK ss
  obtain ⟨t', ht'L, ht'⟩ := hL tt
  have hfs :
      ‖rToEReflectedPairing Wfn
        (osiiOriginalOSNonnegativeTimeShiftSource f ss -
          osiiOriginalOSNonnegativeTimeShiftSource f s')
        (osiiOriginalOSNonnegativeTimeShiftSource f ss -
          osiiOriginalOSNonnegativeTimeShiftSource f s')‖ < δ := by
    rw [rToEReflectedPairing_apply]
    exact hs'
  have hgt :
      ‖rToEReflectedPairing Wfn
        (osiiOriginalOSNonnegativeTimeShiftSource g tt -
          osiiOriginalOSNonnegativeTimeShiftSource g t')
        (osiiOriginalOSNonnegativeTimeShiftSource g tt -
          osiiOriginalOSNonnegativeTimeShiftSource g t')‖ < δ := by
    rw [rToEReflectedPairing_apply]
    exact ht'
  have hnear := happ ss s' tt t' hfs hgt a
  have hp : (s', t') ∈ K ×ˢ L := Finset.mem_product.mpr ⟨hs'K, ht'L⟩
  have hrM : r (s', t') ≤ (M : ℝ) :=
    show (radius (s', t') : ℝ) ≤ (M : ℝ) from Finset.le_sup (f := radius) hp
  have hrR : r (s', t') ≤ R := by dsimp [R]; linarith
  have hsep : (∑ i, (a i)^2) > (r (s', t'))^2 := by
    have hsq : (r (s', t'))^2 ≤ R^2 := by
      simpa only [pow_two] using mul_self_le_mul_self (hr (s', t')).le hrR
    exact hsq.trans_lt ha
  have hfar := hc (s', t') a hsep
  let z := starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) *
    wickRotatedBoundaryPairing Wfn m g.1
  have htriangle := dist_triangle (timeSpacePair Wfn f g ss tt a)
    (timeSpacePair Wfn f g s' t' a) z
  simp only [dist_eq_norm] at htriangle
  have hfinal : ‖timeSpacePair Wfn f g ss tt a - z‖ < ε := by
    dsimp [z] at htriangle ⊢
    linarith
  simpa only [timeSpacePair, rToEReflectedPairing_apply, spatialTranslate,
    osiiOriginalOSNonnegativeTimeShiftSource, ss, tt, z] using hfinal

end OSReconstruction
