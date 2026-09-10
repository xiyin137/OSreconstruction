/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIReducedForwardTubePaleyWiener
import OSReconstruction.Wightman.SpectralEquivalence
import Mathlib.Analysis.Distribution.Support








noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- A point outside the closed forward cone is separated by an open-forward
Euclidean covector. This is the finite-dimensional self-duality calculation
used by the distributional support theorem below. -/
private lemma exists_openForwardCone_pairing_neg_of_not_mem_forwardMomentumCone'
    (d : Nat) [NeZero d]
    {p : Fin (d + 1) -> Real}
    (hp : p ∉ ForwardMomentumCone d) :
    ∃ y : Fin (d + 1) -> Real,
      InOpenForwardCone d y ∧ euclideanDot y p < 0 := by
  simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
    MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
    MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent,
    not_and_or, not_le] at hp
  rcases hp with hncausal | htime
  · by_cases hp0 : p 0 < 0
    · refine ⟨fun i => if i = 0 then (1 : Real) else 0, ?_, ?_⟩
      · constructor
        · simp
        · rw [MinkowskiSpace.minkowskiNormSq_decomp]
          simp [MinkowskiSpace.spatialNormSq, Fin.succ_ne_zero]
      · simp [euclideanDot, hp0]
    · push Not at hp0
      have hpσ : (p 0) ^ 2 < MinkowskiSpace.spatialNormSq d p := by
        have h_decomp := MinkowskiSpace.minkowskiNormSq_decomp d p
        linarith
      set σ := MinkowskiSpace.spatialNormSq d p with hσ_def
      have hσ_pos : (0 : Real) < σ := by
        linarith [sq_nonneg (p 0)]
      set s := Real.sqrt σ with hs_def
      have hs_gt : s > p 0 := by
        calc
          p 0 ≤ |p 0| := le_abs_self _
          _ = Real.sqrt ((p 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ < Real.sqrt σ := Real.sqrt_lt_sqrt (sq_nonneg _) hpσ
      set r : Fin d -> Real := fun i => -(s + p 0) / (2 * σ) * p (Fin.succ i)
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
      have hr_sq_sum :
          ∑ i : Fin d, (r i) ^ 2 = (s + p 0) ^ 2 / (4 * σ) := by
        simp only [r, mul_pow, div_pow]
        rw [← Finset.mul_sum]
        have hσ_eq : ∑ i : Fin d, (p (Fin.succ i)) ^ 2 = σ := by
          simp [hσ_def, MinkowskiSpace.spatialNormSq]
        rw [hσ_eq]
        field_simp [hσ_ne]
        ring
      have hr_sum_lt : ∑ i : Fin d, (r i) ^ 2 < 1 := by
        rw [hr_sq_sum]
        rw [div_lt_one (by positivity)]
        have hs_lt : s + p 0 < 2 * s := by linarith
        have hs_pos : 0 < s := Real.sqrt_pos_of_pos hσ_pos
        have hs_sq : s ^ 2 = σ := by
          rw [hs_def]
          exact Real.sq_sqrt hσ_pos.le
        nlinarith
      have hr_dot :
          p 0 + ∑ i : Fin d, r i * p (Fin.succ i) = (p 0 - s) / 2 := by
        simp only [r]
        have hsum :
            ∀ i : Fin d,
              -(s + p 0) / (2 * σ) * p (Fin.succ i) * p (Fin.succ i) =
                -(s + p 0) / (2 * σ) * (p (Fin.succ i) * p (Fin.succ i)) := by
          intro i
          ring
        simp_rw [hsum, ← Finset.mul_sum]
        have hσ_eq :
            ∑ i : Fin d, p (Fin.succ i) * p (Fin.succ i) = σ := by
          simp [hσ_def, MinkowskiSpace.spatialNormSq, sq]
        rw [hσ_eq]
        field_simp [hσ_ne]
        ring
      have hr_dot_neg : p 0 + ∑ i : Fin d, r i * p (Fin.succ i) < 0 := by
        rw [hr_dot]
        linarith
      let y : Fin (d + 1) -> Real := fun i => if h : i = 0 then 1 else r (i.pred h)
      have hy_mem : InOpenForwardCone d y := by
        constructor
        · simp [y]
        · have hmink :
            MinkowskiSpace.minkowskiNormSq d y = -1 + ∑ i : Fin d, (r i) ^ 2 := by
            rw [MinkowskiSpace.minkowskiNormSq_decomp]
            simp [MinkowskiSpace.spatialNormSq, y, Fin.succ_ne_zero]
          linarith
      have hy_neg : euclideanDot y p < 0 := by
        rw [euclideanDot, Fin.sum_univ_succ]
        simp [y, Fin.succ_ne_zero]
        rw [hr_dot]
        linarith
      exact ⟨y, hy_mem, hy_neg⟩
  · refine ⟨fun i => if i = 0 then (1 : Real) else 0, ?_, ?_⟩
    · constructor
      · simp
      · rw [MinkowskiSpace.minkowskiNormSq_decomp]
        simp [MinkowskiSpace.spatialNormSq, Fin.succ_ne_zero]
    · simp [euclideanDot, htime]

/-- The closed forward cone is exactly the Euclidean dual of the open
forward cone. -/
theorem mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg
    (p : Fin (d + 1) -> Real) :
    p ∈ ForwardMomentumCone d ↔
      ∀ y : Fin (d + 1) -> Real,
        InOpenForwardCone d y -> 0 ≤ euclideanDot y p := by
  constructor
  · intro hp y hy
    apply euclideanDot_nonneg_closedCone y
    · simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
        MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
        MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent]
      exact ⟨le_of_lt hy.2, le_of_lt hy.1⟩
    · exact hp
  · intro h
    by_contra hp
    obtain ⟨y, hy, hneg⟩ :=
      exists_openForwardCone_pairing_neg_of_not_mem_forwardMomentumCone' d hp
    linarith [h y hy]

/-- Extract one particle momentum block from canonical flat particle-block
frequency coordinates. -/
def osiiCanonicalFrequencyParticleBlock
    (d k : Nat) (p : Fin (k * (d + 1)) -> Real) (j : Fin k) :
    Fin (d + 1) -> Real :=
  fun μ => p (finProdFinEquiv (j, μ))

/-- The product closed forward cone in canonical flat particle-block
frequency coordinates. -/
def osiiCanonicalFrequencyProductForwardCone (d k : Nat) [NeZero d] :
    Set (Fin (k * (d + 1)) -> Real) :=
  {p | ∀ j : Fin k,
    osiiCanonicalFrequencyParticleBlock d k p j ∈ ForwardMomentumCone d}

/-- One Lorentz-tilted positive-energy halfspace for a particle block. -/
def osiiCanonicalFrequencyForwardPairingHalfspace
    (d k : Nat) [NeZero d]
    (j : Fin k) (y : Fin (d + 1) -> Real) :
    Set (Fin (k * (d + 1)) -> Real) :=
  {p | 0 ≤ euclideanDot y (osiiCanonicalFrequencyParticleBlock d k p j)}

theorem isClosed_osiiCanonicalFrequencyForwardPairingHalfspace
    (j : Fin k) (y : Fin (d + 1) -> Real) :
    IsClosed (osiiCanonicalFrequencyForwardPairingHalfspace d k j y) := by
  unfold osiiCanonicalFrequencyForwardPairingHalfspace
  exact isClosed_le continuous_const (by
    unfold euclideanDot osiiCanonicalFrequencyParticleBlock
    fun_prop)

/-- Distributional support in every open-forward pairing halfspace implies
support in the product closed forward cone. -/
theorem dsupport_subset_osiiCanonicalFrequencyProductForwardCone_of_vanishing
    (T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex)
    (hT : ∀ (j : Fin k) (y : Fin (d + 1) -> Real),
      InOpenForwardCone d y ->
      Distribution.IsVanishingOn T
        (osiiCanonicalFrequencyForwardPairingHalfspace d k j y)ᶜ) :
    Distribution.dsupport T ⊆
      osiiCanonicalFrequencyProductForwardCone d k := by
  intro p hp j
  rw [mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg]
  intro y hy
  have hp_halfspace :
      p ∈ osiiCanonicalFrequencyForwardPairingHalfspace d k j y := by
    rw [Distribution.mem_dsupport_iff] at hp
    exact hp _
      (hT j y hy)
      (isClosed_osiiCanonicalFrequencyForwardPairingHalfspace (d := d) (k := k) j y)
  exact hp_halfspace

omit [NeZero d] in
/-- Flattening preserves the ordinary Euclidean pairing, splitting it into
the individual particle-block pairings. -/
private theorem osiiCanonicalFrequency_flatten_pairing
    (y : Fin k -> Fin (d + 1) -> Real)
    (p : Fin (k * (d + 1)) -> Real) :
    (∑ i : Fin (k * (d + 1)), BHW.flattenCfgReal k d y i * p i) =
      ∑ j : Fin k,
        euclideanDot (y j) (osiiCanonicalFrequencyParticleBlock d k p j) := by
  calc
    (∑ i : Fin (k * (d + 1)), BHW.flattenCfgReal k d y i * p i) =
        ∑ q : Fin k × Fin (d + 1),
          BHW.flattenCfgReal k d y (finProdFinEquiv q) *
            p (finProdFinEquiv q) := by
      symm
      refine Fintype.sum_equiv finProdFinEquiv
        (fun q => BHW.flattenCfgReal k d y (finProdFinEquiv q) *
          p (finProdFinEquiv q))
        (fun i => BHW.flattenCfgReal k d y i * p i) ?_
      intro q
      rfl
    _ = ∑ q : Fin k × Fin (d + 1), y q.1 q.2 * p (finProdFinEquiv q) := by
      simp [BHW.flattenCfgReal]
    _ = ∑ j : Fin k,
          euclideanDot (y j) (osiiCanonicalFrequencyParticleBlock d k p j) := by
      rw [Fintype.sum_prod_type]
      rfl

/-- The Euclidean dual of the genuine open product forward cone is exactly
the product closed forward cone.  Spectator blocks must remain strictly
timelike; setting them to zero would leave the open product cone. -/
theorem dualConeFlat_osiiReducedForwardFlatCone :
    DualConeFlat (osiiReducedForwardFlatCone d k) =
      osiiCanonicalFrequencyProductForwardCone d k := by
  ext p
  constructor
  · intro hp j
    apply
      (mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg
        (osiiCanonicalFrequencyParticleBlock d k p j)).mpr
    intro v hv
    by_contra hnonneg
    have hvneg :
        euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p j) < 0 :=
      lt_of_not_ge hnonneg
    let A : Real := ∑ l : Fin k,
      if l = j then 0 else osiiCanonicalFrequencyParticleBlock d k p l 0
    obtain ⟨epsilon, hepsilon, hsmall⟩ :=
      exists_pos_mul_abs_lt_of_neg
        (c := A)
        (s := euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p j))
        hvneg
    let y : Fin k -> Fin (d + 1) -> Real :=
      fun l mu => if l = j then v mu else if mu = 0 then epsilon else 0
    have hy : BHW.flattenCfgReal k d y ∈ osiiReducedForwardFlatCone d k := by
      change BHW.unflattenCfgReal k d (BHW.flattenCfgReal k d y) ∈
        BHW.ProductForwardConeReal d k
      rw [BHW.unflatten_flatten_cfg_real]
      intro l
      by_cases hl : l = j
      · have hy_eq : y l = v := by
          funext mu
          simp [y, hl]
        rw [hy_eq]
        rw [InOpenForwardCone] at hv
        exact (inOpenForwardCone_iff (d := d) v).mpr hv
      · have hpublic : InOpenForwardCone d (y l) := by
          constructor
          · simp [y, hl, hepsilon]
          · rw [MinkowskiSpace.minkowskiNormSq_decomp]
            simp [MinkowskiSpace.spatialNormSq, y, hl, Fin.succ_ne_zero]
            have hsquare : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
            linarith
        rw [InOpenForwardCone] at hpublic
        exact (inOpenForwardCone_iff (d := d) (y l)).mpr hpublic
    have hpair_nonneg := hp (BHW.flattenCfgReal k d y) hy
    rw [osiiCanonicalFrequency_flatten_pairing] at hpair_nonneg
    have hpair :
        (∑ l : Fin k,
          euclideanDot (y l) (osiiCanonicalFrequencyParticleBlock d k p l)) =
          euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p j) +
            epsilon * A := by
      have hterm : ∀ l : Fin k,
          euclideanDot (y l) (osiiCanonicalFrequencyParticleBlock d k p l) =
            if l = j then
              euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p l)
            else epsilon * osiiCanonicalFrequencyParticleBlock d k p l 0 := by
        intro l
        by_cases hl : l = j
        · simp [y, hl, euclideanDot]
        · simp [y, hl, euclideanDot]
      rw [Finset.sum_congr rfl (fun l _ => hterm l)]
      have hsplit : ∀ l : Fin k,
          (if l = j then
            euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p l)
          else epsilon * osiiCanonicalFrequencyParticleBlock d k p l 0) =
            (if l = j then
              euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p l)
            else 0) +
            (if l = j then 0
            else epsilon * osiiCanonicalFrequencyParticleBlock d k p l 0) := by
        intro l
        by_cases hl : l = j <;> simp [hl]
      rw [Finset.sum_congr rfl (fun l _ => hsplit l), Finset.sum_add_distrib]
      rw [show
          (∑ l : Fin k, if l = j then
            euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p l)
          else 0) =
            euclideanDot v (osiiCanonicalFrequencyParticleBlock d k p j) by
        simp [Finset.sum_ite_eq']]
      congr 1
      dsimp [A]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l = j <;> simp [hl]
    rw [hpair] at hpair_nonneg
    have hA : epsilon * A ≤ epsilon * |A| :=
      mul_le_mul_of_nonneg_left (le_abs_self A) hepsilon.le
    linarith
  · intro hp y hy
    let eta := BHW.unflattenCfgReal k d y
    have heta : eta ∈ BHW.ProductForwardConeReal d k := hy
    have hy_eq : y = BHW.flattenCfgReal k d eta := by
      exact (BHW.flatten_unflatten_cfg_real k d y).symm
    rw [hy_eq, osiiCanonicalFrequency_flatten_pairing]
    apply Finset.sum_nonneg
    intro j _
    apply
      (mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg
        (osiiCanonicalFrequencyParticleBlock d k p j)).mp (hp j)
    rw [InOpenForwardCone]
    exact (inOpenForwardCone_iff (d := d) (eta j)).mp (heta j)

/-- The production Fourier-support predicate for the reduced tube refers
exactly to pointwise support away from the closed product forward cone. -/
theorem hasFourierSupportInDualCone_osiiReducedForwardFlatCone_iff
    (T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex) :
    HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k) T ↔
      ∀ phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex,
        (∀ p ∈ Function.support
          (phi : (Fin (k * (d + 1)) -> Real) -> Complex),
          p ∉ osiiCanonicalFrequencyProductForwardCone d k) ->
        T phi = 0 := by
  rw [HasFourierSupportInDualCone, dualConeFlat_osiiReducedForwardFlatCone]
  rfl

end OSReconstruction
