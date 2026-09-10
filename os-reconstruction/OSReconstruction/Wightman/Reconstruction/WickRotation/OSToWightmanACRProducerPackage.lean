/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerTemperedness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import Init
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.SCV.DistributionalEOWKernel
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.SCV.ConeDefs
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv









noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal

variable {d k : ℕ} [NeZero d]

/-- The analytic and OS-symmetry core of a simultaneous ACR(1) producer. -/
structure ACROneAnalyticCore
    (OS : OsterwalderSchraderAxioms d) (k : ℕ) where
  toFun : (Fin k → Fin (d + 1) → ℂ) → ℂ
  holomorphic :
    DifferentiableOn ℂ toFun (AnalyticContinuationRegion d k 1)
  reproducesProductTensor :
    ∀ (fs : Fin k → SchwartzSpacetime d)
      (hvanish : VanishesToInfiniteOrderOnCoincidence
        (SchwartzMap.productTensor fs)),
      OS.S k ⟨SchwartzMap.productTensor fs, hvanish⟩ =
        ∫ x : NPointDomain d k,
          toFun (fun j => wickRotatePoint (x j)) *
            (SchwartzMap.productTensor fs) x
  perm_invariant :
    ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
      toFun (fun j => z (σ j)) = toFun z
  translation_invariant :
    ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
      toFun (fun j => z j + a) = toFun z
  negCanonical :
    ∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
      starRingEnd ℂ
        (toFun (fun j μ =>
          ↑(x j μ) +
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
      toFun (fun j μ =>
        ↑(x j μ) -
          ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)

namespace ReducedACROneAnalyticCore

end ReducedACROneAnalyticCore

/-- Coincidence-weighted Euclidean control for a candidate scalar kernel,
before the OS identities have been assembled into an analytic core.

The dense product-tensor argument needs this estimate in order to construct
the continuous zero-diagonal pairing that proves `reproducesProductTensor`;
keeping the datum at function level avoids making that argument circular. -/
structure ACROneEuclideanWeightedKernelData
    {d k : ℕ} [NeZero d]
    (S : (Fin k → Fin (d + 1) → ℂ) → ℂ) where
  C_bd : ℝ
  N : ℕ
  q : ℕ
  C_bd_pos : 0 < C_bd
  measurable :
    AEStronglyMeasurable
      (fun x : NPointDomain d k =>
        S (fun j => wickRotatePoint (x j)))
      volume
  weighted_bound :
    ∀ᵐ x : NPointDomain d k ∂volume,
      ‖S (fun j => wickRotatePoint (x j))‖ *
          Metric.infDist x (CoincidenceLocus d k) ^ (q + 1) ≤
        C_bd * (1 + ‖x‖) ^ N

/-- The coincidence-weighted Euclidean estimate needed on the zero-diagonal
Schwartz space. -/
structure ACROneEuclideanWeightedControl
    {OS : OsterwalderSchraderAxioms d} {k : ℕ}
    (P : ACROneAnalyticCore (d := d) OS k) where
  C_bd : ℝ
  N : ℕ
  q : ℕ
  C_bd_pos : 0 < C_bd
  measurable :
    AEStronglyMeasurable
      (fun x : NPointDomain d k =>
        P.toFun (fun j => wickRotatePoint (x j)))
      volume
  weighted_bound :
    ∀ᵐ x : NPointDomain d k ∂volume,
      ‖P.toFun (fun j => wickRotatePoint (x j))‖ *
          Metric.infDist x (CoincidenceLocus d k) ^ (q + 1) ≤
        C_bd * (1 + ‖x‖) ^ N

/-- Forget the already assembled OS fields and retain only the weighted
kernel estimate. -/
def ACROneEuclideanWeightedControl.toKernelData
    {OS : OsterwalderSchraderAxioms d}
    {P : ACROneAnalyticCore (d := d) OS k}
    (E : ACROneEuclideanWeightedControl P) :
    ACROneEuclideanWeightedKernelData P.toFun where
  C_bd := E.C_bd
  N := E.N
  q := E.q
  C_bd_pos := E.C_bd_pos
  measurable := E.measurable
  weighted_bound := E.weighted_bound

namespace ACROneForwardTubeControl

end ACROneForwardTubeControl

namespace ReducedACROneProducerPackage

end ReducedACROneProducerPackage

namespace OSReconstruction

namespace OSIIReducedACROneRecoveredFlatKernel

end OSIIReducedACROneRecoveredFlatKernel

namespace OSIIReducedACROneMZPatchData

end OSIIReducedACROneMZPatchData

end OSReconstruction

set_option maxHeartbeats 400000 in
/-- A coincidence-weighted polynomial estimate makes integration against the
kernel continuous on the zero-diagonal Schwartz space. -/
theorem zeroDiagonal_integral_continuous_of_ae_infDist_mul_pow_le_polynomial
    {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (m M : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty)
    (C_bd : ℝ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d n ∂volume,
      ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) ≤
        C_bd * (1 + ‖x‖) ^ M) :
    Continuous
      (fun f : ZeroDiagonalSchwartz d n =>
        ∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x) := by
  have hWS : WithSeminorms
      ((schwartzSeminormFamily ℂ (NPointDomain d n) ℂ).comp
        (zeroDiagonalSubmodule d n).subtype) :=
    Topology.IsInducing.withSeminorms
      (schwartz_withSeminorms (𝕜 := ℂ) (E := NPointDomain d n) (F := ℂ))
      Topology.IsInducing.subtypeVal
  have hlin : IsLinearMap ℂ
      (fun f : ZeroDiagonalSchwartz d n =>
        ∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x) := by
    constructor
    · intro f g
      have hf_int :=
        kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
          K hK_meas f m M hcoin C_bd hC.le hK_bound
      have hg_int :=
        kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
          K hK_meas g m M hcoin C_bd hC.le hK_bound
      have heq :
          (fun x : NPointDomain d n =>
            K x * ((f + g).1 : NPointDomain d n → ℂ) x) =
          fun x => K x * (f.1 : NPointDomain d n → ℂ) x +
            K x * (g.1 : NPointDomain d n → ℂ) x := by
        ext x
        change K x * (f.1 x + g.1 x) = _
        ring
      rw [heq]
      exact integral_add hf_int hg_int
    · intro c f
      have heq :
          (fun x : NPointDomain d n =>
            K x * ((c • f).1 : NPointDomain d n → ℂ) x) =
          fun x => c • (K x * (f.1 : NPointDomain d n → ℂ) x) := by
        ext x
        change K x * (c * f.1 x) = c * (K x * f.1 x)
        ring
      rw [heq]
      exact integral_smul c _
  let T : ZeroDiagonalSchwartz d n →ₗ[ℂ] ℂ := hlin.mk'
  change Continuous T
  let D : ℕ := Module.finrank ℝ (NPointDomain d n)
  let degree : ℕ := M + D + m + 2
  have hD_lt : (D : ℝ) < ↑(D + 1) := by
    push_cast
    linarith
  have htail_int :
      Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        volume :=
    integrable_one_add_norm hD_lt
  let I_tail : ℝ :=
    ∫ x : NPointDomain d n, (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ))
  have hI_tail_nonneg : 0 ≤ I_tail :=
    integral_nonneg fun x => Real.rpow_nonneg (by linarith [norm_nonneg x]) _
  let vanishFactor : ℝ := 2 ^ (degree + m + 1) / (Nat.factorial m : ℝ)
  let boundValue : ℝ := C_bd * vanishFactor * I_tail
  have hboundValue_nonneg : 0 ≤ boundValue := by
    positivity
  let boundNN : NNReal := ⟨boundValue, hboundValue_nonneg⟩
  apply Seminorm.cont_withSeminorms_normedSpace ℂ hWS T
  refine ⟨Finset.Iic (degree, m + 1), boundNN, ?_⟩
  rw [Seminorm.le_def]
  intro f
  let sem :=
    ((Finset.Iic (degree, m + 1)).sup
      (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)) f.1
  have hvanish :
      ∀ x : NPointDomain d n,
        (1 + ‖x‖) ^ degree * ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
          vanishFactor * sem *
            Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) :=
    VanishesToInfiniteOrderOnCoincidence.weighted_infDist_bound_explicit
      (f := f.1) f.2 degree m hcoin
  have hpointwise :
      ∀ᵐ x : NPointDomain d n ∂volume,
        ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ ≤
          C_bd * vanishFactor * sem *
            (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
    filter_upwards [hK_bound] with x hx
    let delta : ℝ := Metric.infDist x (CoincidenceLocus d n)
    have hdelta_nonneg : 0 ≤ delta := Metric.infDist_nonneg
    have hf_weighted :
        (1 + ‖x‖) ^ degree * ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
          vanishFactor * sem * delta ^ (m + 1) := by
      simpa [delta] using hvanish x
    have hbase_pos : 0 < 1 + ‖x‖ := by
      linarith [norm_nonneg x]
    rw [Real.rpow_neg hbase_pos.le, Real.rpow_natCast, norm_mul]
    by_cases hdelta : delta = 0
    · have hfx : ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 := by
        have hdegree_pos : 0 < (1 + ‖x‖) ^ degree := pow_pos hbase_pos _
        have hzero :
            (1 + ‖x‖) ^ degree *
                ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 := by
          have := hf_weighted
          simp [hdelta] at this
          exact le_antisymm this
            (mul_nonneg hdegree_pos.le (norm_nonneg _))
        exact (mul_eq_zero.mp hzero).resolve_left hdegree_pos.ne'
      simp [hfx]
      positivity
    · have hdelta_pos : 0 < delta :=
        lt_of_le_of_ne hdelta_nonneg (Ne.symm hdelta)
      have hdeltaPow_pos : 0 < delta ^ (m + 1) := pow_pos hdelta_pos _
      have hdegree_pos : 0 < (1 + ‖x‖) ^ degree := pow_pos hbase_pos _
      have hK :
          ‖K x‖ ≤
            C_bd * (1 + ‖x‖) ^ M / delta ^ (m + 1) := by
        rw [le_div_iff₀ hdeltaPow_pos]
        simpa [delta, mul_comm, mul_left_comm, mul_assoc] using hx
      have hf :
          ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
            vanishFactor * sem * delta ^ (m + 1) /
              (1 + ‖x‖) ^ degree := by
        rw [le_div_iff₀ hdegree_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hf_weighted
      have hdegree : degree = M + (D + m + 2) := by
        omega
      have hpow :
          (1 + ‖x‖) ^ (D + 1) ≤
            (1 + ‖x‖) ^ (D + m + 2) :=
        pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
      calc
        ‖K x‖ * ‖(f.1 : NPointDomain d n → ℂ) x‖
            ≤
          (C_bd * (1 + ‖x‖) ^ M / delta ^ (m + 1)) *
            (vanishFactor * sem * delta ^ (m + 1) /
              (1 + ‖x‖) ^ degree) := by gcongr
        _ =
            C_bd * vanishFactor * sem /
              (1 + ‖x‖) ^ (D + m + 2) := by
              rw [hdegree, pow_add]
              field_simp [pow_pos hbase_pos, hdeltaPow_pos.ne']
              ring
        _ ≤
            C_bd * vanishFactor * sem /
              (1 + ‖x‖) ^ (D + 1) := by
              exact div_le_div_of_nonneg_left
                (by positivity) (pow_pos hbase_pos _) hpow
        _ =
            C_bd * vanishFactor * sem *
              ((1 + ‖x‖) ^ (D + 1))⁻¹ := by
              field_simp
  have hdom_int :
      Integrable
        (fun x : NPointDomain d n =>
          C_bd * vanishFactor * sem *
            (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        volume :=
    htail_int.const_mul (C_bd * vanishFactor * sem)
  have hintegrable :=
    kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
      K hK_meas f m M hcoin C_bd hC.le hK_bound
  have hint :
      ‖∫ x : NPointDomain d n,
          K x * (f.1 : NPointDomain d n → ℂ) x‖ ≤
        boundValue * sem := by
    calc
      ‖∫ x : NPointDomain d n,
          K x * (f.1 : NPointDomain d n → ℂ) x‖
          ≤ ∫ x : NPointDomain d n,
              ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : NPointDomain d n,
          C_bd * vanishFactor * sem *
            (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) :=
        integral_mono_ae hintegrable.norm hdom_int hpointwise
      _ = C_bd * vanishFactor * sem * I_tail := by
        rw [integral_const_mul]
      _ = boundValue * sem := by
        simp only [boundValue]
        ring
  have hsem :
      ((Finset.Iic (degree, m + 1)).sup
        ((schwartzSeminormFamily ℂ (NPointDomain d n) ℂ).comp
          (zeroDiagonalSubmodule d n).subtype)) f = sem := by
    simp only [sem]
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 1
  simp only [Seminorm.coe_comp, Function.comp_apply, normSeminorm,
    Seminorm.smul_apply, NNReal.smul_def]
  rw [hsem]
  exact hint

/-- Function-level weighted data has the exact continuity consequence needed
before product-tensor reproduction has been assembled. -/
theorem ACROneEuclideanWeightedKernelData.pairing_continuous
    {S : (Fin k → Fin (d + 1) → ℂ) → ℂ}
    (E : ACROneEuclideanWeightedKernelData S)
    (hcoin : (CoincidenceLocus d k).Nonempty) :
    Continuous
      (fun f : ZeroDiagonalSchwartz d k =>
        ∫ x : NPointDomain d k,
          S (fun j => wickRotatePoint (x j)) *
            (f.1 : NPointDomain d k → ℂ) x) :=
  zeroDiagonal_integral_continuous_of_ae_infDist_mul_pow_le_polynomial
    (fun x : NPointDomain d k => S (fun j => wickRotatePoint (x j)))
    E.measurable E.q E.N hcoin E.C_bd E.C_bd_pos E.weighted_bound

/-- Function-level weighted data defines the continuous zero-diagonal pairing
used in the pre-completion dense extension. -/
noncomputable def ACROneEuclideanWeightedKernelData.pairingCLM
    {S : (Fin k → Fin (d + 1) → ℂ) → ℂ}
    (E : ACROneEuclideanWeightedKernelData S)
    (hcoin : (CoincidenceLocus d k).Nonempty) :
    ZeroDiagonalSchwartz d k →L[ℂ] ℂ := by
  let K : NPointDomain d k → ℂ :=
    fun x => S (fun j => wickRotatePoint (x j))
  let L : ZeroDiagonalSchwartz d k →ₗ[ℂ] ℂ :=
    { toFun := fun f =>
        ∫ x : NPointDomain d k, K x * (f.1 : NPointDomain d k → ℂ) x
      map_add' := by
        intro f g
        have hf_int :=
          kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
            K E.measurable f E.q E.N hcoin E.C_bd E.C_bd_pos.le
              E.weighted_bound
        have hg_int :=
          kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
            K E.measurable g E.q E.N hcoin E.C_bd E.C_bd_pos.le
              E.weighted_bound
        have heq :
            (fun x : NPointDomain d k =>
              K x * ((f + g).1 : NPointDomain d k → ℂ) x) =
            fun x =>
              K x * (f.1 : NPointDomain d k → ℂ) x +
                K x * (g.1 : NPointDomain d k → ℂ) x := by
          ext x
          change K x * (f.1 x + g.1 x) = _
          ring
        rw [heq]
        exact integral_add hf_int hg_int
      map_smul' := by
        intro c f
        have heq :
            (fun x : NPointDomain d k =>
              K x * ((c • f).1 : NPointDomain d k → ℂ) x) =
            fun x =>
              c • (K x * (f.1 : NPointDomain d k → ℂ) x) := by
          ext x
          change K x * (c * f.1 x) = c * (K x * f.1 x)
          ring
        rw [heq]
        exact integral_smul c _ }
  exact ContinuousLinearMap.mk L (E.pairing_continuous hcoin)

@[simp] theorem ACROneEuclideanWeightedKernelData.pairingCLM_apply
    {S : (Fin k → Fin (d + 1) → ℂ) → ℂ}
    (E : ACROneEuclideanWeightedKernelData S)
    (hcoin : (CoincidenceLocus d k).Nonempty)
    (f : ZeroDiagonalSchwartz d k) :
    E.pairingCLM hcoin f =
      ∫ x : NPointDomain d k,
        S (fun j => wickRotatePoint (x j)) *
          (f.1 : NPointDomain d k → ℂ) x :=
  rfl

/-- If the candidate kernel reproduces Schwinger on any dense generating
family of zero-diagonal tests, function-level weighted control extends the
identity to every zero-diagonal Schwartz test. -/
theorem ACROneEuclideanWeightedKernelData.reproducesZeroDiagonal_of_eq_on_dense
    (OS : OsterwalderSchraderAxioms d)
    {S : (Fin k → Fin (d + 1) → ℂ) → ℂ}
    (E : ACROneEuclideanWeightedKernelData S)
    (hcoin : (CoincidenceLocus d k).Nonempty)
    {G : Set (ZeroDiagonalSchwartz d k)}
    (hDense :
      Dense
        (((Submodule.span ℂ G :
            Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k))))
    (hEq :
      ∀ f ∈ G,
        OS.S k f =
          ∫ x : NPointDomain d k,
            S (fun j => wickRotatePoint (x j)) *
              (f.1 : NPointDomain d k → ℂ) x) :
    ∀ f : ZeroDiagonalSchwartz d k,
      OS.S k f =
        ∫ x : NPointDomain d k,
          S (fun j => wickRotatePoint (x j)) *
            (f.1 : NPointDomain d k → ℂ) x := by
  let L : ZeroDiagonalSchwartz d k →L[ℂ] ℂ :=
    E.pairingCLM hcoin
  have hL_eq :
      L = OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k := by
    apply ContinuousLinearMap.eq_of_eq_on_dense L
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k) hDense
    intro f hf
    change f ∈ Submodule.span ℂ G at hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro g hg
      rw [show L g = ∫ x : NPointDomain d k,
          S (fun j => wickRotatePoint (x j)) *
            (g.1 : NPointDomain d k → ℂ) x by
        exact E.pairingCLM_apply hcoin g]
      exact (hEq g hg).symm
    · simpa [OsterwalderSchraderAxioms.schwingerCLM] using
        (OS.E0_linear k).map_zero.symm
    · intro u v _ _ hu hv
      simp [hu, hv]
    · intro c u _ hu
      simp [hu]
  intro f
  have h :=
    congrArg
      (fun T : ZeroDiagonalSchwartz d k →L[ℂ] ℂ => T f)
      hL_eq
  simpa [L, E.pairingCLM_apply hcoin f] using h.symm

/-- The post-completion weighted estimate uses the pre-completion pairing
CLM definition. -/
noncomputable def ACROneEuclideanWeightedControl.pairingCLM
    {OS : OsterwalderSchraderAxioms d} {k : ℕ}
    {P : ACROneAnalyticCore (d := d) OS k}
    (E : ACROneEuclideanWeightedControl P)
    (hcoin : (CoincidenceLocus d k).Nonempty) :
    ZeroDiagonalSchwartz d k →L[ℂ] ℂ :=
  E.toKernelData.pairingCLM hcoin

@[simp] theorem ACROneEuclideanWeightedControl.pairingCLM_apply
    {OS : OsterwalderSchraderAxioms d} {k : ℕ}
    {P : ACROneAnalyticCore (d := d) OS k}
    (E : ACROneEuclideanWeightedControl P)
    (hcoin : (CoincidenceLocus d k).Nonempty)
    (f : ZeroDiagonalSchwartz d k) :
    E.pairingCLM hcoin f =
      ∫ x : NPointDomain d k,
        P.toFun (fun j => wickRotatePoint (x j)) *
          (f.1 : NPointDomain d k → ℂ) x :=
  rfl
