import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularContinuation

/-!
# Source-linear physical angular continuation

The scalar physical-angular invariant is sufficient for the final radial
integral, but it is not stable under repeated Malgrange-Zerner steps: after
one successor it forgets the full-Schwartz distribution whose evaluation
produces the scalar radial branch.  The next successor then has no
source-linear predecessor arm.

This file records the lossless invariant.  It retains one distribution-valued
continuation on the current angular carrier, together with its first-carrier
provenance.  The synchronized coherent distribution supplies the initial
object.  Compact subsets of every such continuation have one common finite
Schwartz-seminorm bound, so the invariant carries exactly the quantitative
input needed by the full-Schwartz MZ engine.
-/

noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}

/-- A physical angular continuation which retains its complete
full-Schwartz linearity. -/
structure OSIIStep4FullSchwartzAngularContinuationData
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  carrier : Set (Fin k -> osiiAxisPairIndex d -> Complex)
  carrier_open : IsOpen carrier
  firstCarrier_subset :
    osiiAxisPairMultiGapLogDomain d k ⊆ carrier
  distribution :
    (Fin k -> osiiAxisPairIndex d -> Complex) ->
      SchwartzNPoint d (k + 1) →L[Complex] Complex
  weaklyHolomorphic : forall F,
    DifferentiableOn Complex (fun w => distribution w F) carrier
  continuousOn_joint :
    ContinuousOn
      (fun p : (Fin k -> osiiAxisPairIndex d -> Complex) ×
          SchwartzNPoint d (k + 1) =>
        distribution p.1 p.2)
      (carrier ×ˢ Set.univ)
  extendsFirst :
    Set.EqOn distribution (Z.coherent.distribution OS lgc)
      (osiiAxisPairMultiGapLogDomain d k)

namespace OSIIStep4FullSchwartzAngularContinuationData

variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

/-- On every real logarithmic point, a full-Schwartz angular continuation
has the direct OS Schwinger edge on all reduced tests supported in the
observed ball about `XiHat`.  This combines first-carrier provenance with the
support-local chronological carrier theorem; no cutoff extension is compared
globally. -/
theorem distribution_realEdge_reducedTestLift_eq_schwinger_translate_of_flatSupport
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (phi : SchwartzNPoint d k)
    (hsupport :
      Function.support (flattenSchwartzNPoint (d := d) phi) ⊆
        Metric.closedBall
          (osiiStep4MultiGapXiHatCenter d k center) (rho / 4)) :
    D.distribution (osiiAxisPairSimultaneousLogRealEmbed x)
        (BHW.reducedTestLift k d
          (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi) =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (translateSchwartzConfiguration
          (fun i =>
            -osiiAxisPairChronologicalPointTranslation Z.coherent.T x i)
          (BHW.reducedTestLift k d
            (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi))) := by
  let f : SchwartzNPoint d (k + 1) :=
    BHW.reducedTestLift k d
      (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi
  have hfirst := D.extendsFirst
    (osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap x)
  calc
    D.distribution (osiiAxisPairSimultaneousLogRealEmbed x) f =
        Z.coherent.distribution OS lgc
          (osiiAxisPairSimultaneousLogRealEmbed x) f := by
      exact congrArg (fun L : SchwartzNPoint d (k + 1) →L[Complex] Complex =>
        L f) hfirst
    _ = Z.coherent.pairing OS lgc f
          (osiiAxisPairSimultaneousLogRealEmbed x) := by
      exact Z.coherent.distribution_apply OS lgc _ f
    _ = OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (translateSchwartzConfiguration
          (fun i =>
            -osiiAxisPairChronologicalPointTranslation Z.coherent.T x i)
          f)) := by
      exact
        Z.coherent.pairing_realEdge_reducedTestLift_eq_schwinger_translate_of_flatSupport
          rho (osiiStep4MultiGapXiHatCenter d k center)
          OS lgc x phi hsupport

/-- Forget source linearity only at the final physical consumer boundary. -/
noncomputable def toPhysicalAngularContinuationData
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc) :
    OSIIStep4PhysicalAngularContinuationData
      (hcenter := hcenter) Z OS lgc where
  carrier := D.carrier
  carrier_open := D.carrier_open
  firstCarrier_subset := D.firstCarrier_subset
  continuation := fun z w =>
    D.distribution w
      (osiiStep4CoherentTargetSource d k hrho center z)
  weaklyHolomorphic := fun z =>
    D.weaklyHolomorphic
      (osiiStep4CoherentTargetSource d k hrho center z)
  continuousOn_joint_on_compact := by
    intro L _hLcompact hLcarrier
    let source : OSIIStep4FullComplexSpace d k ->
        SchwartzNPoint d (k + 1) :=
      osiiStep4CoherentTargetSource d k hrho center
    let inner : OSIIStep4FullComplexSpace d k ×
        (Fin k -> osiiAxisPairIndex d -> Complex) ->
        (Fin k -> osiiAxisPairIndex d -> Complex) ×
          SchwartzNPoint d (k + 1) :=
      fun p => (p.2, source p.1)
    have hinner : Continuous inner :=
      continuous_snd.prodMk
        ((continuous_osiiStep4CoherentTargetSource
          d k hrho center).comp continuous_fst)
    have hmaps : Set.MapsTo inner (Set.univ ×ˢ L)
        (D.carrier ×ˢ Set.univ) := by
      intro p hp
      exact ⟨hLcarrier hp.2, Set.mem_univ _⟩
    change ContinuousOn
      ((fun p => (D.distribution p.1) p.2) ∘ inner) (Set.univ ×ˢ L)
    exact D.continuousOn_joint.comp hinner.continuousOn hmaps
  extendsFirst := by
    intro z w hw
    let F := osiiStep4CoherentTargetSource d k hrho center z
    calc
      D.distribution w F =
          Z.coherent.distribution OS lgc w F :=
        congrArg
          (fun T : SchwartzNPoint d (k + 1) →L[Complex] Complex => T F)
          (D.extendsFirst hw)
      _ = Z.coherent.pairing OS lgc F w :=
        Z.coherent.distribution_apply OS lgc w F

/-- Every compact angular subcarrier has one finite complex-Schwartz
seminorm controlling the complete distribution family. -/
theorem exists_uniform_schwartzBound_on_compact
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (K : Set (Fin k -> osiiAxisPairIndex d -> Complex))
    (hK_compact : IsCompact K)
    (hK_carrier : K ⊆ D.carrier) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 < C ∧
      forall w, w ∈ K -> forall F : SchwartzNPoint d (k + 1),
        ‖D.distribution w F‖ <=
          C * s.sup
            (schwartzSeminormFamily Complex
              (NPointDomain d (k + 1)) Complex) F := by
  let T : K -> SchwartzNPoint d (k + 1) →L[Complex] Complex :=
    fun w => D.distribution w.1
  have hT_pointwise : forall F : SchwartzNPoint d (k + 1),
      exists C : Real, forall w : K, ‖T w F‖ <= C := by
    intro F
    have hcontinuous : ContinuousOn
        (fun w => D.distribution w F) K := by
      let embed : (Fin k -> osiiAxisPairIndex d -> Complex) ->
          (Fin k -> osiiAxisPairIndex d -> Complex) ×
            SchwartzNPoint d (k + 1) :=
        fun w => (w, F)
      have hembed : Continuous embed :=
        continuous_id.prodMk continuous_const
      have hmaps : Set.MapsTo embed K
          (D.carrier ×ˢ Set.univ) := by
        intro w hw
        exact ⟨hK_carrier hw, Set.mem_univ _⟩
      change ContinuousOn
        ((fun p => (D.distribution p.1) p.2) ∘ embed) K
      exact D.continuousOn_joint.comp hembed.continuousOn hmaps
    obtain ⟨C, hC⟩ :=
      hK_compact.exists_bound_of_continuousOn hcontinuous
    exact ⟨C, fun w => hC w.1 w.2⟩
  have hEqui : UniformEquicontinuous (fun w F => T w F) := by
    let TR : K -> SchwartzNPoint d (k + 1) →L[Real] Complex :=
      fun w => (T w).restrictScalars Real
    simpa [TR] using
      (SchwartzMap.tempered_equicontinuous
        (E := NPointDomain d (k + 1))
        (F := Complex) (G := Complex) (T := TR) hT_pointwise)
  let hsmul : ContinuousSMul Complex (SchwartzNPoint d (k + 1)) :=
    SchwartzMap.instContinuousSMul
  have hq :=
    (@WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm
      Complex Complex
      (SchwartzNPoint d (k + 1))
      Complex
      (Fin 1)
      _ _ _ _ _ _ (RingHom.id Complex) _ K
      (fun _ : Fin 1 => normSeminorm Complex Complex)
      _ _ _ _
      (norm_withSeminorms Complex Complex)
      hsmul
      (fun w => (T w).toLinearMap)).mp hEqui
  obtain ⟨p, hp_cont, hp_bound⟩ := hq (0 : Fin 1)
  obtain ⟨s, C, _hC, hp_dominate⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms Complex
        (NPointDomain d (k + 1)) Complex)
      p hp_cont
  refine ⟨s, (C : Real) + 1, by positivity, ?_⟩
  intro w hw F
  let ws : K := ⟨w, hw⟩
  have hbase :
      ‖D.distribution w F‖ <=
        (C : Real) * s.sup
          (schwartzSeminormFamily Complex
            (NPointDomain d (k + 1)) Complex) F := by
    calc
      ‖D.distribution w F‖ =
          ((normSeminorm Complex Complex).comp
            (T ws).toLinearMap) F := by rfl
      _ <= p F := hp_bound ws F
      _ <= (C • s.sup
            (schwartzSeminormFamily Complex
              (NPointDomain d (k + 1)) Complex)) F :=
        hp_dominate F
      _ = (C : Real) * s.sup
            (schwartzSeminormFamily Complex
              (NPointDomain d (k + 1)) Complex) F := by rfl
  exact hbase.trans <| mul_le_mul_of_nonneg_right
    (by linarith : (C : Real) <= (C : Real) + 1)
    (apply_nonneg _ _)

end OSIIStep4FullSchwartzAngularContinuationData

namespace OSIIStep4SynchronizedMultiGapContinuationData

/-- The coherent localized distribution is the unconditional source-linear
base of the physical angular induction. -/
noncomputable def toFirstFullSchwartzAngularContinuationData
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc where
  carrier := osiiAxisPairMultiGapLogDomain d k
  carrier_open := isOpen_osiiAxisPairMultiGapLogDomain
  firstCarrier_subset := Set.Subset.rfl
  distribution := Z.coherent.distribution OS lgc
  weaklyHolomorphic := by
    intro F
    exact (Z.coherent.pairing_differentiableOn OS lgc F).congr
      (fun w _hw => Z.coherent.distribution_apply OS lgc w F)
  continuousOn_joint := by
    apply continuousOn_of_locally_continuousOn
    intro p hp
    obtain ⟨L, hLcompact, hpL, hLcarrier⟩ :=
      exists_compact_between
        (isCompact_singleton : IsCompact
          ({p.1} : Set
            (Fin k -> osiiAxisPairIndex d -> Complex)))
        isOpen_osiiAxisPairMultiGapLogDomain
        (by simpa using hp.1)
    let U : Set ((Fin k -> osiiAxisPairIndex d -> Complex) ×
        SchwartzNPoint d (k + 1)) :=
      interior L ×ˢ Set.univ
    refine ⟨U, isOpen_interior.prod isOpen_univ, ?_, ?_⟩
    · exact ⟨hpL (by simp), Set.mem_univ _⟩
    · have hpair :=
        Z.coherent.continuousOn_pairing_joint_on_compact
          OS lgc L hLcompact hLcarrier
      have hdistribution : ContinuousOn
          (fun q : (Fin k -> osiiAxisPairIndex d -> Complex) ×
              SchwartzNPoint d (k + 1) =>
            Z.coherent.distribution OS lgc q.1 q.2)
          (L ×ˢ Set.univ) :=
        hpair.congr fun q _hq =>
          Z.coherent.distribution_apply OS lgc q.1 q.2
      exact hdistribution.mono <| by
        intro q hq
        exact ⟨interior_subset hq.2.1, Set.mem_univ _⟩
  extendsFirst := fun _w _hw => rfl

end OSIIStep4SynchronizedMultiGapContinuationData
end OSReconstruction
