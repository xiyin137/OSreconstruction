/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapContinuity











noncomputable section

open Complex Matrix Set Topology
open scoped Classical

namespace OSReconstruction

/-- Membership in the support of a reflected Schwartz source pulls back to
membership in the support of the original source. -/
theorem timeReflectionN_mem_tsupport_of_mem_timeReflect
    {d n : Nat} [NeZero d]
    (f : SchwartzNPoint d n)
    {z : NPointDomain d n}
    (hz : z ∈ tsupport
      ((f.timeReflect : SchwartzNPoint d n) : NPointDomain d n -> Complex)) :
    timeReflectionN d z ∈
      tsupport (f : NPointDomain d n -> Complex) :=
  tsupport_comp_subset_preimage
    ((f : SchwartzNPoint d n) : NPointDomain d n -> Complex)
    (osiiContinuousTimeReflectionN (d := d) (n := n)) hz

/-- The left carrier map: absorb all spectator gaps, reflect the left block,
rotate the chosen axis to Euclidean time, and reflect back to positive time. -/
def osiiStep4MultiGapRotatedFrozenLeftCarrierMap
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : NPointDomain d (q.1.val + 1)) :
    NPointDomain d (q.1.val + 1) :=
  timeReflectionN d (fun j =>
    (osiiAxisPairRotationData T q.2).matrix.mulVec
      (timeReflectionN d
        (fun l => z l + osiiAxisPairChronologicalPointTranslation T
          (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x q.1) l) j))

/-- The right carrier map, including the active-gap compensation before the
chosen axis is rotated to Euclidean time. -/
def osiiStep4MultiGapRotatedFrozenRightCarrierMap
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1)) :
    NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) :=
  fun j =>
    (osiiAxisPairRotationData T q.2).matrix.mulVec
      (z j + osiiAxisPairChronologicalPointTranslation T
          (osiiStep4MultiGapRightSpectatorLogCoordinates d k x q.1) j +
        osiiAxisPairFrozenTranslation T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2)

namespace OSIIStep4MultiGapUniformCommonSlopeData

/-- The complete radial parameter pair at the physical `k`-block arity. -/
abbrev MultiGapSourceParameter (d k : Nat) :=
  (Fin (k * (d + 1)) -> Real) × (Fin (k * (d + 1)) -> Real)

/-- Common absolute carrier for the complete rotated left radial family at a
fixed logarithmic anchor and selected axis. -/
def rotatedFrozenLeftCommonCarrier
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    Set (NPointDomain d (q.1.val + 1)) :=
  osiiStep4MultiGapRotatedFrozenLeftCarrierMap d k D.T x q ''
    osiiStep4MultiGapSelectedLeftCommonCarrier d k rho center q.1

/-- Common absolute carrier for the complete rotated right radial family. -/
def rotatedFrozenRightCommonCarrier
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    Set (NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1)) :=
  osiiStep4MultiGapRotatedFrozenRightCarrierMap d k D.T x q ''
    osiiStep4MultiGapSelectedRightCommonCarrier d k rho center q.1

/-- Every rotated left radial source is supported in the common carrier that
was chosen before its two radial parameters. -/
theorem rotatedFrozenLeftSource_tsupport_subset_commonCarrier
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (p : MultiGapSourceParameter d k) :
    tsupport
        (((D.toSelectedCommonSlopeData p.1 p.2
          ).rotatedFrozenLeftSource x q :
          SchwartzNPoint d (q.1.val + 1)) :
          NPointDomain d (q.1.val + 1) -> Complex) ⊆
      D.rotatedFrozenLeftCommonCarrier x q := by
  let P := D.toSelectedCommonSlopeData p.1 p.2
  let R := (osiiAxisPairRotationData D.T q.2).matrix
  let hR := (osiiAxisPairRotationData D.T q.2).orthogonal
  let v : NPointDomain d (q.1.val + 1) -> NPointDomain d (q.1.val + 1) :=
    fun u => fun j => R.transpose.mulVec (timeReflectionN d u j)
  let cfg : NPointDomain d (q.1.val + 1) := fun j =>
    -osiiAxisPairChronologicalPointTranslation D.T
      (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x q.1) j
  intro u hu
  have hu1 :
      timeReflectionN d u ∈
        tsupport
          ((osiiEuclideanRotateSchwartz R hR
            (P.frozenLeftSource x q.1) :
            SchwartzNPoint d (q.1.val + 1)) :
            NPointDomain d (q.1.val + 1) -> Complex) := by
    exact timeReflectionN_mem_tsupport_of_mem_timeReflect _ hu
  have hu2 : v u ∈
      tsupport (P.frozenLeftSource x q.1 :
        NPointDomain d (q.1.val + 1) -> Complex) := by
    rw [tsupport_osiiEuclideanRotateSchwartz R hR] at hu1
    exact hu1
  have hu3 : timeReflectionN d (v u) ∈
      tsupport
        (osiiStep4MultiGapFrozenLeftPositiveSource
          d k hrho center p.1 p.2 hcenter D.T x q.1 :
          NPointDomain d (q.1.val + 1) -> Complex) := by
    exact timeReflectionN_mem_tsupport_of_mem_timeReflect _ hu2
  rw [osiiStep4MultiGapFrozenLeftPositiveSource,
    OSIIChapterV.tsupport_translateSchwartzConfiguration_eq_preimage] at hu3
  have hbase : timeReflectionN d (v u) + cfg ∈
      osiiStep4MultiGapSelectedLeftCommonCarrier
        d k rho center q.1 :=
    osiiStep4MultiGapSelectedLeftPositiveTimeSource_tsupport_subset_commonCarrier
      d k hrho center p.1 p.2 hcenter q.1 hu3
  refine ⟨timeReflectionN d (v u) + cfg, hbase, ?_⟩
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hadd :
      (fun l => (timeReflectionN d (v u) + cfg) l +
        osiiAxisPairChronologicalPointTranslation D.T
          (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x q.1) l) =
        timeReflectionN d (v u) := by
    funext l mu
    simp [cfg]
  have hreflect :
      timeReflectionN d (timeReflectionN d (v u)) = v u := by
    funext j
    exact timeReflection_timeReflection d ((v u) j)
  have hrotate :
      (fun j => R.mulVec ((v u) j)) = timeReflectionN d u := by
    funext j
    simp [v, Matrix.mulVec_mulVec, hR']
  rw [show osiiStep4MultiGapRotatedFrozenLeftCarrierMap d k D.T x q
      (timeReflectionN d (v u) + cfg) =
        timeReflectionN d
          (fun j => R.mulVec
            (timeReflectionN d
              (fun l => (timeReflectionN d (v u) + cfg) l +
                osiiAxisPairChronologicalPointTranslation D.T
                  (osiiStep4MultiGapLeftSpectatorLogCoordinates
                    d k x q.1) l) j)) by
      rfl]
  rw [hadd, hreflect, hrotate]
  funext j
  exact timeReflection_timeReflection d (u j)

/-- Every compensated rotated right radial source is supported in its common
carrier. -/
theorem rotatedFrozenRightSource_tsupport_subset_commonCarrier
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (p : MultiGapSourceParameter d k) :
    tsupport
        (((D.toSelectedCommonSlopeData p.1 p.2
          ).rotatedFrozenRightSource x q :
          SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1)) :
          NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) ⊆
      D.rotatedFrozenRightCommonCarrier x q := by
  let P := D.toSelectedCommonSlopeData p.1 p.2
  let R := (osiiAxisPairRotationData D.T q.2).matrix
  let hR := (osiiAxisPairRotationData D.T q.2).orthogonal
  let v : NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) ->
      NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) :=
    fun u => fun j => R.transpose.mulVec (u j)
  intro u hu
  have hu1 : v u ∈
      tsupport
        ((translateSchwartzNPoint (d := d)
          (osiiAxisPairFrozenTranslation D.T
            (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
          (P.frozenRightSource x q.1) :
          SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1)) :
          NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) := by
    change u ∈ tsupport
      ((osiiEuclideanRotateSchwartz R hR
        (translateSchwartzNPoint (d := d)
          (osiiAxisPairFrozenTranslation D.T
            (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
          (P.frozenRightSource x q.1)) :
        SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1)) :
        NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) at hu
    rw [tsupport_osiiEuclideanRotateSchwartz R hR] at hu
    exact hu
  have hu1' : v u ∈
      tsupport
        (translateSchwartzConfiguration
          (P.frozenRightPacketConfiguration x q)
          (osiiStep4MultiGapSelectedRightPositiveTimeSource
            d k hrho center p.1 p.2 hcenter q.1).1 :
          NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) := by
    rw [← P.translate_frozenRightSource_eq_configuration x q]
    simpa [P] using hu1
  rw [OSIIChapterV.tsupport_translateSchwartzConfiguration_eq_preimage] at hu1'
  have hbase : v u + P.frozenRightPacketConfiguration x q ∈
      osiiStep4MultiGapSelectedRightCommonCarrier
        d k rho center q.1 :=
    osiiStep4MultiGapSelectedRightPositiveTimeSource_tsupport_subset_commonCarrier
      d k hrho center p.1 p.2 hcenter q.1 hu1'
  refine ⟨v u + P.frozenRightPacketConfiguration x q, hbase, ?_⟩
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hcancel :
      (fun j => (v u + P.frozenRightPacketConfiguration x q) j +
        osiiAxisPairChronologicalPointTranslation D.T
          (osiiStep4MultiGapRightSpectatorLogCoordinates d k x q.1) j +
        osiiAxisPairFrozenTranslation D.T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2) = v u := by
    funext j mu
    simp [P,
      OSIIStep4MultiGapSelectedCommonSlopeData.frozenRightPacketConfiguration]
    ring
  have hrotate : (fun j => R.mulVec ((v u) j)) = u := by
    funext j
    simp [v, Matrix.mulVec_mulVec, hR']
  rw [show osiiStep4MultiGapRotatedFrozenRightCarrierMap d k D.T x q
      (v u + P.frozenRightPacketConfiguration x q) =
        fun j => R.mulVec
          ((v u + P.frozenRightPacketConfiguration x q) j +
            osiiAxisPairChronologicalPointTranslation D.T
              (osiiStep4MultiGapRightSpectatorLogCoordinates d k x q.1) j +
            osiiAxisPairFrozenTranslation D.T
              (osiiAxisPairPositiveCoefficients (x q.1)) q.2) by
      rfl]
  calc
    (fun j => R.mulVec
        ((v u + P.frozenRightPacketConfiguration x q) j +
          osiiAxisPairChronologicalPointTranslation D.T
            (osiiStep4MultiGapRightSpectatorLogCoordinates d k x q.1) j +
          osiiAxisPairFrozenTranslation D.T
            (osiiAxisPairPositiveCoefficients (x q.1)) q.2)) =
        (fun j => R.mulVec ((v u) j)) := by
          funext j
          rw [congrFun hcancel j]
    _ = u := hrotate

/-- Difference-time carrier of the rotated left source universe. -/
def rotatedFrozenLeftTimeCarrier
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    Set (Fin (q.1.val + 1) -> Real) :=
  osiiStep4FullDifferenceTimeProjectionCLM d q.1.val ''
    D.rotatedFrozenLeftCommonCarrier x q

/-- Difference-time carrier of the rotated right source universe. -/
def rotatedFrozenRightTimeCarrier
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    Set (Fin (osiiStep4MultiGapAfterCount q.1 + 1) -> Real) :=
  osiiStep4FullDifferenceTimeProjectionCLM d
      (osiiStep4MultiGapAfterCount q.1) ''
    D.rotatedFrozenRightCommonCarrier x q

/-- Rotated left source in the universal compact-time source space. -/
def rotatedFrozenLeftUniformCompactTimeSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d (q.1.val + 1)
      (D.rotatedFrozenLeftTimeCarrier x q) := by
  let P := D.toSelectedCommonSlopeData p.1 p.2
  refine ⟨P.rotatedFrozenLeftPositiveSource x q, ?_⟩
  intro z hz
  exact ⟨z, D.rotatedFrozenLeftSource_tsupport_subset_commonCarrier
    x q p hz, rfl⟩

/-- Rotated right source in the universal compact-time source space. -/
def rotatedFrozenRightUniformCompactTimeSource
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d
      (osiiStep4MultiGapAfterCount q.1 + 1)
      (D.rotatedFrozenRightTimeCarrier x q) := by
  let P := D.toSelectedCommonSlopeData p.1 p.2
  refine ⟨P.rotatedFrozenRightPositiveSource x q, ?_⟩
  intro z hz
  exact ⟨z, D.rotatedFrozenRightSource_tsupport_subset_commonCarrier
    x q p hz, rfl⟩

@[simp] theorem rotatedFrozenLeftUniformCompactTimeSource_source
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource.source
        (D.rotatedFrozenLeftUniformCompactTimeSource x q p) =
      (D.toSelectedCommonSlopeData p.1 p.2
        ).rotatedFrozenLeftPositiveSource x q :=
  rfl

@[simp] theorem rotatedFrozenRightUniformCompactTimeSource_source
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource.source
        (D.rotatedFrozenRightUniformCompactTimeSource x q p) =
      (D.toSelectedCommonSlopeData p.1 p.2
        ).rotatedFrozenRightPositiveSource x q :=
  rfl

end OSIIStep4MultiGapUniformCommonSlopeData

end OSReconstruction
