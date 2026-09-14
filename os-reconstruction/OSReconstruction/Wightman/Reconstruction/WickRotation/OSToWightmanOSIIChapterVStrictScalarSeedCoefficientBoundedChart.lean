/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientChart















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- One bound-preserving compactified coefficient continuation together with
an open convex target chart. -/
structure BoundedStrictScalarSeedCoefficientChartData
    {m n : Nat} [NeZero n]
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (F : (Fin m -> Complex) -> Complex)
    (seed : Fin n -> Fin m -> Real)
    (w : Fin n -> Real)
    (B : Real) where
  chart :
    StrictCoefficientTargetConvexChartData P
      (osiiStrictScalarSeedCoefficientTarget w)
  extension : (osiiAxisPairIndex n -> Complex) -> Complex
  extension_differentiableOn :
    DifferentiableOn Complex extension
      (osiiAxisPairLogDomain (d := n))
  extension_realEdge :
    forall x : osiiAxisPairIndex n -> Real,
      extension (osiiAxisPairLogRealEmbed x) =
        F (osiiStrictScalarSeedCoefficientMap seed
          (fun j =>
            SCV.stripCompactification P.radius P.slope
              (x (j, false) : Complex)))
  extension_bound :
    forall z, z ∈ osiiAxisPairLogDomain (d := n) ->
      ‖extension z‖ <= B

namespace BoundedStrictScalarSeedCoefficientChartData

variable
  {m n : Nat} [NeZero n]
  {S rho : Real}
  {P : SCV.StripCompactificationParameters S rho}
  {F : (Fin m -> Complex) -> Complex}
  {seed : Fin n -> Fin m -> Real}
  {w : Fin n -> Real}
  {B : Real}

/-- Pull the selected doubled-coordinate continuation back to ordinary
coefficient variables. -/
def germ
    (D : BoundedStrictScalarSeedCoefficientChartData P F seed w B)
    (r : Fin n -> Complex) : Complex :=
  D.extension (osiiStrictCoefficientLocalInverseLift P r)

theorem germ_differentiableOn
    (D : BoundedStrictScalarSeedCoefficientChartData P F seed w B) :
    DifferentiableOn Complex D.germ
      (osiiStrictCoefficientGermDomain P) := by
  change DifferentiableOn Complex
    (fun r => D.extension
      (osiiStrictCoefficientLocalInverseLift P r))
    (osiiStrictCoefficientGermDomain P)
  exact D.extension_differentiableOn.comp
    ((differentiableOn_osiiStrictCoefficientLocalInverseLift P).mono
      (fun _ hr => hr.1))
    (fun _ hr => hr.2)

theorem norm_germ_le
    (D : BoundedStrictScalarSeedCoefficientChartData P F seed w B)
    {r : Fin n -> Complex}
    (hr : r ∈ osiiStrictCoefficientGermDomain P) :
    ‖D.germ r‖ <= B :=
  D.extension_bound _ hr.2

/-- On the bounded real coefficient slice, the selected germ is exactly the
original predecessor composed with the seed coefficient map. -/
theorem germ_real
    (D : BoundedStrictScalarSeedCoefficientChartData P F seed w B)
    (x : Fin n -> Real)
    (hx : (fun i => (x i : Complex)) ∈
      osiiStrictCoefficientGermDomain P) :
    D.germ (fun i => (x i : Complex)) =
      F (osiiStrictScalarSeedCoefficientMap seed
        (fun i => (x i : Complex))) := by
  let q : osiiAxisPairIndex n -> Real :=
    fun a =>
      if a.2 then 0
      else
        (SCV.stripCompactificationLocalInverse
          P (x a.1 : Complex)).re
  have hlift :
      osiiStrictCoefficientLocalInverseLift P
          (fun i => (x i : Complex)) =
        osiiAxisPairLogRealEmbed q :=
    StrictScalarSeedCoefficientMZBoundData.osiiStrictCoefficientLocalInverseLift_real
      (P := P) x hx.1
  rw [germ, hlift, D.extension_realEdge]
  apply congrArg F
  apply congrArg (osiiStrictScalarSeedCoefficientMap seed)
  funext i
  have hxi_norm : ‖(x i : Complex)‖ < P.radius := by
    have hxball :
        (fun j => (x j : Complex)) ∈
          Metric.ball (0 : Fin n -> Complex) P.radius :=
      hx.1
    rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff P.radius_pos] at hxball
    exact hxball i
  have hq :
      (q (i, false) : Complex) =
        SCV.stripCompactificationLocalInverse P (x i : Complex) := by
    dsimp [q]
    have hxi : |x i| < P.radius := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hxi_norm
    rw [SCV.stripCompactificationLocalInverse_ofReal P hxi]
    rfl
  rw [hq]
  exact SCV.stripCompactification_localInverse P hxi_norm

/-- A bound on the compact coefficient window actually sampled by strip
compactification is sufficient for the bounded MZ chart.  No control on the
unbounded real parts of the complete flat tube is needed. -/
theorem nonempty_of_window
    (P : SCV.StripCompactificationParameters S rho)
    (F : (Fin m -> Complex) -> Complex)
    (U : Set (Fin m -> Complex))
    (seed : Fin n -> Fin m -> Real)
    (hF : DifferentiableOn Complex F U)
    (hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆
        osiiStrictScalarSeedCoefficientMap seed ⁻¹' U)
    (hrho : 0 < rho)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S)
    (B : Real)
    (hB : 0 < B)
    (hbound : forall r,
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ->
        ‖F (osiiStrictScalarSeedCoefficientMap seed r)‖ <= B) :
    Nonempty
      (BoundedStrictScalarSeedCoefficientChartData
        P F seed w B) := by
  let Fc : (Fin n -> Complex) -> Complex :=
    fun r => F (osiiStrictScalarSeedCoefficientMap seed r)
  let Uc : Set (Fin n -> Complex) :=
    osiiStrictScalarSeedCoefficientMap seed ⁻¹' U
  have hFc : DifferentiableOn Complex Fc Uc := by
    exact hF.comp
      (osiiStrictScalarSeedCoefficientMap_differentiable
        seed).differentiableOn
      (fun _ hr => hr)
  have hFc_bound : forall r, r ∈
      osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho -> ‖Fc r‖ <= B := by
    intro r hr
    exact hbound r hr
  obtain ⟨Gamma, hGamma, hreal, _hflat, hGammaBound⟩ :=
    exists_osiiStrictCoefficientCompactifiedMZExtension
      P hrho Fc Uc hFc hwindow B hB hFc_bound
  obtain ⟨Q⟩ :=
    nonempty_strictCoefficientTargetConvexChartData
      P w hw hsum
  refine ⟨{
    chart := Q
    extension := Gamma
    extension_differentiableOn := hGamma
    extension_realEdge := ?_
    extension_bound := hGammaBound }⟩
  intro x
  simpa [Fc, Uc,
    osiiStrictCoefficientCompactifiedFlatCrossData,
    osiiStrictCoefficientCompactifiedDirectionalFamily] using
    hreal x

end BoundedStrictScalarSeedCoefficientChartData

end OSIIChapterV
end OSReconstruction
