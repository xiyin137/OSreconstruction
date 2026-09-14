/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIComplexSemigroupContraction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIEuclideanRotationSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertRealEdge











noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

variable {d n m : ℕ} [NeZero d]

/-- A rotated source, packaged in the positive-time Schwartz submodule. -/
noncomputable def osiiEuclideanRotatePositiveTimeComponent
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨osiiEuclideanRotateSchwartz R hR φ,
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive R hR φ hφ⟩

/-- The actual rotated directional source branch uses the original OS
semigroup and does not require an arity-growth hypothesis. -/
noncomputable def osiiAxisPairRotatedSemigroupBranchOfOS
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (_a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R) :
    ℂ → ℂ :=
  fun z =>
    osiiOriginalOSPositiveTimeSemigroupPairingRightCLM OS n m
      ((osiiAxisPairRadius T : ℂ) * z)
      (osiiEuclideanRotatePositiveTimeComponent R hR f hf)
      (osiiEuclideanRotatePositiveTimeComponent R hR g hg)

/-- Original OS data gives holomorphy of the actual directional source
branch throughout the complete coefficient right half-plane. -/
theorem differentiableOn_osiiAxisPairRotatedSemigroupBranchOfOS
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R) :
    DifferentiableOn ℂ
      (osiiAxisPairRotatedSemigroupBranchOfOS OS T a R hR f hf g hg)
      {z : ℂ | 0 < z.re} := by
  have hscale :
      DifferentiableOn ℂ
        (fun z : ℂ => (osiiAxisPairRadius T : ℂ) * z)
        {z : ℂ | 0 < z.re} :=
    (differentiable_id.const_mul (osiiAxisPairRadius T : ℂ)).differentiableOn
  exact
    (differentiableOn_osiiOriginalOSPositiveTimeSemigroupPairing OS n m
      (osiiEuclideanRotatePositiveTimeComponent R hR f hf)
      (osiiEuclideanRotatePositiveTimeComponent R hR g hg)).comp
      hscale
      (fun z hz => by
        simpa [Complex.mul_re] using
          mul_pos (osiiAxisPairRadius_pos T) hz)

/-- The directional source branch has the sharp original-OS Hilbert
Cauchy--Schwarz bound, without the spurious factor two. -/
theorem norm_osiiAxisPairRotatedSemigroupBranchOfOS_le
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R)
    (z : ℂ) (hz : 0 < z.re) :
    ‖osiiAxisPairRotatedSemigroupBranchOfOS OS T a R hR f hf g hg z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS n
          (osiiEuclideanRotatePositiveTimeComponent R hR f hf)‖ *
        ‖osiiPositiveTimeSingleVectorCLM OS m
          (osiiEuclideanRotatePositiveTimeComponent R hR g hg)‖ := by
  let fR := osiiEuclideanRotatePositiveTimeComponent R hR f hf
  let gR := osiiEuclideanRotatePositiveTimeComponent R hR g hg
  let w : ℂ := (osiiAxisPairRadius T : ℂ) * z
  have hw : 0 < w.re := by
    simpa [w, Complex.mul_re] using
      mul_pos (osiiAxisPairRadius_pos T) hz
  change
    ‖@inner ℂ (OSHilbertSpace OS) inferInstance
        (osiiPositiveTimeSingleVectorCLM OS n fR)
        (osiiOriginalOSHilbertComplex OS w
          (osiiPositiveTimeSingleVectorCLM OS m gR))‖ ≤ _
  calc
    _ ≤ ‖osiiPositiveTimeSingleVectorCLM OS n fR‖ *
          ‖osiiOriginalOSHilbertComplex OS w
            (osiiPositiveTimeSingleVectorCLM OS m gR)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖osiiPositiveTimeSingleVectorCLM OS n fR‖ *
          (‖osiiOriginalOSHilbertComplex OS w‖ *
            ‖osiiPositiveTimeSingleVectorCLM OS m gR‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖osiiPositiveTimeSingleVectorCLM OS n fR‖ *
          (1 * ‖osiiPositiveTimeSingleVectorCLM OS m gR‖) := by
      gcongr
      exact osiiOriginalOSHilbertComplex_norm_le_one OS w hw
    _ = _ := by simp [fR, gR]

/-- At every positive coefficient, the growth-free directional branch
recovers its literal zero-diagonal Schwinger source. -/
theorem osiiAxisPairRotatedSemigroupBranchOfOS_ofReal_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (hdir :
      R.transpose.mulVec (timeShiftVec d (osiiAxisPairRadius T)) =
        osiiAxisPairDir (d := d) T a)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R)
    (u : ℝ) (hu : 0 < u) :
    osiiAxisPairRotatedSemigroupBranchOfOS OS T a R hR f hf g hg (u : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((osiiEuclideanRotateSchwartz R hR f).osConjTensorProduct
          (osiiEuclideanRotateSchwartz R hR
            (translateSchwartzNPoint (d := d)
              (u • osiiAxisPairDir (d := d) T a) g)))) := by
  let fR := osiiEuclideanRotatePositiveTimeComponent R hR f hf
  let gR := osiiEuclideanRotatePositiveTimeComponent R hR g hg
  have hut : 0 < u * osiiAxisPairRadius T :=
    mul_pos hu (osiiAxisPairRadius_pos T)
  have htranslate :
      osiiEuclideanRotateSchwartz R hR
          (translateSchwartzNPoint (d := d)
            (u • osiiAxisPairDir (d := d) T a) g) =
        timeShiftSchwartzNPoint (d := d) (u * osiiAxisPairRadius T)
          (osiiEuclideanRotateSchwartz R hR g) := by
    rw [osiiEuclideanRotateSchwartz_translate]
    rw [osiiAxisPairRotation_mulVec_smul_dir hR hdir]
  have hedge :=
    osiiOriginalOSPositiveTimeSemigroupPairing_ofReal_eq_schwinger
      OS n m (u * osiiAxisPairRadius T) hut fR gR
  simpa [osiiAxisPairRotatedSemigroupBranchOfOS, fR, gR,
    htranslate, mul_comm] using hedge

/-- Holomorphic semigroup branch for one genuine axis-pair coefficient.

The semigroup time is the coefficient multiplied by the Euclidean length
`sqrt(T^2 + 1)` of the direction. -/
def osiiAxisPairRotatedSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (_a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R) :
    ℂ → ℂ :=
  fun z =>
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
      (osiiEuclideanRotatePositiveTimeSingle R hR f hf)
      (osiiEuclideanRotatePositiveTimeSingle R hR g hg)
      ((osiiAxisPairRadius T : ℂ) * z)

/-- On its actual coefficient domain, the old growth-indexed directional
branch is exactly the original-OS source branch. -/
theorem osiiAxisPairRotatedSemigroupBranch_eq_ofOS
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R)
    (z : ℂ) (hz : 0 < z.re) :
    osiiAxisPairRotatedSemigroupBranch OS lgc T a R hR f hf g hg z =
      osiiAxisPairRotatedSemigroupBranchOfOS OS T a R hR f hf g hg z := by
  have hscaled : 0 < (((osiiAxisPairRadius T : ℂ) * z).re) := by
    simpa [Complex.mul_re] using
      mul_pos (osiiAxisPairRadius_pos T) hz
  have hpair :=
    osiiPositiveTimeSingleSemigroupPairing_eq_holomorphicValue
      OS lgc n m ((osiiAxisPairRadius T : ℂ) * z) hscaled
      (osiiEuclideanRotatePositiveTimeComponent R hR f hf)
      (osiiEuclideanRotatePositiveTimeComponent R hR g hg)
  simpa [osiiAxisPairRotatedSemigroupBranch,
    osiiAxisPairRotatedSemigroupBranchOfOS,
    osiiOriginalOSPositiveTimeSemigroupPairingRightCLM,
    osiiEuclideanRotatePositiveTimeComponent,
    osiiEuclideanRotatePositiveTimeSingle] using hpair.symm

/-- The rotated one-direction branch is holomorphic on the right half-plane. -/
theorem differentiableOn_osiiAxisPairRotatedSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m) R) :
    DifferentiableOn ℂ
      (osiiAxisPairRotatedSemigroupBranch OS lgc T a R hR f hf g hg)
      {z : ℂ | 0 < z.re} := by
  have hscale :
      DifferentiableOn ℂ
        (fun z : ℂ => (osiiAxisPairRadius T : ℂ) * z)
        {z : ℂ | 0 < z.re} :=
    (differentiable_id.const_mul (osiiAxisPairRadius T : ℂ)).differentiableOn
  exact
    (OSInnerProductTimeShiftHolomorphicValue_differentiableOn
      (d := d) OS lgc
      (osiiEuclideanRotatePositiveTimeSingle R hR f hf)
      (osiiEuclideanRotatePositiveTimeSingle R hR g hg)).comp
      hscale
      (fun z hz => by
        have hr := osiiAxisPairRadius_pos T
        simpa [Complex.mul_re] using mul_pos hr hz)

/-- The canonical signed axis-pair branch is already available under the
original OS axioms. -/
noncomputable def osiiAxisPairCanonicalRotatedSemigroupBranchOfOS
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix) :
    ℂ → ℂ :=
  osiiAxisPairRotatedSemigroupBranchOfOS OS T a
    (osiiAxisPairRotationData T a).matrix
    (osiiAxisPairRotationData T a).orthogonal f hf g hg

/-- Holomorphy of the canonical original-OS directional branch. -/
theorem differentiableOn_osiiAxisPairCanonicalRotatedSemigroupBranchOfOS
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix) :
    DifferentiableOn ℂ
      (osiiAxisPairCanonicalRotatedSemigroupBranchOfOS OS T a f hf g hg)
      {z : ℂ | 0 < z.re} :=
  differentiableOn_osiiAxisPairRotatedSemigroupBranchOfOS OS T a
    (osiiAxisPairRotationData T a).matrix
    (osiiAxisPairRotationData T a).orthogonal f hf g hg

/-- The canonical original-OS source branch preserves the exact product of
the two reflected Hilbert-source norms. -/
theorem norm_osiiAxisPairCanonicalRotatedSemigroupBranchOfOS_le
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix)
    (z : ℂ) (hz : 0 < z.re) :
    ‖osiiAxisPairCanonicalRotatedSemigroupBranchOfOS
        OS T a f hf g hg z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS n
          (osiiEuclideanRotatePositiveTimeComponent
            (osiiAxisPairRotationData T a).matrix
            (osiiAxisPairRotationData T a).orthogonal f hf)‖ *
        ‖osiiPositiveTimeSingleVectorCLM OS m
          (osiiEuclideanRotatePositiveTimeComponent
            (osiiAxisPairRotationData T a).matrix
            (osiiAxisPairRotationData T a).orthogonal g hg)‖ :=
  norm_osiiAxisPairRotatedSemigroupBranchOfOS_le OS T a
    (osiiAxisPairRotationData T a).matrix
    (osiiAxisPairRotationData T a).orthogonal f hf g hg z hz

/-- Exact zero-diagonal Schwinger real edge of the canonical original-OS
directional branch. -/
theorem osiiAxisPairCanonicalRotatedSemigroupBranchOfOS_ofReal_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix)
    (u : ℝ) (hu : 0 < u) :
    osiiAxisPairCanonicalRotatedSemigroupBranchOfOS
        OS T a f hf g hg (u : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((osiiEuclideanRotateSchwartz
            (osiiAxisPairRotationData T a).matrix
            (osiiAxisPairRotationData T a).orthogonal f).osConjTensorProduct
          (osiiEuclideanRotateSchwartz
            (osiiAxisPairRotationData T a).matrix
            (osiiAxisPairRotationData T a).orthogonal
            (translateSchwartzNPoint (d := d)
              (u • osiiAxisPairDir (d := d) T a) g)))) :=
  osiiAxisPairRotatedSemigroupBranchOfOS_ofReal_eq_schwinger OS T a
    (osiiAxisPairRotationData T a).matrix
    (osiiAxisPairRotationData T a).orthogonal
    (osiiAxisPairRotationData T a).transpose_timeShift f hf g hg u hu

/-- Canonical one-direction branch using the bundled proper rotation chosen
for the signed axis-pair direction. -/
def osiiAxisPairCanonicalRotatedSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix) :
    ℂ → ℂ :=
  let P := osiiAxisPairRotationData T a
  osiiAxisPairRotatedSemigroupBranch
    OS lgc T a P.matrix P.orthogonal f hf g hg

/-- The old canonical source branch agrees with the growth-free branch on
the complete physical right half-plane. -/
theorem osiiAxisPairCanonicalRotatedSemigroupBranch_eq_ofOS
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix)
    (z : ℂ) (hz : 0 < z.re) :
    osiiAxisPairCanonicalRotatedSemigroupBranch OS lgc T a f hf g hg z =
      osiiAxisPairCanonicalRotatedSemigroupBranchOfOS OS T a f hf g hg z :=
  osiiAxisPairRotatedSemigroupBranch_eq_ofOS OS lgc T a
    (osiiAxisPairRotationData T a).matrix
    (osiiAxisPairRotationData T a).orthogonal f hf g hg z hz

/-- The canonical one-direction branch is holomorphic on the right
half-plane. -/
theorem differentiableOn_osiiAxisPairCanonicalRotatedSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (f : SchwartzNPoint d n)
    (hf :
      tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
          (osiiAxisPairRotationData T a).matrix)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
          (osiiAxisPairRotationData T a).matrix) :
    DifferentiableOn ℂ
      (osiiAxisPairCanonicalRotatedSemigroupBranch OS lgc T a f hf g hg)
      {z : ℂ | 0 < z.re} := by
  exact
    differentiableOn_osiiAxisPairRotatedSemigroupBranch
      OS lgc T a
        (osiiAxisPairRotationData T a).matrix
        (osiiAxisPairRotationData T a).orthogonal
        f hf g hg

/-- A pair of source tests admissible for the canonical rotation attached to
one signed axis-pair direction. -/
structure OSIIAxisPairRotatedSourcePacket
    (d n m : ℕ) [NeZero d]
    (T : ℝ) (a : osiiAxisPairIndex d) where
  left : SchwartzNPoint d n
  left_support :
    tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n)
        (osiiAxisPairRotationData T a).matrix
  right : SchwartzNPoint d m
  right_support :
    tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := m)
        (osiiAxisPairRotationData T a).matrix

namespace OSIIAxisPairRotatedSourcePacket

/-- Build an admissible directional packet from ordinary ordered
positive-time sources in the selected rotated frame. -/
noncomputable def ofRotatedPositive
    (T : ℝ) (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    OSIIAxisPairRotatedSourcePacket d n m T a where
  left :=
    osiiEuclideanUnrotateSchwartz
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal left
  left_support :=
    osiiEuclideanUnrotateSchwartz_tsupport_orderedPositive
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal left hleft
  right :=
    osiiEuclideanUnrotateSchwartz
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal right
  right_support :=
    osiiEuclideanUnrotateSchwartz_tsupport_orderedPositive
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal right hright

/-- Freeze every inactive axis-pair coefficient into an ordinary
positive-time source in the selected rotated frame. The `T > 1` condition
ensures that the rotated frozen translation has nonnegative time component. -/
noncomputable def ofRotatedPositiveFrozen
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    OSIIAxisPairRotatedSourcePacket d n m T a :=
  ofRotatedPositive T a left hleft
    (translateSchwartzNPoint (d := d)
      ((osiiAxisPairRotationData T a).matrix.mulVec
        (osiiAxisPairFrozenTranslation (d := d) T c a)) right)
    (osiiEuclideanTranslation_preserves_orderedPositive
      ((osiiAxisPairRotationData T a).matrix.mulVec
        (osiiAxisPairFrozenTranslation (d := d) T c a))
      ((osiiAxisPairRotationData T a).mulVec_frozenTranslation_time_nonneg
        hT c hc)
      right hright)

/-- Build a directional packet from one common left source. The inserted
compensation makes the inverse-rotated real edge recover that source exactly. -/
noncomputable def compensatedLeft
    (T : ℝ) (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    OSIIAxisPairRotatedSourcePacket d n m T a where
  left :=
    osiiEuclideanCompensatedLeftSchwartz
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal left
  left_support :=
    osiiEuclideanCompensatedLeftSchwartz_tsupport_orderedPositive
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal left hleft
  right := right
  right_support := hright

/-- Freeze all inactive nonnegative axis-pair coefficients into the right
source while retaining one active semigroup coefficient. -/
noncomputable def compensatedFrozen
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    OSIIAxisPairRotatedSourcePacket d n m T a :=
  compensatedLeft T a left hleft
    (translateSchwartzNPoint (d := d)
      (osiiAxisPairFrozenTranslation (d := d) T c a) right)
    (osiiEuclideanTranslation_preserves_orientedPositive
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairFrozenTranslation (d := d) T c a)
      ((osiiAxisPairRotationData T a).mulVec_frozenTranslation_time_nonneg
        hT c hc)
      right hright)

/-- Canonical common source on the full positive axis-pair real edge. -/
def commonRealSource
    (T : ℝ) (c : osiiAxisPairIndex d → ℝ)
    (left : SchwartzNPoint d n) (right : SchwartzNPoint d m) :
    SchwartzNPoint d (n + m) :=
  left.conj.tensorProduct
    (translateSchwartzNPoint (d := d)
      (∑ b : osiiAxisPairIndex d,
        c b • osiiAxisPairDir (d := d) T b) right)

/-- The canonical source-packet branch is a genuine original-OS object. -/
noncomputable def branchOfOS
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d) :
    ℂ → ℂ :=
  osiiAxisPairCanonicalRotatedSemigroupBranchOfOS
    OS T a P.left P.left_support P.right P.right_support

/-- The canonical semigroup branch owned by an admissible source packet. -/
def branch
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ℂ → ℂ :=
  osiiAxisPairCanonicalRotatedSemigroupBranch
    OS lgc T a P.left P.left_support P.right P.right_support

/-- The old packet branch is only a compatibility presentation of the
growth-free canonical source branch on its physical domain. -/
theorem branch_eq_branchOfOS
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (z : ℂ) (hz : 0 < z.re) :
    P.branch OS lgc z = P.branchOfOS OS z :=
  osiiAxisPairCanonicalRotatedSemigroupBranch_eq_ofOS
    OS lgc T a P.left P.left_support P.right P.right_support z hz

/-- Original OS data suffices for holomorphy of every actual rotated
source-packet branch. -/
theorem branchOfOS_differentiableOn
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d) :
    DifferentiableOn ℂ (P.branchOfOS OS) {z : ℂ | 0 < z.re} :=
  differentiableOn_osiiAxisPairCanonicalRotatedSemigroupBranchOfOS
    OS T a P.left P.left_support P.right P.right_support

/-- The original-OS packet obeys the sharp Hilbert product bound throughout
its entire physical coefficient half-plane. -/
theorem norm_branchOfOS_le
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d)
    (z : ℂ) (hz : 0 < z.re) :
    ‖P.branchOfOS OS z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS n
          (osiiEuclideanRotatePositiveTimeComponent
            (osiiAxisPairRotationData T a).matrix
            (osiiAxisPairRotationData T a).orthogonal
            P.left P.left_support)‖ *
        ‖osiiPositiveTimeSingleVectorCLM OS m
          (osiiEuclideanRotatePositiveTimeComponent
            (osiiAxisPairRotationData T a).matrix
            (osiiAxisPairRotationData T a).orthogonal
            P.right P.right_support)‖ :=
  norm_osiiAxisPairCanonicalRotatedSemigroupBranchOfOS_le
    OS T a P.left P.left_support P.right P.right_support z hz

/-- The actual original-OS branch depends only on the two Schwartz sources;
ordered-support witnesses remain propositionally irrelevant. -/
theorem branchOfOS_eq_of_source_eq
    (P Q : OSIIAxisPairRotatedSourcePacket d n m T a)
    (hleft : P.left = Q.left)
    (hright : P.right = Q.right)
    (OS : OsterwalderSchraderAxioms d) :
    P.branchOfOS OS = Q.branchOfOS OS := by
  rcases P with ⟨Pleft, Pleft_support, Pright, Pright_support⟩
  rcases Q with ⟨Qleft, Qleft_support, Qright, Qright_support⟩
  dsimp at hleft hright ⊢
  subst Qleft
  subst Qright
  rfl

/-- A packet branch depends only on its two Schwartz sources; support proofs
are propositionally irrelevant. -/
theorem branch_eq_of_source_eq
    (P Q : OSIIAxisPairRotatedSourcePacket d n m T a)
    (hleft : P.left = Q.left)
    (hright : P.right = Q.right)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    P.branch OS lgc = Q.branch OS lgc := by
  rcases P with ⟨Pleft, Pleft_support, Pright, Pright_support⟩
  rcases Q with ⟨Qleft, Qleft_support, Qright, Qright_support⟩
  dsimp at hleft hright ⊢
  subst Qleft
  subst Qright
  rfl

/-- Every admissible source packet gives a holomorphic one-direction branch. -/
theorem branch_differentiableOn
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    DifferentiableOn ℂ (P.branch OS lgc) {z : ℂ | 0 < z.re} :=
  differentiableOn_osiiAxisPairCanonicalRotatedSemigroupBranch
    OS lgc T a P.left P.left_support P.right P.right_support

/-- The zero-diagonal source produced directly by the rotated positive-time
semigroup on a positive real coefficient. -/
noncomputable def rotatedRealSource
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (u : ℝ) :
    SchwartzNPoint d (n + m) :=
  (osiiEuclideanRotateSchwartz
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal
      P.left).osConjTensorProduct
    (osiiEuclideanRotateSchwartz
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal
      (translateSchwartzNPoint (d := d)
        (u • osiiAxisPairDir (d := d) T a) P.right))

/-- A packet built in the rotated frame has the ordinary positive-time OS
tensor product with a pure time shift as its real semigroup source. -/
theorem ofRotatedPositive_rotatedRealSource_eq
    (T : ℝ) (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m)
    (u : ℝ) :
    (ofRotatedPositive T a left hleft right hright).rotatedRealSource u =
      left.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d)
          (u * osiiAxisPairRadius T) right) := by
  rw [rotatedRealSource]
  simp only [ofRotatedPositive, osiiEuclideanRotateSchwartz_unrotate]
  rw [osiiEuclideanRotateSchwartz_translate]
  rw [osiiAxisPairRotation_mulVec_smul_dir
    (osiiAxisPairRotationData T a).orthogonal
    (osiiAxisPairRotationData T a).transpose_timeShift]
  rw [osiiEuclideanRotateSchwartz_unrotate]

/-- The source obtained by transporting the semigroup real edge back to the
original Euclidean coordinates. This is the object to compare with a common
Section 4.3 Schwinger germ. -/
noncomputable def unrotatedRealSource
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (u : ℝ) :
    SchwartzNPoint d (n + m) :=
  osiiEuclideanUnrotateSchwartz
    (osiiAxisPairRotationData T a).matrix
    (osiiAxisPairRotationData T a).orthogonal
    (P.rotatedRealSource u)

/-- The actual original-OS packet has its literal zero-diagonal Schwinger
real edge without a legacy arity-growth hypothesis. -/
theorem branchOfOS_ofReal_eq_schwinger
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d)
    (u : ℝ) (hu : 0 < u) :
    P.branchOfOS OS (u : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (P.rotatedRealSource u)) := by
  simpa [branchOfOS, rotatedRealSource] using
    osiiAxisPairCanonicalRotatedSemigroupBranchOfOS_ofReal_eq_schwinger
      OS T a P.left P.left_support P.right P.right_support u hu

/-- The frozen rotated-frame packet has the full rotated spacetime
translation on its positive real edge. -/
theorem ofRotatedPositiveFrozen_rotatedRealSource_eq
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m)
    (u : ℝ) :
    (ofRotatedPositiveFrozen T hT c hc a
        left hleft right hright).rotatedRealSource u =
      left.osConjTensorProduct
        (translateSchwartzNPoint (d := d)
          ((osiiAxisPairRotationData T a).matrix.mulVec
            (osiiAxisPairFrozenTranslation (d := d) T c a +
              u • osiiAxisPairDir (d := d) T a)) right) := by
  rw [ofRotatedPositiveFrozen, ofRotatedPositive_rotatedRealSource_eq]
  ext x
  simp only [SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply, SchwartzNPoint.osConj_apply,
    timeShiftSchwartzNPoint_apply,
    translateSchwartzNPoint_apply]
  apply congrArg₂ (· * ·)
  · rfl
  · congr 1
    funext j
    rw [Matrix.mulVec_add,
      osiiAxisPairRotation_mulVec_smul_dir
        (osiiAxisPairRotationData T a).orthogonal
        (osiiAxisPairRotationData T a).transpose_timeShift]
    module

/-- At the selected coefficient, the frozen packet carries the complete
axis-pair translation vector in the selected rotated frame. -/
theorem ofRotatedPositiveFrozen_rotatedRealSource_selected_eq
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    (ofRotatedPositiveFrozen T hT c hc a
        left hleft right hright).rotatedRealSource (c a) =
      left.osConjTensorProduct
        (translateSchwartzNPoint (d := d)
          ((osiiAxisPairRotationData T a).matrix.mulVec
            (∑ b : osiiAxisPairIndex d,
              c b • osiiAxisPairDir (d := d) T b)) right) := by
  rw [ofRotatedPositiveFrozen_rotatedRealSource_eq]
  rw [osiiAxisPairFrozenTranslation_add_selected]

/-- The genuine frozen packet recovers the full selected rotated source
translation using the original OS axioms alone. -/
theorem ofRotatedPositiveFrozen_branchOfOS_selected_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (hca : 0 < c a)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    (ofRotatedPositiveFrozen T hT c hc a
        left hleft right hright).branchOfOS OS (c a : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (left.osConjTensorProduct
          (translateSchwartzNPoint (d := d)
            ((osiiAxisPairRotationData T a).matrix.mulVec
              (∑ b : osiiAxisPairIndex d,
                c b • osiiAxisPairDir (d := d) T b)) right))) := by
  rw [branchOfOS_ofReal_eq_schwinger
    (ofRotatedPositiveFrozen T hT c hc a left hleft right hright)
    OS (c a) hca]
  rw [ofRotatedPositiveFrozen_rotatedRealSource_selected_eq]

/-- The selected real edge of the frozen packet is the Schwinger functional
of the complete rotated axis-pair translation. -/
theorem ofRotatedPositiveFrozen_branch_selected_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (hca : 0 < c a)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    (ofRotatedPositiveFrozen T hT c hc a
        left hleft right hright).branch OS lgc (c a : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (left.osConjTensorProduct
          (translateSchwartzNPoint (d := d)
            ((osiiAxisPairRotationData T a).matrix.mulVec
              (∑ b : osiiAxisPairIndex d,
                c b • osiiAxisPairDir (d := d) T b)) right))) := by
  rw [branch_eq_branchOfOS
    (ofRotatedPositiveFrozen T hT c hc a left hleft right hright)
    OS lgc (c a : ℂ) (by simpa using hca)]
  exact ofRotatedPositiveFrozen_branchOfOS_selected_eq_schwinger
    OS T hT c hc a hca left hleft right hright

/- Positive real coefficients make the rotated packet source genuinely
zero-diagonal. -/
theorem rotatedRealSource_vanishes
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (u : ℝ) (hu : 0 < u) :
    VanishesToInfiniteOrderOnCoincidence (P.rotatedRealSource u) := by
  let R := (osiiAxisPairRotationData T a).matrix
  let hR := (osiiAxisPairRotationData T a).orthogonal
  let fR := osiiEuclideanRotateSchwartz R hR P.left
  let gR := osiiEuclideanRotateSchwartz R hR P.right
  have hfR :
      tsupport ((fR : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR P.left P.left_support
  have hgR :
      tsupport ((gR : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR P.right P.right_support
  have hr : 0 < osiiAxisPairRadius T := osiiAxisPairRadius_pos T
  have hut : 0 < u * osiiAxisPairRadius T := mul_pos hu hr
  have htranslate :
      osiiEuclideanRotateSchwartz R hR
          (translateSchwartzNPoint (d := d)
            (u • osiiAxisPairDir (d := d) T a) P.right) =
        timeShiftSchwartzNPoint (d := d) (u * osiiAxisPairRadius T) gR := by
    rw [osiiEuclideanRotateSchwartz_translate]
    rw [osiiAxisPairRotation_mulVec_smul_dir hR
      (osiiAxisPairRotationData T a).transpose_timeShift]
  rw [rotatedRealSource, htranslate]
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) fR
      (timeShiftSchwartzNPoint (d := d) (u * osiiAxisPairRadius T) gR)
      hfR
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) (u * osiiAxisPairRadius T) hut gR hgR)

/- The inverse-rotated comparison source remains zero-diagonal. -/
theorem unrotatedRealSource_vanishes
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (u : ℝ) (hu : 0 < u) :
    VanishesToInfiniteOrderOnCoincidence (P.unrotatedRealSource u) := by
  exact
    VanishesToInfiniteOrderOnCoincidence.osiiEuclideanUnrotate
      (P.rotatedRealSource_vanishes u hu)

/-- Pointwise form of the comparison source. The right block is now translated
by the genuine signed spacetime direction; all residual direction dependence
is isolated in the conjugated time reflection on the left block. -/
@[simp] theorem unrotatedRealSource_apply
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (u : ℝ) (x : NPointDomain d (n + m)) :
    P.unrotatedRealSource u x =
      starRingEnd ℂ
          (P.left (fun i =>
            osiiEuclideanRotatedTimeReflection
              (osiiAxisPairRotationData T a).matrix
              (splitFirst n m x i))) *
        P.right (fun j =>
          splitLast n m x j -
            u • osiiAxisPairDir (d := d) T a) := by
  simp only [unrotatedRealSource, rotatedRealSource,
    osiiEuclideanUnrotateSchwartz_apply,
    osiiEuclideanRotateSchwartz_apply,
    SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, timeReflectionN,
    osiiEuclideanRotatedTimeReflection, translateSchwartzNPoint_apply]
  apply congrArg₂ (· * ·)
  · apply congrArg (starRingEnd ℂ)
    congr 1
  · congr 1
    funext j
    change
      (osiiAxisPairRotationData T a).matrix.transpose.mulVec
          ((osiiAxisPairRotationData T a).matrix.mulVec
            (splitLast n m x j)) -
        u • osiiAxisPairDir (d := d) T a =
      splitLast n m x j -
        u • osiiAxisPairDir (d := d) T a
    rw [Matrix.mulVec_mulVec,
      (osiiAxisPairRotationData T a).orthogonal]
    simp

/- The compensated packet removes all direction dependence from the left
factor of the inverse-rotated real edge. -/
@[simp] theorem compensatedLeft_unrotatedRealSource_apply
    (T : ℝ) (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix)
    (u : ℝ) (x : NPointDomain d (n + m)) :
    (compensatedLeft T a left hleft right hright).unrotatedRealSource u x =
      starRingEnd ℂ (left (splitFirst n m x)) *
        right (fun j =>
          splitLast n m x j -
            u • osiiAxisPairDir (d := d) T a) := by
  rw [unrotatedRealSource_apply]
  simp only [compensatedLeft, osiiEuclideanCompensatedLeftSchwartz_apply]
  apply congrArg₂ (· * ·)
  · apply congrArg (starRingEnd ℂ)
    congr 1
    funext i
    exact
      osiiEuclideanRotatedTimeReflection_involutive
        (osiiAxisPairRotationData T a).matrix
        (osiiAxisPairRotationData T a).orthogonal
        (splitFirst n m x i)
  · rfl

/- At the selected coefficient, every frozen packet has the same full
axis-pair translation on its inverse-rotated real edge. -/
@[simp] theorem compensatedFrozen_unrotatedRealSource_selected_apply
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix)
    (x : NPointDomain d (n + m)) :
    (compensatedFrozen T hT c hc a left hleft right hright).unrotatedRealSource
        (c a) x =
      starRingEnd ℂ (left (splitFirst n m x)) *
        right (fun j =>
          splitLast n m x j -
            ∑ b : osiiAxisPairIndex d,
              c b • osiiAxisPairDir (d := d) T b) := by
  rw [compensatedFrozen, compensatedLeft_unrotatedRealSource_apply]
  simp only [translateSchwartzNPoint_apply]
  apply congrArg₂ (· * ·)
  · rfl
  · congr 1
    funext j
    rw [← osiiAxisPairFrozenTranslation_add_selected
      (d := d) T c a]
    module

omit [NeZero d] in
@[simp] theorem commonRealSource_apply
    (T : ℝ) (c : osiiAxisPairIndex d → ℝ)
    (left : SchwartzNPoint d n) (right : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    commonRealSource T c left right x =
      starRingEnd ℂ (left (splitFirst n m x)) *
        right (fun j =>
          splitLast n m x j -
            ∑ b : osiiAxisPairIndex d,
              c b • osiiAxisPairDir (d := d) T b) := by
  rfl

theorem compensatedFrozen_unrotatedRealSource_selected_eq_commonRealSource
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    (compensatedFrozen T hT c hc a left hleft right hright).unrotatedRealSource
        (c a) =
      commonRealSource T c left right := by
  ext x
  exact compensatedFrozen_unrotatedRealSource_selected_apply
    T hT c hc a left hleft right hright x

/-- The common full-translation source of a compensated packet is genuinely
zero-diagonal. This exposes the support consequence already used internally
by the inverse-rotated semigroup comparison. -/
theorem commonRealSource_vanishes
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (hca : 0 < c a)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    VanishesToInfiniteOrderOnCoincidence
      (commonRealSource T c left right) := by
  let P :=
    compensatedFrozen T hT c hc a left hleft right hright
  rw [← compensatedFrozen_unrotatedRealSource_selected_eq_commonRealSource
    T hT c hc a left hleft right hright]
  exact P.unrotatedRealSource_vanishes (c a) hca

/-- E1 rewrites the packet real edge in the original Euclidean coordinates.
The remaining family-level task is exactly to identify these sources with one
common Schwinger germ. -/
theorem branchOfOS_ofReal_eq_unrotated_schwinger
    (P : OSIIAxisPairRotatedSourcePacket d n m T a)
    (OS : OsterwalderSchraderAxioms d)
    (u : ℝ) (hu : 0 < u) :
    P.branchOfOS OS (u : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (P.unrotatedRealSource u)) := by
  rw [P.branchOfOS_ofReal_eq_schwinger OS u hu]
  exact
    osiiEuclideanUnrotateSchwartz_schwinger_eq
      OS
      (osiiAxisPairRotationData T a).matrix
      (osiiAxisPairRotationData T a).orthogonal
      (osiiAxisPairRotationData T a).det_one
      (P.rotatedRealSource u)
      (P.rotatedRealSource_vanishes u hu)

/-- The genuine compensated frozen packet has the exact common original
zero-diagonal Schwinger source, with no arity-growth hypothesis. -/
theorem compensatedFrozen_branchOfOS_selected_eq_common_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (hca : 0 < c a)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    (compensatedFrozen T hT c hc a left hleft right hright).branchOfOS
        OS (c a : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (commonRealSource T c left right)) := by
  rw [branchOfOS_ofReal_eq_unrotated_schwinger
    (compensatedFrozen T hT c hc a left hleft right hright)
    OS (c a) hca]
  rw [compensatedFrozen_unrotatedRealSource_selected_eq_commonRealSource]

/- The selected directional branch evaluates to the common full-translation
Schwinger source at every strictly positive real coefficient vector. -/
theorem compensatedFrozen_branch_selected_eq_common_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (hca : 0 < c a)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    (compensatedFrozen T hT c hc a left hleft right hright).branch
        OS lgc (c a : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (commonRealSource T c left right)) := by
  rw [branch_eq_branchOfOS
    (compensatedFrozen T hT c hc a left hleft right hright)
    OS lgc (c a : ℂ) (by simpa using hca)]
  exact compensatedFrozen_branchOfOS_selected_eq_common_schwinger
    OS T hT c hc a hca left hleft right hright

/-- Compensated frozen branches depend on the real coefficient base only away
from their selected active coefficient. -/
theorem compensatedFrozen_branch_congr_of_eq_off_selected
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    {c e : osiiAxisPairIndex d → ℝ}
    (hc : ∀ b, 0 ≤ c b)
    (he : ∀ b, 0 ≤ e b)
    (a : osiiAxisPairIndex d)
    (hce : ∀ b, b ≠ a → c b = e b)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix) :
    (compensatedFrozen T hT c hc a
        left hleft right hright).branch OS lgc =
      (compensatedFrozen T hT e he a
        left hleft right hright).branch OS lgc := by
  apply branch_eq_of_source_eq
  · rfl
  · dsimp [compensatedFrozen, compensatedLeft]
    rw [osiiAxisPairFrozenTranslation_congr_of_eq_off_selected T a hce]

end OSIIAxisPairRotatedSourcePacket

end OSReconstruction
