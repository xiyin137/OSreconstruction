/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.EuclideanPositiveTime














noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

set_option synthInstance.maxHeartbeats 200000

private theorem osPreHilbert_coe_add
    (OS : OsterwalderSchraderAxioms d)
    (x y : OSPreHilbertSpace OS) :
    (((OSPreHilbertSpace.instAdd OS).add x y :
        OSPreHilbertSpace OS) : OSHilbertSpace OS) =
      (x : OSHilbertSpace OS) + (y : OSHilbertSpace OS) := by
  letI : AddGroup (OSPreHilbertSpace OS) :=
    (OSPreHilbertSpace.instAddCommGroup OS).toAddGroup
  letI : NormedAddCommGroup (OSPreHilbertSpace OS) :=
    OSPreHilbertSpace.instNormedAddCommGroup OS
  exact UniformSpace.Completion.coe_add x y

private theorem osPreHilbert_coe_smul
    (OS : OsterwalderSchraderAxioms d) (c : ℂ)
    (x : OSPreHilbertSpace OS) :
    (((OSPreHilbertSpace.instSMul OS).smul c x :
        OSPreHilbertSpace OS) : OSHilbertSpace OS) =
      c • (x : OSHilbertSpace OS) := by
  letI : SMul ℂ (OSPreHilbertSpace OS) :=
    OSPreHilbertSpace.instSMul OS
  letI : NormedAddCommGroup (OSPreHilbertSpace OS) :=
    OSPreHilbertSpace.instNormedAddCommGroup OS
  letI : Module ℂ (OSPreHilbertSpace OS) :=
    OSPreHilbertSpace.instModule OS
  letI : InnerProductSpace ℂ (OSPreHilbertSpace OS) :=
    OSPreHilbertSpace.instInnerProductSpace OS
  exact UniformSpace.Completion.coe_smul c x

private noncomputable def osiiPositiveTimeSingleVectorLinear
    (OS : OsterwalderSchraderAxioms d) (n : ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n →ₗ[ℂ] OSHilbertSpace OS where
  toFun f :=
    (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
  map_add' f g := by
    let Ff := PositiveTimeBorchersSequence.single n f.1 f.2
    let Fg := PositiveTimeBorchersSequence.single n g.1 g.2
    have hpre :
        (⟦PositiveTimeBorchersSequence.single n (f + g).1 (f + g).2⟧ :
            OSPreHilbertSpace OS) =
          (OSPreHilbertSpace.instAdd OS).add
            (⟦Ff⟧ : OSPreHilbertSpace OS)
            (⟦Fg⟧ : OSPreHilbertSpace OS) := by
      apply OSPreHilbertSpace.mk_eq_of_funcs_eq
      intro m
      by_cases hm : m = n
      · subst hm
        simp [Ff, Fg, BorchersSequence.add_funcs]
      · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
          BorchersSequence.add_funcs, Ff, Fg, hm]
    have hcoe :=
      congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre
    exact hcoe.trans
      (osPreHilbert_coe_add OS (⟦Ff⟧ : OSPreHilbertSpace OS)
        (⟦Fg⟧ : OSPreHilbertSpace OS))
  map_smul' c f := by
    let Ff := PositiveTimeBorchersSequence.single n f.1 f.2
    have hpre :
        (⟦PositiveTimeBorchersSequence.single n (c • f).1 (c • f).2⟧ :
            OSPreHilbertSpace OS) =
          (OSPreHilbertSpace.instSMul OS).smul c
            (⟦Ff⟧ : OSPreHilbertSpace OS) := by
      apply OSPreHilbertSpace.mk_eq_of_funcs_eq
      intro m
      by_cases hm : m = n
      · subst hm
        simp [Ff, BorchersSequence.smul_funcs]
      · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
          BorchersSequence.smul_funcs, Ff, hm]
    have hcoe :=
      congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre
    exact hcoe.trans
      (osPreHilbert_coe_smul OS c (⟦Ff⟧ : OSPreHilbertSpace OS))

private theorem osiiPositiveTimeSingleVectorLinear_norm_sq
    (OS : OsterwalderSchraderAxioms d) (n : ℕ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    ‖osiiPositiveTimeSingleVectorLinear OS n f‖ ^ 2 =
      (OS.S (n + n)
        (ZeroDiagonalSchwartz.ofClassical (f.1.osConjTensorProduct f.1))).re := by
  let F := PositiveTimeBorchersSequence.single n f.1 f.2
  have hnorm :
      RCLike.re
          (@inner ℂ (OSHilbertSpace OS) _
            (osiiPositiveTimeSingleVectorLinear OS n f)
            (osiiPositiveTimeSingleVectorLinear OS n f)) =
        ‖osiiPositiveTimeSingleVectorLinear OS n f‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ)
        (osiiPositiveTimeSingleVectorLinear OS n f))
  rw [← hnorm]
  change
    RCLike.re
      (@inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))) =
      _
  rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
  exact congrArg Complex.re
    (OSInnerProduct_single_single (d := d) OS.S OS.E0_linear n n f.1 f.1)

private theorem continuous_osiiPositiveTimeSingleVectorLinear
    (OS : OsterwalderSchraderAxioms d) (n : ℕ) :
    Continuous (osiiPositiveTimeSingleVectorLinear OS n) := by
  rw [continuous_iff_seqContinuous]
  intro u f huf
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdiff :
      Filter.Tendsto (fun j => u j - f) Filter.atTop (nhds 0) := by
    simpa using huf.sub_const f
  have hzero :
      ∀ g : euclideanPositiveTimeSubmodule (d := d) n,
        VanishesToInfiniteOrderOnCoincidence
          (g.1.osConjTensorProduct g.1) := by
    intro g
    exact
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (f := g.1) (g := g.1) g.2 g.2
  have htest_cont :
      Continuous (fun g : euclideanPositiveTimeSubmodule (d := d) n =>
        (⟨g.1.osConjTensorProduct g.1, hzero g⟩ :
          ZeroDiagonalSchwartz d (n + n))) := by
    have hpair :
        Continuous (fun g : euclideanPositiveTimeSubmodule (d := d) n =>
          (g.1, g.1)) :=
      continuous_subtype_val.prodMk continuous_subtype_val
    have htensor :
        Continuous (fun g : euclideanPositiveTimeSubmodule (d := d) n =>
          g.1.osConjTensorProduct g.1) :=
      (SchwartzNPoint.osConjTensorProduct_continuous
        (d := d) (n := n) (m := n)).comp hpair
    exact htensor.subtype_mk _
  have hscalar_cont :
      Continuous (fun g : euclideanPositiveTimeSubmodule (d := d) n =>
        OS.S (n + n)
          (⟨g.1.osConjTensorProduct g.1, hzero g⟩ :
            ZeroDiagonalSchwartz d (n + n))) :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + n)).continuous.comp
      htest_cont
  have hscalar :
      Filter.Tendsto
        (fun j =>
          (OS.S (n + n)
            (⟨(u j - f).1.osConjTensorProduct (u j - f).1, hzero (u j - f)⟩ :
              ZeroDiagonalSchwartz d (n + n))).re)
        Filter.atTop (nhds 0) := by
    have hcomplex :
        Filter.Tendsto
          (fun j =>
            OS.S (n + n)
              (⟨(u j - f).1.osConjTensorProduct (u j - f).1,
                hzero (u j - f)⟩ : ZeroDiagonalSchwartz d (n + n)))
          Filter.atTop (nhds 0) := by
      convert hscalar_cont.continuousAt.tendsto.comp hdiff using 1
      · have hz :
            (⟨((0 : euclideanPositiveTimeSubmodule (d := d) n).1
                : SchwartzNPoint d n).osConjTensorProduct
                  ((0 : euclideanPositiveTimeSubmodule (d := d) n).1 :
                    SchwartzNPoint d n),
              hzero 0⟩ : ZeroDiagonalSchwartz d (n + n)) = 0 := by
            apply Subtype.ext
            simp
        rw [hz]
        exact congrArg nhds (OS.E0_linear (n + n)).map_zero.symm
    simpa only [Function.comp_apply, Complex.zero_re] using
      (Complex.continuous_re.tendsto 0).comp hcomplex
  have hnorm_eq :
      ∀ g : euclideanPositiveTimeSubmodule (d := d) n,
        ‖osiiPositiveTimeSingleVectorLinear OS n g‖ =
          Real.sqrt
            (OS.S (n + n)
              (⟨g.1.osConjTensorProduct g.1, hzero g⟩ :
                ZeroDiagonalSchwartz d (n + n))).re := by
    intro g
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [osiiPositiveTimeSingleVectorLinear_norm_sq]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := g.1.osConjTensorProduct g.1) (hzero g)]
  have hnorm :
      Filter.Tendsto
        (fun j => ‖osiiPositiveTimeSingleVectorLinear OS n (u j - f)‖)
        Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hscalar
    simpa only [Function.comp_apply, Real.sqrt_zero] using
      hsqrt.congr (fun j => (hnorm_eq (u j - f)).symm)
  have hdist :
      Filter.Tendsto
        (fun j => dist (osiiPositiveTimeSingleVectorLinear OS n (u j))
          (osiiPositiveTimeSingleVectorLinear OS n f))
        Filter.atTop (nhds 0) := by
    refine hnorm.congr fun j => ?_
    rw [dist_eq_norm, ← (osiiPositiveTimeSingleVectorLinear OS n).map_sub]
  have hevent := (Metric.tendsto_nhds.mp hdist) ε hε
  exact hevent.mono fun j hj => by
    simpa [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg] using hj

noncomputable def osiiPositiveTimeSingleVectorCLM
    (OS : OsterwalderSchraderAxioms d) (n : ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ] OSHilbertSpace OS :=
  ⟨osiiPositiveTimeSingleVectorLinear OS n,
    continuous_osiiPositiveTimeSingleVectorLinear OS n⟩

@[simp] theorem osiiPositiveTimeSingleVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d) (n : ℕ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    osiiPositiveTimeSingleVectorCLM OS n f =
      (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) :
          OSHilbertSpace OS)) :=
  rfl

/-- The mixed OS Hilbert pairing of two homogeneous positive-time source
vectors is the Schwinger functional on their reflected tensor product.

This is the coefficient-level form of the scalar-product identity used in
OS II Chapter V.  Keeping the two source blocks distinct is essential for the
Taylor-tail argument, where the norm square expands into mixed pairings of
different homogeneous coefficients. -/
theorem osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    @inner ℂ (OSHilbertSpace OS) _
        (osiiPositiveTimeSingleVectorCLM OS n f)
        (osiiPositiveTimeSingleVectorCLM OS m g) =
      OS.S (n + m)
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct g.1)) := by
  let F := PositiveTimeBorchersSequence.single n f.1 f.2
  let G := PositiveTimeBorchersSequence.single m g.1 g.2
  change
    @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) =
      _
  rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
  exact OSInnerProduct_single_single (d := d) OS.S OS.E0_linear
    n m f.1 g.1

theorem osiiPositiveTimeSingleVectorCLM_norm_sq
    (OS : OsterwalderSchraderAxioms d) (n : ℕ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    ‖osiiPositiveTimeSingleVectorCLM OS n f‖ ^ 2 =
      (OS.S (n + n)
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct f.1))).re := by
  exact osiiPositiveTimeSingleVectorLinear_norm_sq OS n f

/-- For fixed complex semigroup time and left positive-time source, the OS
matrix element is a continuous linear functional of the right source. -/
noncomputable def osiiPositiveTimeSingleSemigroupPairingRightCLM
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ) (z : ℂ)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) m →L[ℂ] ℂ :=
  (innerSL ℂ (osiiPositiveTimeSingleVectorCLM OS n f)).comp
    ((osiiOriginalOSHilbertComplex OS z).comp
      (osiiPositiveTimeSingleVectorCLM OS m))

@[simp] theorem osiiPositiveTimeSingleSemigroupPairingRightCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ) (z : ℂ)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    osiiPositiveTimeSingleSemigroupPairingRightCLM OS n m z f g =
      @inner ℂ (OSHilbertSpace OS) _
        (osiiPositiveTimeSingleVectorCLM OS n f)
        (osiiOriginalOSHilbertComplex OS z
          (osiiPositiveTimeSingleVectorCLM OS m g)) :=
  rfl

/-- On the right half-plane, the continuous source pairing is exactly the
existing holomorphic OS semigroup value. -/
theorem osiiPositiveTimeSingleSemigroupPairing_eq_holomorphicValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (z : ℂ) (hz : 0 < z.re)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    osiiPositiveTimeSingleSemigroupPairingRightCLM
        OS n m z f g =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f.1 f.2)
        (PositiveTimeBorchersSequence.single m g.1 g.2) z := by
  exact
    (OSInnerProductTimeShiftHolomorphicValue_eq_inner_osTimeShiftHilbertComplex
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f.1 f.2)
      (PositiveTimeBorchersSequence.single m g.1 g.2) z hz).symm

end OSReconstruction
