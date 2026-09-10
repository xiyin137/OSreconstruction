import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeHermiticity

/-!
# All-degree source pairing and native Wightman positivity

Hermiticity was derived from nonempty source blocks and the independent
low-point cases. It now supplies the right-vacuum pairing. The full coupled
OS form, including degree zero, passes to arbitrary finite Schwartz sequences
by compact-source density and continuity.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

/-- The exact coupled source identity, including both vacuum faces. -/
theorem strictGeneratedFullBoundary_sourcePairing
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat)
    (phi : SchwartzNPoint d n) (psi : SchwartzNPoint d m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf : HasCompactSupport (f.1 : NPointDomain d n -> Complex))
    (hg : HasCompactSupport (g.1 : NPointDomain d m -> Complex))
    (hphi : section43FrequencyProjection d n phi =
      section43FourierLaplaceTransformComponent d n f.1 f.2 hf)
    (hpsi : section43FrequencyProjection d m psi =
      section43FourierLaplaceTransformComponent d m g.1 g.2 hg) :
    initial.strictGeneratedFullBoundary lgc (n + m) (phi.conjTensorProduct psi) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.1.osConjTensorProduct g.1)) := by
  cases m with
  | succ m =>
      exact initial.strictGeneratedFullBoundary_sourcePairing_succRight_of_transformComponent
        lgc n m phi psi f g hf hg hphi hpsi
  | zero =>
      cases n with
      | zero =>
          have hphi0 := section43TransformComponent_zero_eval_eq d phi f.1 f.2 hf hphi
          have hpsi0 := section43TransformComponent_zero_eval_eq d psi g.1 g.2 hg hpsi
          have hphiV (x : NPointDomain d 0) : phi x = f.1 0 :=
            (congrArg phi (Subsingleton.elim x 0)).trans hphi0
          have hpsiV (x : NPointDomain d 0) : psi x = g.1 0 :=
            (congrArg psi (Subsingleton.elim x 0)).trans hpsi0
          have hfV (x : NPointDomain d 0) : f.1 x = f.1 0 := congrArg f.1 (Subsingleton.elim x 0)
          have hgV (x : NPointDomain d 0) : g.1 x = g.1 0 := congrArg g.1 (Subsingleton.elim x 0)
          change (phi.conjTensorProduct psi) 0 = OS.S 0 _
          rw [lgc.normalized_zero, ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
            (f.1.osConjTensorProduct g.1)
            (VanishesToInfiniteOrderOnCoincidence_zero_degree (f.1.osConjTensorProduct g.1))]
          change starRingEnd Complex (phi _) * psi _ =
            starRingEnd Complex (f.1 _) * g.1 _
          simp only [hphiV, hpsiV, hfV, hgV]
      | succ n =>
          let W := fun k f => initial.strictGeneratedFullBoundary lgc k f
          have hlinear (k : Nat) : IsLinearMap Complex (W k) :=
            ⟨(initial.strictGeneratedFullBoundary lgc k).map_add,
              (initial.strictGeneratedFullBoundary lgc k).map_smul⟩
          have hW := WightmanInnerProduct_hermitian_of W
            (initial.strictGeneratedFullBoundary_hermitian lgc)
            (BorchersSequence.single (n + 1) phi) (BorchersSequence.single 0 psi)
          simp only [WightmanInnerProduct_single_single d W hlinear] at hW
          have hOS := PositiveTimeBorchersSequence.osInner_hermitian OS
            (PositiveTimeBorchersSequence.single (n + 1) f.1 f.2)
            (PositiveTimeBorchersSequence.single 0 g.1 g.2)
          simp only [PositiveTimeBorchersSequence.osInner,
            PositiveTimeBorchersSequence.single_toBorchersSequence,
            OSInnerProduct_single_single d OS.S OS.E0_linear] at hOS
          calc
            _ = starRingEnd Complex (initial.strictGeneratedFullBoundary lgc (0 + (n + 1))
                (psi.conjTensorProduct phi)) := hW
            _ = starRingEnd Complex (OS.S (0 + (n + 1))
                (ZeroDiagonalSchwartz.ofClassical (g.1.osConjTensorProduct f.1))) :=
              congrArg (starRingEnd Complex)
                (initial.strictGeneratedFullBoundary_sourcePairing_succRight_of_transformComponent
                  lgc 0 n psi phi g f hg hf hpsi hphi)
            _ = _ := hOS.symm

private theorem finiteSourceQuadratic_nonneg
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (B : Nat)
    (p : (n : Fin (B + 1)) -> SchwartzNPoint d n.val) :
    0 ≤ (∑ n : Fin (B + 1), ∑ m : Fin (B + 1),
      initial.strictGeneratedFullBoundary lgc (n.val + m.val)
        ((p n).conjTensorProduct (p m))).re := by
  let Q := fun p : (n : Fin (B + 1)) -> SchwartzNPoint d n.val =>
    ∑ n : Fin (B + 1), ∑ m : Fin (B + 1),
      initial.strictGeneratedFullBoundary lgc (n.val + m.val)
        ((p n).conjTensorProduct (p m))
  have hQ : Continuous Q := by
    apply continuous_finset_sum
    intro n _
    apply continuous_finset_sum
    intro m _
    have hpair : Continuous
        (fun p : (n : Fin (B + 1)) -> SchwartzNPoint d n.val => (p n, p m)) :=
      (continuous_apply n).prodMk (continuous_apply m)
    exact (initial.strictGeneratedFullBoundary lgc _).continuous.comp
      ((conjTensorProduct_continuous_closure (d := d) (n := n.val) (m := m.val)).comp hpair)
  have hdense := dense_pi (Set.univ : Set (Fin (B + 1)))
    (fun n _ => dense_section43FourierLaplace_compact_ordered_frequency_preimage d n.val)
  refine hdense.induction (P := fun p => 0 ≤ (Q p).re) ?_
    (isClosed_le continuous_const (Complex.continuous_re.comp hQ)) p
  intro p hp
  have hsrc : ∀ n : Fin (B + 1), ∃ src : Section43CompactOrderedSource d n.val,
      section43FourierLaplaceTransformComponentMap d n.val src =
        section43FrequencyProjection d n.val (p n) := fun n => hp n (by trivial)
  choose src hsrc using hsrc
  let F := section43FiniteSource_to_positiveTimeBorchersSequence d B src
  have hpair : Q p = PositiveTimeBorchersSequence.osInner OS F F := by
    unfold Q PositiveTimeBorchersSequence.osInner OSInnerProduct
    change (∑ n : Fin (B + 1), ∑ m : Fin (B + 1),
      initial.strictGeneratedFullBoundary lgc (n.val + m.val) ((p n).conjTensorProduct (p m))) =
      ∑ n ∈ Finset.range (B + 1), ∑ m ∈ Finset.range (B + 1),
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (((F : BorchersSequence d).funcs n).osConjTensorProduct ((F : BorchersSequence d).funcs m)))
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt := Finset.mem_range.mp hn
    rw [dif_pos hnlt, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    have hmlt := Finset.mem_range.mp hm
    rw [dif_pos hmlt]
    have hFn : (F : BorchersSequence d).funcs n = (src ⟨n, hnlt⟩).f := by
      simp [F, section43FiniteSource_to_positiveTimeBorchersSequence, Nat.lt_succ_iff.mp hnlt]
    have hFm : (F : BorchersSequence d).funcs m = (src ⟨m, hmlt⟩).f := by
      simp [F, section43FiniteSource_to_positiveTimeBorchersSequence, Nat.lt_succ_iff.mp hmlt]
    rw [hFn, hFm]
    exact initial.strictGeneratedFullBoundary_sourcePairing lgc n m (p ⟨n, hnlt⟩) (p ⟨m, hmlt⟩)
      ⟨(src ⟨n, hnlt⟩).f, (src ⟨n, hnlt⟩).ordered⟩
      ⟨(src ⟨m, hmlt⟩).f, (src ⟨m, hmlt⟩).ordered⟩
      (src ⟨n, hnlt⟩).compact (src ⟨m, hmlt⟩).compact
      (hsrc ⟨n, hnlt⟩).symm (hsrc ⟨m, hmlt⟩).symm
  change 0 ≤ (Q p).re
  rw [hpair]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

/-- Coupled positivity for every finite full-Schwartz Borchers sequence. -/
theorem strictGeneratedFullBoundary_positive
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (F : BorchersSequence d) :
    0 ≤ (WightmanInnerProduct d (fun n f => initial.strictGeneratedFullBoundary lgc n f) F F).re := by
  have h := initial.finiteSourceQuadratic_nonneg lgc F.bound (fun n => F.funcs n.val)
  have heq : (∑ n : Fin (F.bound + 1), ∑ m : Fin (F.bound + 1),
      initial.strictGeneratedFullBoundary lgc (n.val + m.val)
        ((F.funcs n.val).conjTensorProduct (F.funcs m.val))) =
      WightmanInnerProduct d (fun n f => initial.strictGeneratedFullBoundary lgc n f) F F := by
    unfold WightmanInnerProduct
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    rw [dif_pos (Finset.mem_range.mp hn), Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    rw [dif_pos (Finset.mem_range.mp hm)]
  exact heq ▸ h

/-- Positivity is a real nonnegative complex value, not only a bound on its
real part. Hermiticity here has an independent nonempty-source proof. -/
theorem strictGeneratedFullBoundary_positive_real
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (F : BorchersSequence d) :
    ∃ r : Real, 0 ≤ r ∧
      WightmanInnerProduct d (fun n f => initial.strictGeneratedFullBoundary lgc n f) F F = r := by
  let q := WightmanInnerProduct d (fun n f => initial.strictGeneratedFullBoundary lgc n f) F F
  have hq : q = starRingEnd Complex q :=
    WightmanInnerProduct_hermitian_of _ (initial.strictGeneratedFullBoundary_hermitian lgc) F F
  have him : q.im = 0 := by
    have h := congrArg Complex.im hq
    simp only [Complex.conj_im] at h
    linarith
  refine ⟨q.re, initial.strictGeneratedFullBoundary_positive lgc F, ?_⟩
  change q = (q.re : Complex)
  exact Complex.ext rfl (by simpa using him)

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
