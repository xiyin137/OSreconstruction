import Definitions
import OSReconstruction.Specification.Wightman

noncomputable section
open MeasureTheory Complex Filter Set Topology Matrix
namespace OSReconstructionAudit

example {d : ℕ} [NeZero d] : ConnectedLorentz d = LorentzGroup d := rfl
example {d : ℕ} [NeZero d] (W : Family d) :
    lorentzCovariant d W = IsLorentzCovariantWeak d W := rfl
example {d : ℕ} [NeZero d] (W : Family d) :
    adjacentLocality d W = IsAdjacentLocallyCommutativeWeak d W := rfl
example {d n : ℕ} [NeZero d] (f : Test d n) :
    fourier d n f = SchwartzNPointSpace.fourierTransform d f := rfl
example {d n : ℕ} [NeZero d] (f : Test d (n + 1)) (ξ : Config d n) :
    reduceBasepoint d n f ξ = diffVarReduction d n f ξ := rfl
example {d : ℕ} [NeZero d] (W : Family d) :
    forwardAnalyticity d W = ForwardTubeAnalyticityCompactSubset d W := rfl

theorem spectralSupport_iff {d : ℕ} [NeZero d] (W : Family d) :
    spectralSupport d W ↔ SpectralConditionDistribution d W := by
  constructor
  · intro h n
    obtain ⟨w, hc, hl, hr, hs⟩ := h n
    refine ⟨w, hc, hl, ?_, hs⟩
    intro f
    obtain ⟨g, hg, hwg⟩ := hr f
    have heq : g = diffVarReduction d n f := by ext ξ; exact hg ξ
    simpa [heq] using hwg
  · intro h n
    obtain ⟨w, hc, hl, hr, hs⟩ := h n
    refine ⟨w, hc, hl, ?_, hs⟩
    intro f
    exact ⟨diffVarReduction d n f, (fun _ => rfl), hr f⟩

/-- The tensor witness is unique and agrees with the production wrapper. -/
theorem tensorRelation_iff {d n m : ℕ} (f : Test d n) (g : Test d m)
    (h : Test d (n + m)) : tensorRelation f g h ↔ h = f.tensorProduct g := by
  constructor
  · intro hh; ext x; exact hh x
  · intro hh; subst h; intro x; rfl

/-- The conjugate tensor witness includes reversal in the first factor. -/
theorem conjugateTensorRelation_iff {d n m : ℕ} (f : Test d n) (g : Test d m)
    (h : Test d (n + m)) :
    conjugateTensorRelation f g h ↔ h = f.conjTensorProduct g := by
  constructor
  · intro hh; ext x; exact hh x
  · intro hh; subst h; intro x; rfl

def Borchers.toProduction {d : ℕ} (F : Borchers d) : BorchersSequence d :=
  ⟨F.funcs, F.bound, F.bound_spec⟩

def Borchers.ofProduction {d : ℕ} (F : BorchersSequence d) : Borchers d :=
  ⟨F.funcs, F.bound, F.bound_spec⟩

theorem positiveDefinite_iff {d : ℕ} [NeZero d] (W : Family d) :
    positiveDefinite d W ↔ _root_.Wightman.IsPositiveDefinite d W := by
  constructor
  · intro h F
    exact h (Borchers.ofProduction F)
      (fun n m => (F.funcs n).conjTensorProduct (F.funcs m))
      (fun _ _ _ => rfl)
  · intro h F H hH
    have heq : H = fun n m => (F.funcs n).conjTensorProduct (F.funcs m) := by
      funext n m
      exact (conjugateTensorRelation_iff _ _ _).mp (hH n m)
    rw [heq]
    exact h (Borchers.toProduction F)

/-- Adapt the independent fields to the complete production record. -/
def Wightman.toProduction {d : ℕ} [NeZero d] (A : Wightman d) : WightmanFunctions d where
  W := A.W
  linear := A.linear
  tempered := A.tempered
  normalized := A.normalized
  translation_invariant := A.translation_invariant
  lorentz_covariant := A.lorentz_covariant
  spectrum_condition := A.spectrum_condition
  spectral_support := (spectralSupport_iff A.W).mp A.spectral_support
  locally_commutative := A.locally_commutative
  positive_definite := (positiveDefinite_iff A.W).mp A.positive_definite
  hermitian := A.hermitian
  cluster := by
    intro n m f g ε hε
    obtain ⟨R, hR, h⟩ := A.cluster n m f g ε hε
    refine ⟨R, hR, ?_⟩
    intro a ha hlarge ga hga
    exact h a ha hlarge ga hga (f.tensorProduct ga) (fun _ => rfl)

/-- Recover every independent axiom from the production theorem's result. -/
def Wightman.ofProduction {d : ℕ} [NeZero d] (A : WightmanFunctions d) : Wightman d where
  W := A.W
  linear := A.linear
  tempered := A.tempered
  normalized := A.normalized
  translation_invariant := A.translation_invariant
  lorentz_covariant := A.lorentz_covariant
  spectrum_condition := A.spectrum_condition
  spectral_support := (spectralSupport_iff A.W).mpr A.spectral_support
  locally_commutative := A.locally_commutative
  positive_definite := (positiveDefinite_iff A.W).mpr A.positive_definite
  hermitian := A.hermitian
  cluster := by
    intro n m f g ε hε
    obtain ⟨R, hR, h⟩ := A.cluster n m f g ε hε
    refine ⟨R, hR, ?_⟩
    intro a ha hlarge ga hga t ht
    rw [(tensorRelation_iff _ _ _).mp ht]
    exact h a ha hlarge ga hga

@[simp] theorem Wightman.toProduction_W {d : ℕ} [NeZero d] (A : Wightman d) :
    A.toProduction.W = A.W := rfl

@[simp] theorem Wightman.ofProduction_W {d : ℕ} [NeZero d] (A : WightmanFunctions d) :
    (Wightman.ofProduction A).W = A.W := rfl

@[simp] theorem Wightman.toProduction_ofProduction {d : ℕ} [NeZero d]
    (A : WightmanFunctions d) : (Wightman.ofProduction A).toProduction = A := by
  cases A
  rfl

@[simp] theorem Wightman.ofProduction_toProduction {d : ℕ} [NeZero d]
    (A : Wightman d) : Wightman.ofProduction A.toProduction = A := by
  cases A
  rfl

/-- No independent field adds or removes an assumption on a family. -/
theorem wightman_iff {d : ℕ} [NeZero d] (W : Family d) :
    (∃ A : Wightman d, A.W = W) ↔ (∃ A : WightmanFunctions d, A.W = W) := by
  constructor
  · rintro ⟨A, rfl⟩; exact ⟨A.toProduction, rfl⟩
  · rintro ⟨A, rfl⟩; exact ⟨Wightman.ofProduction A, rfl⟩

end OSReconstructionAudit
