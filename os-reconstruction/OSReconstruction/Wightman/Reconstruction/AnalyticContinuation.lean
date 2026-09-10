/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry
import Init
import OSReconstruction.SCV.SeparatelyAnalytic
import OSReconstruction.SCV.EdgeOfWedge
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Core
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Preconnected
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.MvPolynomial.Basic
import OSReconstruction.ComplexLieGroups.SOConnected
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Topology.LocallyConstant.Basic
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow
import OSReconstruction.Bridge.AxiomBridge
import Mathlib.Data.Fin.Tuple.Sort




































































noncomputable section

open Complex

variable {d : ℕ} [NeZero d]















/-- The extended forward tube using the full complex Lorentz group.

    T'_n = ⋃_{Λ ∈ L₊(ℂ)} Λ(T_n)

    Note: WightmanAxioms.lean defined `ExtendedForwardTube` using only the real
    connected proper-orthochronous Lorentz group. Here we use the full complex Lorentz group, which
    gives a strictly larger domain. The two are related by:
      ExtendedForwardTube ⊂ ComplexExtendedForwardTube ⊂ PermutedExtendedTube -/
def ComplexExtendedForwardTube (d n : ℕ) [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
    w ∈ ForwardTube d n ∧
    z = fun k μ => ∑ ν, Λ.val μ ν * w k ν }

/-- The permuted forward tube for permutation π.

    π(T_n) = {z ∈ ℂ^{n(d+1)} : (z_{π(1)}, ..., z_{π(n)}) ∈ T_n}

    Different permutations impose different orderings on the imaginary parts. -/
def PermutedForwardTube (d n : ℕ) [NeZero d] (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

/-- The permuted extended tube T''_n = ⋃_{π ∈ S_n} π(T'_n)

    This is the union over all permutations of the complex-extended forward tubes.
    The BHW theorem says Wightman functions extend holomorphically to (the envelope
    of holomorphy of) this domain. -/
def PermutedExtendedTube (d n : ℕ) [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = fun k μ => ∑ ν, Λ.val μ ν * w k ν }

/-- The forward tube is contained in the complex extended forward tube
    (take Λ = identity). -/
theorem ForwardTube_subset_ComplexExtended (d n : ℕ) [NeZero d] :
    ForwardTube d n ⊆ ComplexExtendedForwardTube d n := by
  intro z hz
  refine ⟨⟨1, ?_, ?_⟩, z, hz, ?_⟩
  · -- Identity preserves metric: Σ_α η(α) · δ_{αμ} · δ_{αν} = η(μ) · δ_{μν}
    intro μ ν
    simp only [Matrix.one_apply]
    by_cases h : μ = ν
    · subst h; simp [Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [h, ite_false]
      apply Finset.sum_eq_zero
      intro α _
      split_ifs <;> simp_all
  · simp [Matrix.det_one]
  · ext k μ; simp [Matrix.one_apply, Finset.mem_univ]

/-- The complex extended forward tube is contained in the permuted extended tube
    (take π = identity). -/
theorem ComplexExtended_subset_Permuted (d n : ℕ) [NeZero d] :
    ComplexExtendedForwardTube d n ⊆ PermutedExtendedTube d n := by
  intro z ⟨Λ, w, hw, hz⟩
  simp only [PermutedExtendedTube, Set.mem_iUnion]
  exact ⟨Equiv.refl _, Λ, w, by simpa [PermutedForwardTube] using hw, hz⟩



/-- Euclidean points with increasing times are in the forward tube.

    If 0 < τ₀ < τ₁ < ... < τₙ₋₁ (strictly increasing positive Euclidean times),
    then the Wick-rotated points (iτ₀, x⃗₀), ..., (iτₙ₋₁, x⃗ₙ₋₁) lie in the forward tube.

    The imaginary part differences are:
      Im(z_k - z_{k-1})₀ = τ_k - τ_{k-1} > 0   (time component)
      Im(z_k - z_{k-1})_μ = 0                     (spatial, μ ≥ 1)
    so η = (τ_k - τ_{k-1}, 0,...,0) has positive time and zero spatial part.
    The Minkowski norm η² = -(τ_k - τ_{k-1})² < 0, so η ∈ V₊. -/
theorem euclidean_ordered_in_forwardTube
    (xs : Fin n → Fin (d + 1) → ℝ)
    (hord : ∀ k j : Fin n, k < j → xs k 0 < xs j 0)
    (hpos : ∀ k : Fin n, xs k 0 > 0) :
    (fun k => wickRotatePoint (xs k)) ∈ ForwardTube d n := by
  intro k
  -- η_μ = Im(z_k μ - prev μ) where prev = 0 if k=0, z_{k-1} if k≥1
  -- For Wick-rotated points: η = (τ_k - τ_{k-1}, 0, ..., 0)
  -- which has positive time and negative Minkowski norm
  constructor
  · -- η 0 > 0 (positive time component)
    dsimp
    split_ifs with hk
    · -- k = 0: Im(wickRotatePoint(xs k) 0 - 0) = xs k 0 > 0
      simp only [wickRotatePoint, ite_true, Pi.zero_apply,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
        Complex.zero_im, sub_zero, zero_add]
      exact hpos k
    · -- k ≥ 1: Im(i*τ_k - i*τ_{k-1}) = τ_k - τ_{k-1} > 0
      simp only [wickRotatePoint, ite_true,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
      have hlt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
        simp only [Fin.lt_def]; omega
      linarith [hord ⟨k.val - 1, by omega⟩ k hlt]
  · -- minkowskiNormSq η < 0 (purely timelike, so η² = -η₀² < 0)
    dsimp
    simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature]
    -- Split sum: i=0 term + sum of spatial terms
    rw [Fin.sum_univ_succ]
    simp only [Fin.succ_ne_zero, ite_false, ite_true, one_mul]
    -- Spatial imaginary parts vanish: Im(wickRotatePoint x μ) = 0 for μ ≠ 0
    have hspatial : ∀ i : Fin d,
        (wickRotatePoint (xs k) i.succ).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) i.succ).im = 0 := by
      intro i
      simp only [wickRotatePoint, Fin.succ_ne_zero, ite_false, Complex.ofReal_im]
      split_ifs with hk
      · simp [Complex.zero_im]
      · simp [wickRotatePoint, Fin.succ_ne_zero, Complex.ofReal_im]
    simp only [hspatial, mul_zero, Finset.sum_const_zero, add_zero]
    -- Goal: -1 * η₀ * η₀ < 0, where η₀ = time difference > 0
    have heta_pos : (wickRotatePoint (xs k) 0).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) 0).im > 0 := by
      simp only [wickRotatePoint, ite_true, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
      split_ifs with hk
      · simp only [Pi.zero_apply, Complex.zero_im, sub_zero]; exact hpos k
      · simp only [wickRotatePoint, ite_true, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        have hlt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
          simp only [Fin.lt_def]; omega
        linarith [hord ⟨k.val - 1, by omega⟩ k hlt]
    nlinarith [sq_nonneg ((wickRotatePoint (xs k) 0).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) 0).im)]

/-- For any configuration of distinct Euclidean points with positive times,
    there exists a permutation that orders the times, placing the permuted
    configuration in the forward tube.

    This is the key geometric fact: **all** distinct positive-time Euclidean
    points lie in the permuted extended tube, not just the time-ordered ones.

    The positive time condition is natural for Osterwalder-Schrader reconstruction,
    where Schwinger functions are defined for positive Euclidean times. -/
theorem euclidean_distinct_in_permutedTube {n : ℕ}
    (xs : Fin n → Fin (d + 1) → ℝ)
    (hdistinct : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0)
    (hpos : ∀ i : Fin n, xs i 0 > 0) :
    (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n := by
  -- Step 1: Find a sorting permutation π such that times are strictly increasing
  let π := Tuple.sort (fun k => xs k 0)
  have hmono := Tuple.monotone_sort (fun k => xs k 0)
  -- Times are distinct, hence injective
  have hinj : Function.Injective (fun k => xs k 0) := by
    intro i j h; by_contra hij; exact hdistinct i j hij h
  -- Monotone + injective = strictly monotone
  have hstrict : StrictMono ((fun k => xs k 0) ∘ π) :=
    hmono.strictMono_of_injective (hinj.comp π.injective)
  -- Step 2: The permuted configuration is time-ordered with positive times
  have hord : ∀ k j : Fin n, k < j → xs (π k) 0 < xs (π j) 0 :=
    fun k j hkj => hstrict hkj
  have hpos' : ∀ k : Fin n, xs (π k) 0 > 0 := fun k => hpos (π k)
  -- Step 3: Apply euclidean_ordered_in_forwardTube to get forward tube membership
  have hfwd : (fun k => wickRotatePoint (xs (π k))) ∈ ForwardTube d n :=
    euclidean_ordered_in_forwardTube (fun k => xs (π k)) hord hpos'
  -- Step 4: This gives PermutedForwardTube membership (by definition)
  -- PermutedForwardTube d n π = { z | (fun k => z (π k)) ∈ ForwardTube d n }
  -- So z = (fun k => wickRotatePoint (xs k)) is in PermutedForwardTube d n π
  -- Step 5: Use the identity complex Lorentz to get PermutedExtendedTube membership
  simp only [PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨π, ?_⟩
  -- Construct the identity complex Lorentz transformation
  refine ⟨⟨1, ?_, by simp [Matrix.det_one]⟩, fun k => wickRotatePoint (xs k), hfwd, ?_⟩
  · -- Identity preserves metric
    intro μ ν
    simp only [Matrix.one_apply]
    by_cases h : μ = ν
    · subst h; simp [Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [h, ite_false]
      apply Finset.sum_eq_zero; intro α _; split_ifs <;> simp_all
  · -- z = 1 · w = w
    ext k μ; simp [Matrix.one_apply, Finset.mem_univ]



/- The edge-of-the-wedge theorem (Bogoliubov).

    This is a deep result in several complex variables. The simplest version states:

    Let C ⊂ ℝⁿ be an open convex cone, and let T₊ = ℝⁿ + iC, T₋ = ℝⁿ - iC be
    the corresponding tube domains. If f₊ : T₊ → ℂ and f₋ : T₋ → ℂ are holomorphic,
    and their boundary values (as distributions) agree on an open set E ⊂ ℝⁿ:
      lim_{ε→0⁺} f₊(x + iεη) = lim_{ε→0⁺} f₋(x - iεη) for x ∈ E
    then there exists a holomorphic function F on a complex neighborhood of E that
    agrees with f₊ on T₊ ∩ U and f₋ on T₋ ∩ U for some open U.

    This is the mathematical backbone of the BHW theorem: it allows "gluing"
    analytic continuations from overlapping tube domains. -/






















/-- The BHW forward tube equals the Wightman forward tube. -/
theorem BHW_forwardTube_eq : BHW.ForwardTube d n = ForwardTube d n := by
  ext z; simp only [BHW.ForwardTube, ForwardTube, Set.mem_setOf_eq]
  exact forall_congr' fun k => inOpenForwardCone_iff _

/-- The BHW permuted forward tube equals the Wightman permuted forward tube. -/
theorem BHW_permutedForwardTube_eq (π : Equiv.Perm (Fin n)) :
    BHW.PermutedForwardTube d n π = PermutedForwardTube d n π := by
  ext z; simp only [BHW.PermutedForwardTube, PermutedForwardTube, Set.mem_setOf_eq]
  rw [← BHW_forwardTube_eq]

/-- The BHW permuted extended tube equals the Wightman permuted extended tube. -/
theorem BHW_permutedExtendedTube_eq :
    BHW.PermutedExtendedTube d n = PermutedExtendedTube d n := by
  have hft := BHW_forwardTube_eq (d := d) (n := n)
  ext z
  simp only [BHW.PermutedExtendedTube, PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq,
    BHW.PermutedForwardTube, PermutedForwardTube]
  constructor
  · rintro ⟨π, Λ, w, hw, hz⟩
    refine ⟨π, Λ, w, hft ▸ hw, ?_⟩
    rw [hz]; rfl
  · rintro ⟨π, Λ, w, hw, hz⟩
    refine ⟨π, Λ, w, hft ▸ hw, ?_⟩
    rw [hz]; rfl

/-- **The Bargmann-Hall-Wightman (BHW) theorem.**

    Given a holomorphic function F on the forward tube T_n that is:
    1. Invariant under the real Lorentz group L₊↑
    2. Continuously extends to the real boundary (`hF_bv`)
    3. Has boundary values satisfying local commutativity at spacelike pairs (`hF_local`)

    Then F extends uniquely to a holomorphic function F_ext on the permuted extended
    tube T''_n, and the extension is:
    1. Invariant under the complex Lorentz group L₊(ℂ)
    2. Invariant under all permutations of the arguments
    3. Unique (any other holomorphic extension agreeing with F on the forward tube
       must equal F_ext on the permuted extended tube)

    **Note on the boundary data:** Real points lie outside the forward tube
    (Im = 0 ∉ V₊), so the theorem is phrased using the honest distributional
    boundary functional `W` and weak local commutativity on Schwartz tests,
    rather than pointwise values of a total function on the real edge.

    **Proof:** Delegates to `BHW.bargmann_hall_wightman_theorem` from
    `Connectedness.lean` via the `AxiomBridge` type conversions.

    References:
    - Bargmann, Hall, Wightman (1957), Nuovo Cimento 5, 1-14
    - Streater & Wightman, PCT Spin and Statistics, Theorem 2-11
    - Jost (1965), The General Theory of Quantized Fields, Ch. IV -/
theorem bargmann_hall_wightman (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f)))
    (hF_local_dist : IsAdjacentLocallyCommutativeWeak d W) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) ∧
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z) := by
  -- Convert hypotheses from Wightman types to BHW types
  have hft_eq := BHW_forwardTube_eq (d := d) (n := n)
  have hpet_eq := BHW_permutedExtendedTube_eq (d := d) (n := n)
  have hF_holo' : DifferentiableOn ℂ F (BHW.ForwardTube d n) :=
    hft_eq ▸ hF_holo
  have hF_lorentz' : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z := by
    intro Λ z hz
    have hz' : z ∈ ForwardTube d n := hft_eq ▸ hz
    exact hF_lorentz (lorentzGroupToWightman Λ) z hz'
  -- Apply BHW theorem from Connectedness.lean
  obtain ⟨F_ext, h1, h2, h3, h4, h5⟩ :=
    BHW.bargmann_hall_wightman_theorem n F hF_holo' hF_lorentz' W hF_bv_dist hF_local_dist
  -- Convert the result back from BHW types to Wightman types
  refine ⟨F_ext, ?_, ?_, ?_, ?_, ?_⟩
  · -- DifferentiableOn on PermutedExtendedTube
    rwa [← hpet_eq]
  · -- Restriction to ForwardTube
    intro z hz
    exact h2 z (hft_eq ▸ hz)
  · -- Complex Lorentz invariance
    intro Λ z hz
    have hz' : z ∈ BHW.PermutedExtendedTube d n := hpet_eq ▸ hz
    have := h3 Λ z hz'
    rwa [show BHW.complexLorentzAction Λ z = fun k μ => ∑ ν, Λ.val μ ν * z k ν from rfl] at this
  · -- Permutation invariance
    intro π z hz
    exact h4 π z (hpet_eq ▸ hz)
  · -- Uniqueness
    intro G hG_holo hG_eq z hz
    have hz' : z ∈ BHW.PermutedExtendedTube d n := hpet_eq ▸ hz
    exact h5 G (hpet_eq ▸ hG_holo)
      (fun w hw => hG_eq w (hft_eq ▸ hw)) z hz'





/-- Define Schwinger functions from Wightman functions using analytic continuation.

    Given Wightman functions W_n with analytic continuation W_analytic to the forward tube,
    the Schwinger functions are defined by evaluating W_analytic at Euclidean points:

      S_n(τ₁, x⃗₁, ..., τₙ, x⃗ₙ) = W_analytic_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ)

    for τ₁ > τ₂ > ... > τₙ > 0 (time-ordered Euclidean points lie in the forward tube).

    By the BHW theorem, the analytic continuation extends to the permuted extended tube,
    making S_n pointwise well-defined on the currently formalized PET subregions
    (notably positive-time and common-half-space Euclidean configurations), and
    a.e. well-defined for general Euclidean configurations. -/
def SchwingerFromWightman (d : ℕ) [NeZero d]
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (n : ℕ) → (Fin n → Fin (d + 1) → ℝ) → ℂ :=
  fun n xs => W_analytic n (fun k => wickRotatePoint (xs k))











omit [NeZero d] in
/-- The Wick rotation intertwines Euclidean rotations with complex Lorentz transformations:
    wickRotatePoint(R · x) = (ofEuclidean R) · wickRotatePoint(x)

    For R ∈ SO(d+1), the diagram commutes:
      ℝ^{d+1} --R--> ℝ^{d+1}
        |                |
    wick             wick
        |                |
      ℂ^{d+1} --Λ_R-> ℂ^{d+1}  -/
theorem wickRotatePoint_ofEuclidean
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (x : Fin (d + 1) → ℝ) :
    ∀ μ : Fin (d + 1),
      wickRotatePoint (R.mulVec x) μ =
      ∑ ν, (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val μ ν *
        wickRotatePoint x ν := by
  intro μ
  simp only [wickRotatePoint, ComplexLorentzGroup.ofEuclidean, Matrix.mulVec, dotProduct]
  -- Each summand on RHS: (wμ * R(μ,ν) * wν⁻¹) * wickRotatePoint(x)(ν)
  -- For ν=0: wμ * R(μ,0) * (-I) * (I * x(0)) = wμ * R(μ,0) * x(0)  [since -I*I = 1]
  -- For ν≠0: wμ * R(μ,ν) * 1 * x(ν) = wμ * R(μ,ν) * x(ν)
  -- So RHS = wμ * Σ_ν R(μ,ν) * x(ν) = LHS
  -- First, simplify each summand via -I*I = 1
  have simplify_summand : ∀ ν : Fin (d + 1),
      (if μ = 0 then I else (1 : ℂ)) * ↑(R μ ν) * (if ν = 0 then -I else 1) *
      (if ν = 0 then I * ↑(x 0) else ↑(x ν)) =
      (if μ = 0 then I else (1 : ℂ)) * ↑(R μ ν) * ↑(x ν) := by
    intro ν
    by_cases hν : ν = (0 : Fin (d + 1))
    · subst hν; simp only [ite_true]
      rw [show (if μ = 0 then I else (1 : ℂ)) * ↑(R μ 0) * -I * (I * ↑(x 0)) =
        (if μ = 0 then I else (1 : ℂ)) * ↑(R μ 0) * ↑(x 0) * (-I * I) from by ring]
      rw [show (-I : ℂ) * I = -(I * I) from by ring, ← sq, Complex.I_sq]; ring
    · simp only [hν, ite_false]; ring
  simp_rw [simplify_summand]
  -- Now RHS = Σ_ν wμ * ↑(R(μ,ν)) * ↑(x(ν)) = wμ * Σ_ν ↑(R(μ,ν) * x(ν))
  by_cases hμ : μ = (0 : Fin (d + 1))
  · subst hμ; simp only [ite_true]
    rw [Complex.ofReal_sum, Finset.mul_sum]
    congr 1; ext ν; push_cast; ring
  · simp only [hμ, ite_false]
    rw [Complex.ofReal_sum]
    congr 1; ext ν; push_cast; ring

omit [NeZero d] in
/-- The transpose of an orthogonal matrix with det 1 also has det 1. -/
private lemma det_transpose_of_SO {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hR_det : R.det = 1) : R.transpose.det = 1 := by
  rw [Matrix.det_transpose]; exact hR_det

omit [NeZero d] in
/-- The transpose of an orthogonal matrix R (with RᵀR = I) satisfies (Rᵀ)ᵀRᵀ = I. -/
private lemma transpose_orth_of_SO {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hR_orth : R.transpose * R = 1) : R.transpose.transpose * R.transpose = 1 := by
  rw [Matrix.transpose_transpose]
  have : R * R.transpose = 1 := mul_eq_one_comm.mpr hR_orth
  exact this

omit [NeZero d] in
/-- The matrix product of ofEuclidean(Rᵀ) and ofEuclidean(R) is the identity.

    This follows from the fact that ofEuclidean is a group homomorphism:
    W·Rᵀ·W⁻¹ · W·R·W⁻¹ = W·(RᵀR)·W⁻¹ = W·I·W⁻¹ = I -/
private lemma ofEuclidean_transpose_mul_self
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1) :
    ∀ μ α : Fin (d + 1),
      ∑ ν, (ComplexLorentzGroup.ofEuclidean R.transpose
              (det_transpose_of_SO hR_det) (transpose_orth_of_SO hR_orth)).val μ ν *
           (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val ν α =
      if μ = α then 1 else 0 := by
  intro μ α
  simp only [ComplexLorentzGroup.ofEuclidean, Matrix.transpose_apply]
  -- Each summand: (wμ * Rᵀ(μ,ν) * wν⁻¹) * (wν * R(ν,α) * wα⁻¹)
  -- = wμ * Rᵀ(μ,ν) * R(ν,α) * wα⁻¹  [since wν⁻¹ * wν = 1]
  have simplify : ∀ ν : Fin (d + 1),
      (if μ = 0 then I else (1 : ℂ)) * ↑(R ν μ) * (if ν = 0 then -I else 1) *
      ((if ν = 0 then I else (1 : ℂ)) * ↑(R ν α) * (if α = 0 then -I else 1)) =
      (if μ = 0 then I else (1 : ℂ)) * (if α = 0 then -I else (1 : ℂ)) *
      (↑(R ν μ) * ↑(R ν α)) := by
    intro ν
    by_cases hν : ν = (0 : Fin (d + 1))
    · subst hν; simp only [ite_true]
      rw [show (if μ = 0 then I else (1 : ℂ)) * ↑(R 0 μ) * -I * (I * ↑(R 0 α) *
        (if α = 0 then -I else 1)) =
        (if μ = 0 then I else (1 : ℂ)) * (if α = 0 then -I else (1 : ℂ)) *
        (↑(R 0 μ) * ↑(R 0 α)) * (-I * I) from by ring]
      rw [show (-I : ℂ) * I = -(I * I) from by ring, ← sq, Complex.I_sq, neg_neg, mul_one]
    · simp only [hν, ite_false]; ring
  simp_rw [simplify, ← Finset.mul_sum]
  -- Now need: Σ_ν R(ν,μ) * R(ν,α) = δ_{μα}  (from RᵀR = I)
  have hRtR : ∑ ν : Fin (d + 1), (R ν μ : ℂ) * (R ν α : ℂ) =
      if μ = α then 1 else 0 := by
    have h := congr_fun (congr_fun hR_orth μ) α
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    have : ∑ ν, (R ν μ : ℂ) * (R ν α : ℂ) = (∑ ν, R ν μ * R ν α : ℝ) := by
      push_cast; rfl
    rw [this, h]; split_ifs <;> simp
  rw [hRtR]
  by_cases hμ : μ = (0 : Fin (d + 1)) <;> by_cases hα : α = (0 : Fin (d + 1))
  · -- μ = 0, α = 0
    subst hμ; subst hα; simp
  · -- μ = 0, α ≠ 0
    subst hμ; simp only [ite_true, hα, ite_false]
    have : ¬(0 : Fin (d + 1)) = α := fun h => hα h.symm
    simp only [this, ite_false]; ring
  · -- μ ≠ 0, α = 0
    subst hα; simp only [hμ, ite_false, ite_true]; ring
  · -- μ ≠ 0, α ≠ 0
    simp only [hμ, hα, ite_false]
    split_ifs <;> ring

/-- If a Wick-rotated configuration lies in PET, then applying the inverse
    Euclidean rotation's complex Lorentz embedding recovers the original
    (un-rotated) configuration in PET.

    More precisely: if (fun k => wickRotatePoint (R · x_k)) ∈ PET, then
    (fun k => wickRotatePoint (x_k)) ∈ PET, witnessed by applying
    ofEuclidean(Rᵀ) as the complex Lorentz transformation. -/
theorem PermutedExtendedTube_euclidean_preimage
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (x : Fin n → Fin (d + 1) → ℝ)
    (h : (fun k => wickRotatePoint (R.mulVec (x k))) ∈ PermutedExtendedTube d n) :
    (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n := by
  -- Unpack PET membership: there exist π, Λ, w with w ∈ PermutedForwardTube π
  simp only [PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq] at h ⊢
  obtain ⟨π, Λ, w, hw, hzw⟩ := h
  -- Use the same permutation and forward tube witness
  refine ⟨π, ?_⟩
  -- Build the new complex Lorentz transformation: ofEuclidean(Rᵀ) * Λ
  -- But we don't have a Group instance, so we compose manually
  -- First, build ofEuclidean(Rᵀ)
  let Λ_inv := ComplexLorentzGroup.ofEuclidean R.transpose
    (det_transpose_of_SO hR_det) (transpose_orth_of_SO hR_orth)
  -- We need to show wickRotatePoint(x_k) = Λ_new · w where Λ_new = Λ_inv composed with Λ
  -- Strategy: wickRotatePoint(x_k) = Λ_inv · wickRotatePoint(R · x_k) = Λ_inv · (Λ · w)
  -- By wickRotatePoint_ofEuclidean: wickRotatePoint(R · x_k) = ofEuclidean(R) · wickRotatePoint(x_k)
  -- So: wickRotatePoint(x_k) = ofEuclidean(Rᵀ) · ofEuclidean(R) · wickRotatePoint(x_k)
  --   = ofEuclidean(Rᵀ) · (Λ · w)
  -- But we want wickRotatePoint(x_k) = Λ_new · w, i.e., we need Λ_new such that
  -- Σ_ν Λ_new μ ν * w k ν = wickRotatePoint(x_k) μ
  -- From hzw: wickRotatePoint(R · x_k) = Λ · w, i.e.,
  --   Σ_ν Λ.val μ ν * w k ν = wickRotatePoint(R · x_k) μ
  --   = Σ_ν (ofEuclidean R).val μ ν * wickRotatePoint(x_k) ν
  -- So: wickRotatePoint(x_k) μ = Σ_ν (ofEuclidean Rᵀ · ofEuclidean R)_{μν} * wickRotatePoint(x_k) ν
  --   = Σ_α (ofEuclidean Rᵀ)_{μα} * Σ_ν (ofEuclidean R)_{αν} * wickRotatePoint(x_k) ν
  --   = Σ_α (ofEuclidean Rᵀ)_{μα} * wickRotatePoint(R · x_k) α
  --   = Σ_α (ofEuclidean Rᵀ)_{μα} * Σ_ν Λ_{αν} * w_k ν
  --   = Σ_ν (Σ_α (ofEuclidean Rᵀ)_{μα} * Λ_{αν}) * w_k ν
  -- Build Λ_new with val μ ν = Σ_α Λ_inv.val μ α * Λ.val α ν
  let Λ_new : ComplexLorentzGroup d := {
    val := Λ_inv.val * Λ.val
    metric_preserving := by
      intro μ ν
      have hΛ_inv := Λ_inv.metric_preserving
      have hΛ := Λ.metric_preserving
      simp only [Matrix.mul_apply]
      -- Prove: Σ_α η(α) * (Σ_j ..) * (Σ_j ..) = η(μ)*δ_{μν}
      -- = Σ_β Σ_γ (Σ_α η(α)*Λ_inv(α,β)*Λ_inv(α,γ)) * Λ(β,μ)*Λ(γ,ν)
      -- = Σ_β η(β)*Λ(β,μ)*Λ(β,ν) = η(μ)*δ_{μν}
      trans (∑ β : Fin (d + 1), ∑ γ : Fin (d + 1),
            (∑ α : Fin (d + 1), (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              Λ_inv.val α β * Λ_inv.val α γ) * (Λ.val β μ * Λ.val γ ν))
      · -- Expand product of sums and swap sum order
        trans (∑ α, ∑ β, ∑ γ, (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              Λ_inv.val α β * Λ_inv.val α γ * (Λ.val β μ * Λ.val γ ν))
        · -- Expand the product of sums
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [show (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              (∑ j, Λ_inv.val α j * Λ.val j μ) *
              (∑ j, Λ_inv.val α j * Λ.val j ν) =
            (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              ((∑ j, Λ_inv.val α j * Λ.val j μ) *
              (∑ j, Λ_inv.val α j * Λ.val j ν)) from mul_assoc _ _ _,
            Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun γ _ => ?_
          ring
        · -- Swap sums and factor out constant
          rw [Finset.sum_comm (f := fun α β => _)]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.sum_comm (f := fun α γ => _)]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [← Finset.sum_mul]
      · -- Use Λ_inv.metric_preserving and Λ.metric_preserving
        simp_rw [hΛ_inv]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        convert hΛ μ ν using 1
        refine Finset.sum_congr rfl fun β _ => ?_; ring
    proper := by
      show (Λ_inv.val * Λ.val).det = 1
      rw [Matrix.det_mul, Λ_inv.proper, Λ.proper, mul_one]
  }
  refine ⟨Λ_new, w, hw, ?_⟩
  -- Show: wickRotatePoint(x_k) = Λ_new · w
  funext k μ
  show wickRotatePoint (x k) μ = ∑ ν, (Λ_inv.val * Λ.val) μ ν * w k ν
  simp only [Matrix.mul_apply]
  -- Goal: wick(x_k)(μ) = Σ_ν (Σ_j Λ_inv(μ,j)*Λ(j,ν)) * w(k,ν)
  -- From hzw: wickRotatePoint(R · x_k)(α) = Σ_ν Λ(α,ν) * w(k,ν)
  have hzw_k : ∀ α, wickRotatePoint (R.mulVec (x k)) α =
      ∑ ν, Λ.val α ν * w k ν :=
    fun α => congr_fun (congr_fun hzw k) α
  -- Step 1: wick(x_k)(μ) = Σ_α δ_{μα} * wick(x_k)(α)
  --       = Σ_α (Σ_j Λ_inv(μ,j)*ofEuc(R)(j,α)) * wick(x_k)(α)
  --       = Σ_j Λ_inv(μ,j) * Σ_α ofEuc(R)(j,α) * wick(x_k)(α)
  --       = Σ_j Λ_inv(μ,j) * wick(R·x_k)(j)    [by wickRotatePoint_ofEuclidean]
  --       = Σ_j Λ_inv(μ,j) * Σ_ν Λ(j,ν) * w(k,ν)   [by hzw_k]
  --       = Σ_ν (Σ_j Λ_inv(μ,j) * Λ(j,ν)) * w(k,ν)  [swap sums]
  -- Build the chain step by step
  -- First, wick(x_k)(μ) = Σ_j Λ_inv(μ,j) * wick(R·x_k)(j)
  have step1 : wickRotatePoint (x k) μ =
      ∑ j, Λ_inv.val μ j * wickRotatePoint (R.mulVec (x k)) j := by
    -- Use ofEuclidean_transpose_mul_self: Σ_ν Λ_inv(μ,ν)*ofEuc(R)(ν,α) = δ_{μα}
    symm
    calc ∑ j, Λ_inv.val μ j * wickRotatePoint (R.mulVec (x k)) j
        = ∑ j, Λ_inv.val μ j * ∑ α, (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val j α *
            wickRotatePoint (x k) α := by
          congr 1; funext j
          congr 1
          exact wickRotatePoint_ofEuclidean R hR_det hR_orth (x k) j
      _ = ∑ j, ∑ α, Λ_inv.val μ j *
            (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val j α *
            wickRotatePoint (x k) α := by
          congr 1; funext j; rw [Finset.mul_sum]
          congr 1; funext α; ring
      _ = ∑ α, (∑ j, Λ_inv.val μ j *
            (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val j α) *
            wickRotatePoint (x k) α := by
          rw [Finset.sum_comm]; congr 1; funext α; rw [Finset.sum_mul]
      _ = ∑ α, (if μ = α then (1 : ℂ) else 0) * wickRotatePoint (x k) α := by
          congr 1; funext α
          congr 1
          exact ofEuclidean_transpose_mul_self R hR_det hR_orth μ α
      _ = wickRotatePoint (x k) μ := by
          simp only [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 2: substitute hzw_k and swap sums
  rw [step1]
  simp_rw [hzw_k, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Euclidean invariance of Schwinger functions follows from complex Lorentz
    invariance of the analytically continued Wightman functions.

    The key: SO(d+1) embeds into L₊(ℂ) as the subgroup of complex Lorentz
    transformations that preserve Euclidean points. -/
theorem schwinger_euclidean_invariant
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_inv : ∀ n (Λ : ComplexLorentzGroup d) z,
      z ∈ PermutedExtendedTube d n →
      W_analytic n (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = W_analytic n z)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (xs : Fin n → Fin (d + 1) → ℝ)
    (htube : (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n) :
    SchwingerFromWightman d W_analytic n (fun k => R.mulVec (xs k)) =
    SchwingerFromWightman d W_analytic n xs := by
  simp only [SchwingerFromWightman]
  -- wickRotatePoint (R.mulVec x) = Λ_R · wickRotatePoint x by wickRotatePoint_ofEuclidean
  have h : (fun k => wickRotatePoint (R.mulVec (xs k))) =
      (fun k μ => ∑ ν, (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val μ ν *
        wickRotatePoint (xs k) ν) := by
    ext k μ
    exact wickRotatePoint_ofEuclidean R hR_det hR_orth (xs k) μ
  rw [h]
  exact hW_inv n (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth)
    (fun k => wickRotatePoint (xs k)) htube

end
