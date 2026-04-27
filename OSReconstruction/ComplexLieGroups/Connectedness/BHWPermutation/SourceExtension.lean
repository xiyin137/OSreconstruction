import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeGluing
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.SCV.DistributionalUniqueness

/-!
# Source BHW extension on the permuted extended tube

This file contains the theorem-2-facing, source-coordinate Hall-Wightman data
and local support lemmas in PET language.

The unresolved Hall-Wightman/BHW branch-law theorem is deliberately kept in
the proof docs until it has a checked proof or an explicitly approved source
import boundary.  This production module only exposes the scalar-product
domains, the distributional adjacent anchor, the scalar representative data
shape, and checked local translations of compact-test equality into adjacent
scalar Gram seed equality.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d n : ℕ}

/-- Complex Minkowski Gram matrix of an ordered tuple of complex spacetime
vectors.  This is the scalar-product coordinate used by Hall-Wightman. -/
def sourceMinkowskiGram (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) * x i μ * x j μ

/-- Complex source Gram matrices are symmetric. -/
theorem sourceMinkowskiGram_symm
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℂ)
    (i j : Fin n) :
    sourceMinkowskiGram d n x i j =
      sourceMinkowskiGram d n x j i := by
  simp [sourceMinkowskiGram, mul_comm, mul_left_comm]

/-- Real Minkowski Gram matrix of an ordered tuple of real spacetime vectors. -/
def sourceRealMinkowskiGram (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    ∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ * x i μ * x j μ

/-- Real source Gram matrices are symmetric. -/
theorem sourceRealMinkowskiGram_symm
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (i j : Fin n) :
    sourceRealMinkowskiGram d n x i j =
      sourceRealMinkowskiGram d n x j i := by
  simp [sourceRealMinkowskiGram, mul_comm, mul_left_comm]

/-- The complex Hall-Wightman scalar-product variety, represented as the range
of the complex Minkowski Gram map.  For arity above the spacetime vector
dimension this is a rank-bounded algebraic variety, not an open subset of the
full matrix coordinate space. -/
def sourceComplexGramVariety (d n : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  Set.range (sourceMinkowskiGram d n)

/-- The real Hall-Wightman scalar-product variety, represented as the range of
the real Minkowski Gram map. -/
def sourceRealGramVariety (d n : ℕ) :
    Set (Fin n → Fin n → ℝ) :=
  Set.range (sourceRealMinkowskiGram d n)

/-- Coordinate permutation on complex Gram matrices. -/
def sourcePermuteComplexGram (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j => Z (σ i) (σ j)

/-- Permuting source vectors permutes the complex source Gram matrix. -/
theorem sourceMinkowskiGram_perm
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n (fun k => z (σ k)) =
      sourcePermuteComplexGram n σ (sourceMinkowskiGram d n z) := by
  ext i j
  rfl

/-- The scalar-product image of the ordinary extended tube. -/
def sourceExtendedTubeGramDomain (d n : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  sourceMinkowskiGram d n '' ExtendedTube d n

/-- Domain where both a Gram matrix and a coordinate-permuted Gram matrix
come from ordinary extended-tube configurations. -/
def sourceDoublePermutationGramDomain (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin n → ℂ) :=
  {Z | Z ∈ sourceExtendedTubeGramDomain d n ∧
    sourcePermuteComplexGram n σ Z ∈ sourceExtendedTubeGramDomain d n}

/-- Expected dimension of the regular Hall-Wightman scalar-product variety.
For spacetime vector dimension `D = d + 1` and `m = min n D`, this is
`n * m - m * (m - 1) / 2`.  In four spacetime dimensions this is
`1, 3, 6, 10, 4n - 6`, the dimension count used by Hall-Wightman. -/
def sourceGramExpectedDim (d n : ℕ) : ℕ :=
  let m := min n (d + 1)
  n * m - (m * (m - 1)) / 2

/-- Real span of the source vectors in spacetime. -/
def sourceConfigurationSpan (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Submodule ℝ (Fin (d + 1) → ℝ) :=
  Submodule.span ℝ (Set.range x)

/-- Complex span of the source vectors in complexified spacetime. -/
def sourceComplexConfigurationSpan (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Submodule ℂ (Fin (d + 1) → ℂ) :=
  Submodule.span ℂ (Set.range z)

/-- Regular real configurations are maximal-span configurations.  For the
nondegenerate Minkowski form this is the regular stratum of the source Gram
map onto the Hall-Wightman scalar-product variety. -/
def SourceGramRegularAt (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) : Prop :=
  Module.finrank ℝ (sourceConfigurationSpan d n x) = min n (d + 1)

/-- Regular complex configurations are maximal-span configurations. -/
def SourceComplexGramRegularAt (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  Module.finrank ℂ (sourceComplexConfigurationSpan d n z) = min n (d + 1)

/-- A concrete maximal-span template used in the source Gram regular-locus
geometry: the available coordinate basis vectors appear among the first
`min n (d + 1)` source vectors, and later source vectors are zero. -/
def sourceFullSpanTemplate (d n : ℕ) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ.val = k.val then 1 else 0

/-- Coordinate permutation on real Gram matrices. -/
def sourcePermuteGram (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (G : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => G (σ i) (σ j)

/-- Permuting source vectors permutes the real source Gram matrix. -/
theorem sourceRealMinkowskiGram_perm
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealMinkowskiGram d n (fun k => x (σ k)) =
      sourcePermuteGram n σ (sourceRealMinkowskiGram d n x) := by
  ext i j
  rfl

/-- The canonical complexification of a real Gram matrix. -/
def sourceRealGramComplexify (n : ℕ)
    (G : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℂ :=
  fun i j => (G i j : ℂ)

/-- Complexifying a permuted real Gram matrix agrees with permuting the
complexified Gram matrix. -/
theorem sourceRealGramComplexify_perm
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (G : Fin n → Fin n → ℝ) :
    sourceRealGramComplexify n (sourcePermuteGram n σ G) =
      sourcePermuteComplexGram n σ (sourceRealGramComplexify n G) := by
  ext i j
  rfl

/-- Complexifying a real source Gram matrix agrees with the complex source Gram
matrix of the real embedding. -/
theorem sourceMinkowskiGram_realEmbed
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceMinkowskiGram d n (realEmbed x) =
      sourceRealGramComplexify n (sourceRealMinkowskiGram d n x) := by
  ext i j
  simp [sourceMinkowskiGram, sourceRealMinkowskiGram,
    sourceRealGramComplexify, realEmbed]

/-- The complexification of any realized real Gram matrix lies in the complex
Hall-Wightman scalar-product variety. -/
theorem sourceRealGramComplexify_mem_sourceComplexGramVariety
    (d n : ℕ)
    {G : Fin n → Fin n → ℝ}
    (hG : G ∈ sourceRealGramVariety d n) :
    sourceRealGramComplexify n G ∈ sourceComplexGramVariety d n := by
  rcases hG with ⟨x, rfl⟩
  exact ⟨realEmbed x, sourceMinkowskiGram_realEmbed d n x⟩

/-- Relative openness in the complex Hall-Wightman scalar-product variety. -/
def IsRelOpenInSourceComplexGramVariety
    (d n : ℕ)
    (U : Set (Fin n → Fin n → ℂ)) : Prop :=
  ∃ U0 : Set (Fin n → Fin n → ℂ),
    IsOpen U0 ∧ U = U0 ∩ sourceComplexGramVariety d n

/-- Relative openness in the real Hall-Wightman scalar-product variety. -/
def IsRelOpenInSourceRealGramVariety
    (d n : ℕ)
    (E : Set (Fin n → Fin n → ℝ)) : Prop :=
  ∃ E0 : Set (Fin n → Fin n → ℝ),
    IsOpen E0 ∧ E = E0 ∩ sourceRealGramVariety d n

/-- Local ambient holomorphicity for scalar-product representatives on the
Hall-Wightman scalar-product variety.  This is the analytic-set style surface
needed beyond the small-arity full-matrix case. -/
def SourceVarietyHolomorphicOn
    (d n : ℕ)
    (Φ : (Fin n → Fin n → ℂ) → ℂ)
    (U : Set (Fin n → Fin n → ℂ)) : Prop :=
  ∀ Z ∈ U, ∃ U0 : Set (Fin n → Fin n → ℂ),
    IsOpen U0 ∧ Z ∈ U0 ∧ DifferentiableOn ℂ Φ U0 ∧
      U0 ∩ sourceComplexGramVariety d n ⊆ U

/-- A Hall-Wightman real Gram environment which is a uniqueness set for
variety-holomorphic scalar-product representatives.

This is the theorem-2-facing uniqueness predicate: agreement on `E` determines
variety-holomorphic scalar-product representatives on connected relatively
open domains in the scalar-product variety. -/
def sourceDistributionalUniquenessSetOnVariety
    (d n : ℕ)
    (E : Set (Fin n → Fin n → ℝ)) : Prop :=
  E.Nonempty ∧
    ∀ (U : Set (Fin n → Fin n → ℂ))
      (Φ Ψ : (Fin n → Fin n → ℂ) → ℂ),
      IsRelOpenInSourceComplexGramVariety d n U →
      IsConnected U →
      (∀ G ∈ E, sourceRealGramComplexify n G ∈ U) →
      SourceVarietyHolomorphicOn d n Φ U →
      SourceVarietyHolomorphicOn d n Ψ U →
      (∀ G ∈ E, Φ (sourceRealGramComplexify n G) =
        Ψ (sourceRealGramComplexify n G)) →
      Set.EqOn Φ Ψ U

/-- Variety-level uniqueness is monotone in the real environment.  This lets
the OS supplier enlarge a small Hall-Wightman real environment to the whole
Gram image of the selected Jost patch without losing uniqueness. -/
theorem sourceDistributionalUniquenessSetOnVariety_mono
    (d n : ℕ)
    {O E : Set (Fin n → Fin n → ℝ)}
    (hO : sourceDistributionalUniquenessSetOnVariety d n O)
    (hOE : O ⊆ E) :
    sourceDistributionalUniquenessSetOnVariety d n E := by
  refine ⟨hO.1.mono hOE, ?_⟩
  intro U Φ Ψ hU_rel hU_conn hE_sub hΦ hΨ h_eq
  exact hO.2 U Φ Ψ hU_rel hU_conn
    (fun G hG => hE_sub G (hOE hG))
    hΦ hΨ
    (fun G hG => h_eq G (hOE hG))

/-- A full-matrix real Gram environment which is a uniqueness set for
holomorphic scalar-product representatives.

This is a sufficient small/full-dimensional criterion, not the general
Hall-Wightman scalar-product-variety predicate needed by the OS supplier in
arbitrary arity. -/
def sourceDistributionalUniquenessSet
    (_d n : ℕ)
    (E : Set (Fin n → Fin n → ℝ)) : Prop :=
  E.Nonempty ∧
    ∀ (U : Set (Fin n → Fin n → ℂ))
      (Φ Ψ : (Fin n → Fin n → ℂ) → ℂ),
      IsOpen U →
      IsConnected U →
      (∀ G ∈ E, sourceRealGramComplexify n G ∈ U) →
      DifferentiableOn ℂ Φ U →
      DifferentiableOn ℂ Ψ U →
      (∀ G ∈ E, Φ (sourceRealGramComplexify n G) =
        Ψ (sourceRealGramComplexify n G)) →
      Set.EqOn Φ Ψ U

/-- Any nonempty open real Gram environment is a uniqueness set for
holomorphic scalar-product representatives. -/
theorem sourceDistributionalUniquenessSet_of_isOpen_nonempty
    (d n : ℕ)
    {E : Set (Fin n → Fin n → ℝ)}
    (hE_open : IsOpen E)
    (hE_ne : E.Nonempty) :
    sourceDistributionalUniquenessSet d n E := by
  refine ⟨hE_ne, ?_⟩
  intro U Φ Ψ hU_open hU_conn hE_sub hΦ hΨ h_eq
  have hsub :
      ∀ G ∈ E, SCV.realToComplexProduct G ∈ U := by
    intro G hG
    simpa [sourceRealGramComplexify, SCV.realToComplexProduct] using
      hE_sub G hG
  have hzero :
      ∀ G ∈ E, (Φ - Ψ) (SCV.realToComplexProduct G) = 0 := by
    intro G hG
    have hG_eq := h_eq G hG
    simpa [sourceRealGramComplexify, SCV.realToComplexProduct, sub_eq_zero] using hG_eq
  have hident :
      ∀ Z ∈ U, (Φ - Ψ) Z = 0 :=
    SCV.identity_theorem_totally_real_product
      (n := n) (p := n)
      hU_open hU_conn (hΦ.sub hΨ) hE_open hE_ne hsub hzero
  intro Z hZ
  exact sub_eq_zero.mp (hident Z hZ)

/-- A real Gram environment containing a nonempty open real subset is a
uniqueness set for holomorphic scalar-product representatives.

This is a sufficient full-matrix criterion.  The general Hall-Wightman
supplier for arbitrary arity works on the scalar-product variety; a realized
Gram image need not contain an open subset of the full matrix coordinate
space. -/
theorem sourceDistributionalUniquenessSet_of_contains_open
    (d n : ℕ)
    {E O : Set (Fin n → Fin n → ℝ)}
    (hO_open : IsOpen O)
    (hO_ne : O.Nonempty)
    (hO_sub : O ⊆ E) :
    sourceDistributionalUniquenessSet d n E := by
  have hE_ne : E.Nonempty := by
    rcases hO_ne with ⟨G, hG⟩
    exact ⟨G, hO_sub hG⟩
  refine ⟨hE_ne, ?_⟩
  intro U Φ Ψ hU_open hU_conn hE_sub hΦ hΨ h_eq
  exact
    (sourceDistributionalUniquenessSet_of_isOpen_nonempty
      (d := d) (n := n) hO_open hO_ne).2
      U Φ Ψ hU_open hU_conn
      (fun G hG => hE_sub G (hO_sub hG))
      hΦ hΨ
      (fun G hG => h_eq G (hO_sub hG))

/-- Distributional Euclidean/Jost anchor for adjacent PET branches.

The fields are indexed by a PET sector label `π` and an adjacent transposition.
They record the real Jost patches on which both adjacent branches have boundary
values, the scalar-product uniqueness environments, and the compact-test
equality of the two branch boundary distributions there. -/
structure SourceDistributionalAdjacentTubeAnchor
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  realPatch :
    Equiv.Perm (Fin n) →
    (i : Fin n) →
    (hi : i.val + 1 < n) →
    Set (Fin n → Fin (d + 1) → ℝ)
  realPatch_open :
    ∀ π i hi, IsOpen (realPatch π i hi)
  realPatch_nonempty :
    ∀ π i hi, (realPatch π i hi).Nonempty
  realPatch_jost :
    ∀ π i hi, realPatch π i hi ⊆ JostSet d n
  realPatch_left_sector :
    ∀ π i hi x, x ∈ realPatch π i hi →
      realEmbed x ∈ permutedExtendedTubeSector d n π
  realPatch_right_sector :
    ∀ π i hi x, x ∈ realPatch π i hi →
      realEmbed x ∈
        permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩)
  gramEnvironment :
    Equiv.Perm (Fin n) →
    (i : Fin n) →
    (hi : i.val + 1 < n) →
    Set (Fin n → Fin n → ℝ)
  gramEnvironment_unique :
    ∀ π i hi,
      sourceDistributionalUniquenessSetOnVariety d n
        (gramEnvironment π i hi)
  gram_left_mem :
    ∀ π i hi x, x ∈ realPatch π i hi →
      sourceRealMinkowskiGram d n (fun k => x (π k)) ∈
        gramEnvironment π i hi
  gram_environment_realized :
    ∀ π i hi G, G ∈ gramEnvironment π i hi →
      ∃ x ∈ realPatch π i hi,
        sourceRealMinkowskiGram d n (fun k => x (π k)) = G
  gram_right_eq_perm_left :
    ∀ π i hi x, x ∈ realPatch π i hi →
      sourceRealMinkowskiGram d n
          (fun k => x ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
        sourcePermuteGram n (Equiv.swap i ⟨i.val + 1, hi⟩)
          (sourceRealMinkowskiGram d n (fun k => x (π k)))
  compact_branch_eq :
    ∀ π i hi (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
      HasCompactSupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
      tsupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ realPatch π i hi →
      ∫ x : Fin n → Fin (d + 1) → ℝ,
          extendF F (fun k => realEmbed x (π k)) * φ x
        =
      ∫ x : Fin n → Fin (d + 1) → ℝ,
          extendF F
            (fun k => realEmbed x
              ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) *
            φ x

/-- Hall-Wightman scalar-product representative data for the ordinary
extended-tube branch.

The representative lives on the scalar-product image of the ordinary extended
tube.  For arity above the spacetime dimension this is a relatively open
domain in the Hall-Wightman Gram variety, not an open subset of the full
matrix coordinate space. -/
structure SourceScalarRepresentativeData
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  U : Set (Fin n → Fin n → ℂ)
  U_eq : U = sourceExtendedTubeGramDomain d n
  U_relOpen : IsRelOpenInSourceComplexGramVariety d n U
  U_connected : IsConnected U
  Phi : (Fin n → Fin n → ℂ) → ℂ
  Phi_holomorphic : SourceVarietyHolomorphicOn d n Phi U
  branch_eq :
    ∀ w : Fin n → Fin (d + 1) → ℂ,
      w ∈ ExtendedTube d n →
      Phi (sourceMinkowskiGram d n w) = extendF F w

/- The unresolved Hall-Wightman source existence theorem for this data is kept
in the proof docs until it has a checked proof or an explicitly approved source
import boundary.  This production module contains only checked source data and
support lemmas. -/

/-- Compact-test equality in the adjacent source anchor gives pointwise
equality on the selected real patch. -/
theorem sourceAnchor_compactBranchEq_pointwise_on_realPatch
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    ∀ x, x ∈ hAnchor.realPatch π i hi →
      extendF F (fun k => realEmbed x (π k)) =
        extendF F
          (fun k =>
            realEmbed x
              ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) := by
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hExtend_cont : ContinuousOn (extendF F) (ExtendedTube d n) :=
    (extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn
  have hleftEmbed_cont :
      Continuous
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          fun k => realEmbed x (π k)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply (π k)))
  have hrightEmbed_cont :
      Continuous
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          fun k => realEmbed x
            ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp
        (continuous_apply ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)))
  let L : (Fin n → Fin (d + 1) → ℝ) → ℂ :=
    fun x => extendF F (fun k => realEmbed x (π k))
  let R : (Fin n → Fin (d + 1) → ℝ) → ℂ :=
    fun x =>
      extendF F
        (fun k => realEmbed x
          ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k))
  have hL_cont : ContinuousOn L (hAnchor.realPatch π i hi) := by
    refine hExtend_cont.comp hleftEmbed_cont.continuousOn ?_
    intro x hx
    simpa [L, permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_left_sector π i hi x hx
  have hR_cont : ContinuousOn R (hAnchor.realPatch π i hi) := by
    refine hExtend_cont.comp hrightEmbed_cont.continuousOn ?_
    intro x hx
    simpa [R, permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_right_sector π i hi x hx
  have hEqOn : Set.EqOn L R (hAnchor.realPatch π i hi) := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      (hAnchor.realPatch_open π i hi) hL_cont hR_cont ?_
    intro φ hφ_compact hφ_tsupport
    exact hAnchor.compact_branch_eq π i hi φ hφ_compact hφ_tsupport
  intro x hx
  exact hEqOn hx

/-- Adjacent compact-test equality rewritten as equality of the
Hall-Wightman scalar-product representative on the real Gram environment. -/
theorem sourceScalarRepresentative_adjacent_seed_eq_on_environment
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      hRep.Phi (sourceRealGramComplexify n G) =
        hRep.Phi
          (sourcePermuteComplexGram n τ
            (sourceRealGramComplexify n G)) := by
  dsimp
  intro G hG
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  change
    hRep.Phi (sourceRealGramComplexify n G) =
      hRep.Phi
        (sourcePermuteComplexGram n τ
          (sourceRealGramComplexify n G))
  rcases hAnchor.gram_environment_realized π i hi G hG with
    ⟨x, hxPatch, hGx⟩
  have hpoint :
      extendF F (fun k => realEmbed x (π k)) =
        extendF F (fun k => realEmbed x ((π * τ) k)) := by
    simpa [τ] using
      sourceAnchor_compactBranchEq_pointwise_on_realPatch
        (d := d) n F hF_holo hF_lorentz hAnchor π i hi x hxPatch
  have hleft_ET :
      realEmbed (fun k => x (π k)) ∈ ExtendedTube d n := by
    simpa [permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_left_sector π i hi x hxPatch
  have hright_ET :
      realEmbed (fun k => x ((π * τ) k)) ∈ ExtendedTube d n := by
    simpa [permutedExtendedTubeSector, realEmbed, τ] using
      hAnchor.realPatch_right_sector π i hi x hxPatch
  have hleft :
      hRep.Phi (sourceRealGramComplexify n G) =
        extendF F (fun k => realEmbed x (π k)) := by
    simpa [hGx, sourceMinkowskiGram_realEmbed, realEmbed] using
      hRep.branch_eq (realEmbed (fun k => x (π k))) hleft_ET
  have hrightReal :
      sourceRealMinkowskiGram d n (fun k => x ((π * τ) k)) =
        sourcePermuteGram n τ
          (sourceRealMinkowskiGram d n (fun k => x (π k))) := by
    simpa [τ] using hAnchor.gram_right_eq_perm_left π i hi x hxPatch
  have hrightGram :
      sourceMinkowskiGram d n (realEmbed (fun k => x ((π * τ) k))) =
        sourcePermuteComplexGram n τ (sourceRealGramComplexify n G) := by
    calc
      sourceMinkowskiGram d n (realEmbed (fun k => x ((π * τ) k)))
          = sourceRealGramComplexify n
              (sourceRealMinkowskiGram d n (fun k => x ((π * τ) k))) := by
            exact sourceMinkowskiGram_realEmbed
              (d := d) (n := n) (fun k => x ((π * τ) k))
      _ = sourceRealGramComplexify n
            (sourcePermuteGram n τ
              (sourceRealMinkowskiGram d n (fun k => x (π k)))) := by
            rw [hrightReal]
      _ = sourceRealGramComplexify n (sourcePermuteGram n τ G) := by
            rw [hGx]
      _ = sourcePermuteComplexGram n τ (sourceRealGramComplexify n G) :=
            sourceRealGramComplexify_perm (n := n) τ G
  have hright :
      hRep.Phi
          (sourcePermuteComplexGram n τ (sourceRealGramComplexify n G)) =
        extendF F (fun k => realEmbed x ((π * τ) k)) := by
    rw [← hrightGram]
    simpa [realEmbed, Equiv.Perm.mul_apply] using
      hRep.branch_eq (realEmbed (fun k => x ((π * τ) k))) hright_ET
  exact hleft.trans (hpoint.trans hright.symm)

/- The scalar-overlap continuation theorem from adjacent real Gram seeds is
also deliberately not exposed as production Lean yet.  The checked theorem
above is the last local support lemma before that genuine Hall-Wightman source
obligation. -/

private theorem source_lorentz_perm_commute
    (Γ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (τ : Equiv.Perm (Fin n)) :
    complexLorentzAction Γ (fun k => w (τ k)) =
      fun k => (complexLorentzAction Γ w) (τ k) := by
  ext k μ
  simp only [complexLorentzAction]

private theorem source_complexLorentzAction_mem_extendedTube
    (n : ℕ)
    (Λ : ComplexLorentzGroup d)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n) :
    complexLorentzAction Λ z ∈ ExtendedTube d n := by
  rcases Set.mem_iUnion.mp hz with ⟨Γ, w, hw, rfl⟩
  exact Set.mem_iUnion.mpr ⟨Λ * Γ, w, hw, by rw [complexLorentzAction_mul]⟩

private theorem source_permutedExtendedTubeSector_complexLorentzAction_iff
    (Λ : ComplexLorentzGroup d)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ z ∈ permutedExtendedTubeSector d n π ↔
      z ∈ permutedExtendedTubeSector d n π := by
  constructor
  · intro h
    have h' : complexLorentzAction Λ⁻¹
        (fun k => (complexLorentzAction Λ z) (π k)) ∈ ExtendedTube d n :=
      source_complexLorentzAction_mem_extendedTube n Λ⁻¹ h
    have hrewrite :
        complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (π k)) =
          fun k => z (π k) := by
      calc
        complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (π k))
            = complexLorentzAction Λ⁻¹
                (complexLorentzAction Λ (fun k => z (π k))) := by
                simp [source_lorentz_perm_commute]
        _ = fun k => z (π k) := by
                rw [complexLorentzAction_inv]
    simpa [permutedExtendedTubeSector, hrewrite] using h'
  · intro h
    have h' : complexLorentzAction Λ (fun k => z (π k)) ∈ ExtendedTube d n :=
      source_complexLorentzAction_mem_extendedTube n Λ h
    have hrewrite :
        (fun k => (complexLorentzAction Λ z) (π k)) =
          complexLorentzAction Λ (fun k => z (π k)) := by
      simp [source_lorentz_perm_commute]
    simpa [permutedExtendedTubeSector, hrewrite] using h'

/-- The raw permuted forward-tube branch is holomorphic on its permuted
forward-tube sector.  This packages the `S'_n` datum before BHW enlargement. -/
private theorem source_permutedForwardBranch_holomorphicOn
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => F (fun k => z (π k)))
      (PermutedForwardTube d n π) := by
  intro z hz
  have hzFT : (fun k => z (π k)) ∈ ForwardTube d n := by
    simpa [PermutedForwardTube] using hz
  have hF_at :
      DifferentiableAt ℂ F (fun k => z (π k)) := by
    exact (hF_holo (fun k => z (π k)) hzFT).differentiableAt
      (isOpen_forwardTube.mem_nhds hzFT)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π k)
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => F (fun k => w (π k))) z := by
    simpa [Function.comp_def] using hF_at.comp z hperm_diff.differentiableAt
  exact hbranch_at.differentiableWithinAt

/-- Restricted real Lorentz invariance transported to each raw permuted
forward-tube branch. -/
private theorem source_permutedForwardBranch_restrictedLorentzInvariant
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (π : Equiv.Perm (Fin n)) :
    ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ PermutedForwardTube d n π →
      (fun z' : Fin n → Fin (d + 1) → ℂ => F (fun k => z' (π k)))
        (complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z) =
      F (fun k => z (π k)) := by
  intro Λ z hz
  have hzFT : (fun k => z (π k)) ∈ ForwardTube d n := by
    simpa [PermutedForwardTube] using hz
  have hcomm :
      (fun k => (complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z) (π k)) =
        complexLorentzAction (ComplexLorentzGroup.ofReal Λ) (fun k => z (π k)) := by
    simpa using
      (source_lorentz_perm_commute (d := d) (n := n)
        (ComplexLorentzGroup.ofReal Λ) z π).symm
  calc
    (fun z' : Fin n → Fin (d + 1) → ℂ => F (fun k => z' (π k)))
        (complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z)
        = F (complexLorentzAction (ComplexLorentzGroup.ofReal Λ)
            (fun k => z (π k))) := by
            simpa using congrArg F hcomm
    _ = F (fun k => z (π k)) := hF_lorentz Λ (fun k => z (π k)) hzFT

/-- The permutation symmetry hypothesis identifies all raw permuted
forward-tube branches as one symmetric `S'_n` datum. -/
private theorem source_permutedForwardBranch_symmetric
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        F (fun k => z (σ k)) = F z) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      F (fun k => z (π k)) = F (fun k => z (ρ k)) := by
  intro π ρ z
  exact (hF_perm π z).trans (hF_perm ρ z).symm

/-- Each permuted `extendF` branch is holomorphic on its PET sector.  This is a
local analytic sub-obligation for the source theorem below; it uses only the
forward-tube BHW continuation theorem and derives complex-Lorentz overlap
invariance from restricted real Lorentz invariance. -/
theorem permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => extendF F (fun k => z (π k)))
      (permutedExtendedTubeSector d n π) := by
  intro z hz
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hExt_at :
      DifferentiableAt ℂ (extendF F) (fun k => z (π k)) := by
    exact
      ((extendF_holomorphicOn n F hF_holo hF_cinv)
        (fun k => z (π k)) hz).differentiableAt
        (isOpen_extendedTube.mem_nhds hz)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π k)
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => extendF F (fun k => w (π k))) z := by
    simpa [Function.comp_def] using hExt_at.comp z hperm_diff.differentiableAt
  exact hbranch_at.differentiableWithinAt

/- The PET branch law, PET extension theorem, and sector single-valuedness
corollary are likewise proof-doc obligations until the Hall-Wightman source
compatibility theorem is proved. -/

end BHW
