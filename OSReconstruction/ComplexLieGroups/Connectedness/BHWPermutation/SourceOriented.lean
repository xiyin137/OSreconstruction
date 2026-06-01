import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension

/-!
# Oriented source invariants for the BHW route

This file starts the finite-dimensional oriented source layer used by the
strict proper-complex Hall-Wightman/Jost route.  It packages the ordinary source
Gram coordinates together with full-frame determinant coordinates and proves the
basic determinant algebra under source permutations and proper complex Lorentz
transformations.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Source Gram data enhanced by all ordered full-frame determinant
coordinates.  The determinant coordinates are indexed by embeddings of a
spacetime-size frame into the source labels.

This is an abbreviation for the product coordinate space so the oriented
source variety inherits the usual finite-dimensional complex normed vector
space structure needed by the later germ-holomorphic API. -/
abbrev SourceOrientedGramData (d n : ℕ) :=
  (Fin n → Fin n → ℂ) × ((Fin (d + 1) ↪ Fin n) → ℂ)

namespace SourceOrientedGramData

/-- The ordinary source Gram coordinates of oriented source data. -/
def gram (G : SourceOrientedGramData d n) : Fin n → Fin n → ℂ :=
  G.1

/-- The ordered full-frame determinant coordinates of oriented source data. -/
def det (G : SourceOrientedGramData d n) :
    (Fin (d + 1) ↪ Fin n) → ℂ :=
  G.2

/-- Extensionality for oriented source data. -/
@[ext]
theorem ext {G H : SourceOrientedGramData d n}
    (hgram : G.gram = H.gram)
    (hdet : G.det = H.det) :
    G = H := by
  cases G with
  | mk Ggram Gdet =>
    cases H with
    | mk Hgram Hdet =>
      simp [gram, det] at hgram hdet
      cases hgram
      cases hdet
      rfl

end SourceOrientedGramData

/-- The product-coordinate map defining the topology is continuous. -/
theorem continuous_sourceOrientedGramData_pair :
    Continuous (fun G : SourceOrientedGramData d n => (G.gram, G.det)) := by
  simpa [SourceOrientedGramData.gram, SourceOrientedGramData.det] using
    (continuous_fst.prodMk continuous_snd :
      Continuous (fun G : SourceOrientedGramData d n => (G.1, G.2)))

/-- The Gram-coordinate projection is continuous. -/
theorem continuous_sourceOrientedGramData_gram :
    Continuous (fun G : SourceOrientedGramData d n => G.gram) :=
  continuous_fst.comp
    (continuous_sourceOrientedGramData_pair (d := d) (n := n))

/-- The determinant-coordinate projection is continuous. -/
theorem continuous_sourceOrientedGramData_det :
    Continuous (fun G : SourceOrientedGramData d n => G.det) :=
  continuous_snd.comp
    (continuous_sourceOrientedGramData_pair (d := d) (n := n))

/-- Constructor continuity for oriented source data. -/
theorem continuous_sourceOrientedGramData_mk
    {α : Type*} [TopologicalSpace α]
    {g : α → Fin n → Fin n → ℂ}
    {δ : α → (Fin (d + 1) ↪ Fin n) → ℂ}
    (hg : Continuous g)
    (hδ : Continuous δ) :
    Continuous (fun a : α =>
      ((g a, δ a) : SourceOrientedGramData d n)) := by
  exact hg.prodMk hδ

/-- Selected full-frame source matrix.  Rows are source labels and columns are
spacetime coordinates. -/
def sourceFullFrameMatrix (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun a μ => z (ι a) μ

/-- Determinant of a selected full-frame source matrix. -/
def sourceFullFrameDet (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  (sourceFullFrameMatrix d n ι z).det

/-- Continuity of the selected full-frame matrix map. -/
theorem continuous_sourceFullFrameMatrix
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceFullFrameMatrix d n ι) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (ι a))

/-- Continuity of the selected full-frame determinant. -/
theorem continuous_sourceFullFrameDet
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (fun z : Fin n → Fin (d + 1) → ℂ =>
      sourceFullFrameDet d n ι z) := by
  exact (continuous_sourceFullFrameMatrix (d := d) (n := n) ι).matrix_det

/-- The oriented source invariant: ordinary source Gram coordinates plus all
full-frame determinants. -/
def sourceOrientedMinkowskiInvariant (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceOrientedGramData d n :=
  (sourceMinkowskiGram d n z, fun ι => sourceFullFrameDet d n ι z)

/-- Equality of oriented source invariants implies equality of the ordinary
source Gram coordinates. -/
theorem same_sourceOrientedInvariant_sourceGram
    {z w : Fin n → Fin (d + 1) → ℂ}
    (horiented :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    sourceMinkowskiGram d n z = sourceMinkowskiGram d n w := by
  simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram] using
    congrArg SourceOrientedGramData.gram horiented

/-- Equality of oriented source invariants implies equality of every ordered
full-frame determinant coordinate. -/
theorem same_sourceOrientedInvariant_fullFrameDet
    {z w : Fin n → Fin (d + 1) → ℂ}
    (horiented :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceFullFrameDet d n ι z = sourceFullFrameDet d n ι w := by
  simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det] using
    congrFun (congrArg SourceOrientedGramData.det horiented) ι

/-- The oriented Hall-Wightman source variety. -/
def sourceOrientedGramVariety (d n : ℕ) :
    Set (SourceOrientedGramData d n) :=
  Set.range (sourceOrientedMinkowskiInvariant d n)

/-- The oriented scalar image of the ordinary extended tube. -/
def sourceOrientedExtendedTubeDomain (d n : ℕ) :
    Set (SourceOrientedGramData d n) :=
  sourceOrientedMinkowskiInvariant d n '' ExtendedTube d n

/-- The oriented extended-tube image lies in the oriented source variety. -/
theorem sourceOrientedExtendedTubeDomain_subset_variety
    (d n : ℕ) :
    sourceOrientedExtendedTubeDomain d n ⊆
      sourceOrientedGramVariety d n := by
  rintro G ⟨z, _hz, rfl⟩
  exact ⟨z, rfl⟩

/-- Coordinate permutation on oriented source data.  Full-frame determinant
coordinates are transported by composing the selected embedding with the source
permutation. -/
def sourcePermuteOrientedGram (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (G : SourceOrientedGramData d n) :
    SourceOrientedGramData d n :=
  (sourcePermuteComplexGram n σ G.gram,
    fun ι => G.det (ι.trans σ.toEmbedding))

/-- The identity permutation acts trivially on oriented source data. -/
theorem sourcePermuteOrientedGram_one
    (G : SourceOrientedGramData d n) :
    sourcePermuteOrientedGram d n 1 G = G := by
  apply SourceOrientedGramData.ext
  · exact sourcePermuteComplexGram_one n G.gram
  · funext ι
    have hι : ι.trans (1 : Equiv.Perm (Fin n)).toEmbedding = ι := by
      ext a
      simp
    dsimp [sourcePermuteOrientedGram, SourceOrientedGramData.det]
    rw [hι]

/-- Permuting oriented source data and then permuting back recovers the
original data. -/
theorem sourcePermuteOrientedGram_inv_mul
    (σ : Equiv.Perm (Fin n))
    (G : SourceOrientedGramData d n) :
    sourcePermuteOrientedGram d n σ⁻¹
        (sourcePermuteOrientedGram d n σ G) = G := by
  apply SourceOrientedGramData.ext
  · simpa [sourcePermuteOrientedGram] using
      sourcePermuteComplexGram_inv_mul n σ G.gram
  · funext ι
    have hι :
        (ι.trans (σ⁻¹).toEmbedding).trans σ.toEmbedding = ι := by
      ext a
      simp
    dsimp [sourcePermuteOrientedGram, SourceOrientedGramData.det,
      SourceOrientedGramData.gram]
    rw [hι]

/-- Complex source Gram coordinates are continuous polynomial functions of the
source tuple. -/
theorem continuous_sourceMinkowskiGram :
    Continuous (sourceMinkowskiGram d n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finset_sum _ fun μ _ => by
    have hiμ : Continuous (fun z : Fin n → Fin (d + 1) → ℂ => z i μ) :=
      (continuous_apply μ).comp (continuous_apply i)
    have hjμ : Continuous (fun z : Fin n → Fin (d + 1) → ℂ => z j μ) :=
      (continuous_apply μ).comp (continuous_apply j)
    simpa [mul_assoc] using (continuous_const.mul hiμ).mul hjμ

/-- Continuity of the oriented source invariant. -/
theorem continuous_sourceOrientedMinkowskiInvariant :
    Continuous (sourceOrientedMinkowskiInvariant d n) :=
  continuous_sourceOrientedGramData_mk
    (d := d) (n := n)
    (continuous_sourceMinkowskiGram (d := d) (n := n))
    (continuous_pi fun ι =>
      continuous_sourceFullFrameDet (d := d) (n := n) ι)

/-- Coordinate permutation on oriented source data is continuous. -/
theorem continuous_sourcePermuteOrientedGram
    (σ : Equiv.Perm (Fin n)) :
    Continuous (sourcePermuteOrientedGram d n σ) := by
  apply continuous_sourceOrientedGramData_mk
  · exact
      (continuous_sourcePermuteComplexGram n σ).comp
        continuous_sourceOrientedGramData_gram
  · apply continuous_pi
    intro ι
    exact
      (continuous_apply (ι.trans σ.toEmbedding)).comp
        continuous_sourceOrientedGramData_det

/-- Coordinate permutation on oriented source data is complex differentiable. -/
theorem differentiable_sourcePermuteOrientedGram
    (σ : Equiv.Perm (Fin n)) :
    Differentiable ℂ (sourcePermuteOrientedGram d n σ) := by
  have hgram :
      Differentiable ℂ
        (fun G : SourceOrientedGramData d n =>
          sourcePermuteComplexGram n σ G.gram) := by
    exact
      (differentiable_sourcePermuteComplexGram n σ).comp
        differentiable_fst
  have hdet :
      Differentiable ℂ
        (fun G : SourceOrientedGramData d n =>
          fun ι : Fin (d + 1) ↪ Fin n =>
            G.det (ι.trans σ.toEmbedding)) := by
    have hsnd :
        Differentiable ℂ
          (fun G : SourceOrientedGramData d n => G.det) := by
      change
        Differentiable ℂ
          (fun G :
            (Fin n → Fin n → ℂ) ×
              ((Fin (d + 1) ↪ Fin n) → ℂ) => G.2)
      exact differentiable_snd
    rw [differentiable_pi]
    intro ι
    exact
      (differentiable_apply (ι.trans σ.toEmbedding)).comp
        hsnd
  simpa [sourcePermuteOrientedGram, SourceOrientedGramData.gram,
    SourceOrientedGramData.det] using
      Differentiable.prodMk hgram hdet

/-- Relative openness in the oriented source variety. -/
def IsRelOpenInSourceOrientedGramVariety
    (d n : ℕ)
    (U : Set (SourceOrientedGramData d n)) : Prop :=
  ∃ U0 : Set (SourceOrientedGramData d n),
    IsOpen U0 ∧ U = U0 ∩ sourceOrientedGramVariety d n

/-- Relatively open oriented source-variety domains are subsets of the oriented
source variety. -/
theorem IsRelOpenInSourceOrientedGramVariety.subset
    {U : Set (SourceOrientedGramData d n)}
    (hU : IsRelOpenInSourceOrientedGramVariety d n U) :
    U ⊆ sourceOrientedGramVariety d n := by
  rcases hU with ⟨U0, _hU0_open, hU_eq⟩
  intro G hGU
  rw [hU_eq] at hGU
  exact hGU.2

/-- Germ-style holomorphicity on the oriented source variety.  The local
representative may differ from the global scalar function away from the
oriented source variety; equality is required only on the analytic variety
slice. -/
def SourceOrientedVarietyGermHolomorphicOn
    (d n : ℕ)
    (Φ : SourceOrientedGramData d n → ℂ)
    (U : Set (SourceOrientedGramData d n)) : Prop :=
  ∀ G ∈ U, ∃ U0 Ψ,
    IsOpen U0 ∧ G ∈ U0 ∧ DifferentiableOn ℂ Ψ U0 ∧
      Set.EqOn Φ Ψ (U0 ∩ sourceOrientedGramVariety d n) ∧
      U0 ∩ sourceOrientedGramVariety d n ⊆ U

/-- Germ-holomorphic oriented source representatives are continuous on domains
contained in the oriented source variety. -/
theorem SourceOrientedVarietyGermHolomorphicOn.continuousOn
    {U : Set (SourceOrientedGramData d n)}
    {Φ : SourceOrientedGramData d n → ℂ}
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (hU_sub : U ⊆ sourceOrientedGramVariety d n) :
    ContinuousOn Φ U := by
  rw [continuousOn_iff]
  intro G hGU T hT_open hΦGT
  rcases hΦ G hGU with
    ⟨U0, Ψ, hU0_open, hGU0, hDiffU0, hEq, _hU0_sub⟩
  have hΨGT : Ψ G ∈ T := by
    have hEqG : Φ G = Ψ G := hEq ⟨hGU0, hU_sub hGU⟩
    simpa [hEqG] using hΦGT
  have hContU0 : ContinuousOn Ψ U0 := hDiffU0.continuousOn
  rcases (continuousOn_iff.mp hContU0) G hGU0 T hT_open hΨGT with
    ⟨V, hV_open, hGV, hV_sub⟩
  refine ⟨V ∩ U0, hV_open.inter hU0_open, ⟨hGV, hGU0⟩, ?_⟩
  intro H hH
  have hΨHT : Ψ H ∈ T := hV_sub ⟨hH.1.1, hH.1.2⟩
  have hEqH : Φ H = Ψ H := hEq ⟨hH.1.2, hU_sub hH.2⟩
  simpa [hEqH] using hΨHT

/-- Restrict oriented germ holomorphicity from an oriented source-variety
domain to a relatively open subdomain. -/
theorem SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
    {Φ : SourceOrientedGramData d n → ℂ}
    {U V : Set (SourceOrientedGramData d n)}
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (hV_rel : IsRelOpenInSourceOrientedGramVariety d n V)
    (hVU : V ⊆ U) :
    SourceOrientedVarietyGermHolomorphicOn d n Φ V := by
  intro G hGV
  rcases hΦ G (hVU hGV) with
    ⟨U0, Ψ, hU0_open, hGU0, hDiffU0, hEq, _hU0_sub⟩
  rcases hV_rel with ⟨V0, hV0_open, hV0_eq⟩
  refine ⟨U0 ∩ V0, Ψ, hU0_open.inter hV0_open, ⟨hGU0, ?_⟩, ?_, ?_, ?_⟩
  · rw [hV0_eq] at hGV
    exact hGV.1
  · exact hDiffU0.mono (by intro H hH; exact hH.1)
  · intro H hH
    exact hEq ⟨hH.1.1, hH.2⟩
  · intro H hH
    rw [hV0_eq]
    exact ⟨hH.1.2, hH.2⟩

/-- Oriented germ holomorphicity is stable under subtraction. -/
theorem SourceOrientedVarietyGermHolomorphicOn.sub
    {U : Set (SourceOrientedGramData d n)}
    {Φ Ψ : SourceOrientedGramData d n → ℂ}
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (hΨ : SourceOrientedVarietyGermHolomorphicOn d n Ψ U) :
    SourceOrientedVarietyGermHolomorphicOn d n (fun G => Φ G - Ψ G) U := by
  intro G hGU
  rcases hΦ G hGU with
    ⟨UΦ, Φ0, hUΦ_open, hGUΦ, hDiffΦ, hEqΦ, hUΦ_sub⟩
  rcases hΨ G hGU with
    ⟨UΨ, Ψ0, hUΨ_open, hGUΨ, hDiffΨ, hEqΨ, _hUΨ_sub⟩
  refine ⟨UΦ ∩ UΨ, (fun H => Φ0 H - Ψ0 H),
    hUΦ_open.inter hUΨ_open, ⟨hGUΦ, hGUΨ⟩, ?_, ?_, ?_⟩
  · exact (hDiffΦ.mono (by intro H hH; exact hH.1)).sub
      (hDiffΨ.mono (by intro H hH; exact hH.2))
  · intro H hH
    have hΦH : Φ H = Φ0 H := hEqΦ ⟨hH.1.1, hH.2⟩
    have hΨH : Ψ H = Ψ0 H := hEqΨ ⟨hH.1.2, hH.2⟩
    simp [hΦH, hΨH]
  · intro H hH
    exact hUΦ_sub ⟨hH.1.1, hH.2⟩

/-- Full-frame matrices commute with source-label permutations. -/
theorem sourceFullFrameMatrix_permAct
    (ι : Fin (d + 1) ↪ Fin n)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameMatrix d n ι (permAct (d := d) σ z) =
      sourceFullFrameMatrix d n (ι.trans σ.toEmbedding) z := by
  rfl

/-- Full-frame determinants commute with source-label permutations. -/
theorem sourceFullFrameDet_permAct
    (ι : Fin (d + 1) ↪ Fin n)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameDet d n ι (permAct (d := d) σ z) =
      sourceFullFrameDet d n (ι.trans σ.toEmbedding) z := by
  rfl

/-- The selected frame matrix of a Lorentz-transformed configuration is the
selected frame matrix multiplied on the right by the transpose Lorentz matrix. -/
theorem sourceFullFrameMatrix_complexLorentzAction
    (ι : Fin (d + 1) ↪ Fin n)
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameMatrix d n ι (complexLorentzAction Λ z) =
      sourceFullFrameMatrix d n ι z * Λ.val.transpose := by
  ext a μ
  simp [sourceFullFrameMatrix, complexLorentzAction, complexLorentzVectorAction, Matrix.mul_apply,
    Matrix.transpose_apply, mul_comm]

/-- Proper complex Lorentz transformations preserve every full-frame
determinant coordinate. -/
theorem sourceFullFrameDet_complexLorentzAction
    (ι : Fin (d + 1) ↪ Fin n)
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameDet d n ι (complexLorentzAction Λ z) =
      sourceFullFrameDet d n ι z := by
  rw [sourceFullFrameDet, sourceFullFrameMatrix_complexLorentzAction,
    sourceFullFrameDet, Matrix.det_mul, Matrix.det_transpose, Λ.proper,
    mul_one]

/-- Complex Lorentz transformations preserve the source Minkowski Gram matrix. -/
theorem sourceMinkowskiGram_complexLorentzAction
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n (complexLorentzAction Λ z) =
      sourceMinkowskiGram d n z := by
  ext i j
  simp only [sourceMinkowskiGram, complexLorentzAction]
  have hmetric : ∀ μ ν : Fin (d + 1),
      (∑ x, ↑(MinkowskiSpace.metricSignature d x) *
        Λ.val x μ * Λ.val x ν) =
        if μ = ν then (MinkowskiSpace.metricSignature d μ : ℂ) else 0 := by
    intro μ ν
    simpa [MinkowskiSpace.metricSignature,
      LorentzLieGroup.minkowskiSignature] using
      Λ.metric_preserving μ ν
  calc
    ∑ x, (↑(MinkowskiSpace.metricSignature d x) * ∑ ν, Λ.val x ν * z i ν) *
        ∑ ν, Λ.val x ν * z j ν
        = ∑ μ, ∑ ν,
            (∑ x, (↑(MinkowskiSpace.metricSignature d x) *
              Λ.val x μ * Λ.val x ν)) * z i ν * z j μ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ν _
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ μ, ∑ ν,
          (if μ = ν then
            (MinkowskiSpace.metricSignature d μ : ℂ) else 0) *
            z i ν * z j μ := by
          simp [hmetric]
    _ = ∑ μ, (↑(MinkowskiSpace.metricSignature d μ) * z i μ * z j μ) := by
          simp
    _ = ∑ μ, ↑(MinkowskiSpace.metricSignature d μ) * z i μ * z j μ := by
          rfl

/-- Proper complex Lorentz transformations preserve the full oriented source
invariant. -/
theorem sourceOrientedMinkowskiInvariant_complexLorentzAction
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceOrientedMinkowskiInvariant d n (complexLorentzAction Λ z) =
      sourceOrientedMinkowskiInvariant d n z := by
  apply SourceOrientedGramData.ext
  · exact sourceMinkowskiGram_complexLorentzAction (d := d) (n := n) Λ z
  · funext ι
    exact sourceFullFrameDet_complexLorentzAction (d := d) (n := n) ι Λ z

/-- Permuting source labels permutes the full oriented source invariant. -/
theorem sourceOrientedMinkowskiInvariant_permAct
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceOrientedMinkowskiInvariant d n (permAct (d := d) σ z) =
      sourcePermuteOrientedGram d n σ
        (sourceOrientedMinkowskiInvariant d n z) := by
  apply SourceOrientedGramData.ext
  · simpa [permAct, sourceOrientedMinkowskiInvariant, sourcePermuteOrientedGram]
      using sourceMinkowskiGram_perm d n σ z
  · funext ι
    exact sourceFullFrameDet_permAct (d := d) (n := n) ι σ z

/-- Coordinate permutation preserves the oriented source variety. -/
theorem sourcePermuteOrientedGram_mem_variety_iff
    (σ : Equiv.Perm (Fin n))
    (G : SourceOrientedGramData d n) :
    sourcePermuteOrientedGram d n σ G ∈
        sourceOrientedGramVariety d n ↔
      G ∈ sourceOrientedGramVariety d n := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨permAct (d := d) σ⁻¹ z, ?_⟩
    calc
      sourceOrientedMinkowskiInvariant d n (permAct (d := d) σ⁻¹ z)
          = sourcePermuteOrientedGram d n σ⁻¹
              (sourceOrientedMinkowskiInvariant d n z) :=
            sourceOrientedMinkowskiInvariant_permAct (d := d) (n := n) σ⁻¹ z
      _ = sourcePermuteOrientedGram d n σ⁻¹
              (sourcePermuteOrientedGram d n σ G) := by
            rw [hz]
      _ = G := sourcePermuteOrientedGram_inv_mul (d := d) (n := n) σ G
  · rintro ⟨z, rfl⟩
    exact ⟨permAct (d := d) σ z,
      sourceOrientedMinkowskiInvariant_permAct (d := d) (n := n) σ z⟩

/-- Oriented germ holomorphicity is stable under an oriented source-coordinate
permutation. -/
theorem SourceOrientedVarietyGermHolomorphicOn.precomp_sourcePermuteOrientedGram
    {Φ : SourceOrientedGramData d n → ℂ}
    {U : Set (SourceOrientedGramData d n)}
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (σ : Equiv.Perm (Fin n)) :
    SourceOrientedVarietyGermHolomorphicOn d n
      (fun G => Φ (sourcePermuteOrientedGram d n σ G))
      {G | sourcePermuteOrientedGram d n σ G ∈ U} := by
  intro G hG
  rcases hΦ (sourcePermuteOrientedGram d n σ G) hG with
    ⟨U0, Ψ, hU0_open, hGU0, hDiffU0, hEq, hU0_sub⟩
  refine ⟨{H | sourcePermuteOrientedGram d n σ H ∈ U0},
    (fun H => Ψ (sourcePermuteOrientedGram d n σ H)),
    hU0_open.preimage
      (continuous_sourcePermuteOrientedGram (d := d) (n := n) σ),
    hGU0, ?_, ?_, ?_⟩
  · exact hDiffU0.fun_comp
      (differentiable_sourcePermuteOrientedGram
        (d := d) (n := n) σ).differentiableOn
      (by intro H hH; exact hH)
  · intro H hH
    exact hEq ⟨hH.1,
      (sourcePermuteOrientedGram_mem_variety_iff
        (d := d) (n := n) σ H).2 hH.2⟩
  · intro H hH
    exact hU0_sub ⟨hH.1,
      (sourcePermuteOrientedGram_mem_variety_iff
        (d := d) (n := n) σ H).2 hH.2⟩

/-- Relative openness in the oriented source variety is preserved under
precomposition by a coordinate permutation. -/
theorem IsRelOpenInSourceOrientedGramVariety.preimage_sourcePermuteOrientedGram
    {U : Set (SourceOrientedGramData d n)}
    (hU : IsRelOpenInSourceOrientedGramVariety d n U)
    (σ : Equiv.Perm (Fin n)) :
    IsRelOpenInSourceOrientedGramVariety d n
      {G | sourcePermuteOrientedGram d n σ G ∈ U} := by
  rcases hU with ⟨U0, hU0_open, rfl⟩
  refine ⟨{G | sourcePermuteOrientedGram d n σ G ∈ U0},
    hU0_open.preimage (continuous_sourcePermuteOrientedGram (d := d) (n := n) σ),
    ?_⟩
  ext G
  constructor
  · intro h
    exact ⟨h.1,
      (sourcePermuteOrientedGram_mem_variety_iff
        (d := d) (n := n) σ G).1 h.2⟩
  · intro h
    exact ⟨h.1,
      (sourcePermuteOrientedGram_mem_variety_iff
        (d := d) (n := n) σ G).2 h.2⟩

/-- Relative openness in the oriented source variety is stable under
intersection. -/
theorem IsRelOpenInSourceOrientedGramVariety.inter
    {U V : Set (SourceOrientedGramData d n)}
    (hU : IsRelOpenInSourceOrientedGramVariety d n U)
    (hV : IsRelOpenInSourceOrientedGramVariety d n V) :
    IsRelOpenInSourceOrientedGramVariety d n (U ∩ V) := by
  rcases hU with ⟨U0, hU0_open, rfl⟩
  rcases hV with ⟨V0, hV0_open, rfl⟩
  refine ⟨U0 ∩ V0, hU0_open.inter hV0_open, ?_⟩
  ext G
  simp [Set.inter_left_comm, Set.inter_comm]

/-- Relative openness in the oriented source variety is stable under arbitrary
unions. -/
theorem IsRelOpenInSourceOrientedGramVariety.iUnion
    {ι : Type*}
    {U : ι → Set (SourceOrientedGramData d n)}
    (hU : ∀ i, IsRelOpenInSourceOrientedGramVariety d n (U i)) :
    IsRelOpenInSourceOrientedGramVariety d n (⋃ i, U i) := by
  choose U0 hU0_open hU0_eq using hU
  refine ⟨⋃ i, U0 i, isOpen_iUnion hU0_open, ?_⟩
  ext G
  simp [hU0_eq]

/-- Domain where both an oriented source point and its permuted point are in
the oriented extended-tube image. -/
def sourceOrientedDoublePermutationDomain
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Set (SourceOrientedGramData d n) :=
  {G | G ∈ sourceOrientedExtendedTubeDomain d n ∧
    sourcePermuteOrientedGram d n σ G ∈
      sourceOrientedExtendedTubeDomain d n}

/-- The identity double-permutation domain is just the oriented extended-tube
image. -/
theorem sourceOrientedDoublePermutationDomain_one_eq
    (d n : ℕ) :
    sourceOrientedDoublePermutationDomain d n
        (1 : Equiv.Perm (Fin n)) =
      sourceOrientedExtendedTubeDomain d n := by
  ext G
  simp [sourceOrientedDoublePermutationDomain,
    sourcePermuteOrientedGram_one]

/-- Conditional relative-openness of oriented double-permutation domains from
relative-openness of the oriented extended-tube image. -/
theorem sourceOrientedDoublePermutationDomain_relOpen_of_sourceOrientedExtendedTubeDomain
    (hU : IsRelOpenInSourceOrientedGramVariety d n
      (sourceOrientedExtendedTubeDomain d n))
    (σ : Equiv.Perm (Fin n)) :
    IsRelOpenInSourceOrientedGramVariety d n
      (sourceOrientedDoublePermutationDomain d n σ) := by
  have hpre :
      IsRelOpenInSourceOrientedGramVariety d n
        {G | sourcePermuteOrientedGram d n σ G ∈
          sourceOrientedExtendedTubeDomain d n} :=
    IsRelOpenInSourceOrientedGramVariety.preimage_sourcePermuteOrientedGram
      (d := d) (n := n) hU σ
  simpa [sourceOrientedDoublePermutationDomain] using
    IsRelOpenInSourceOrientedGramVariety.inter
      (d := d) (n := n) hU hpre

/-- Connectedness of the oriented extended-tube image is the continuous image
of the ordinary extended tube. -/
theorem sourceOrientedExtendedTubeDomain_connected
    (d n : ℕ) :
    IsConnected (sourceOrientedExtendedTubeDomain d n) := by
  simpa [sourceOrientedExtendedTubeDomain] using
    (isConnected_extendedTube (d := d) (n := n)).image
      (sourceOrientedMinkowskiInvariant d n)
      (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).continuousOn

end BHW
