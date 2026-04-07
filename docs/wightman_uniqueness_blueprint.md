# Wightman Uniqueness Blueprint

Purpose: this note is the implementation blueprint for the standalone theorem

- `wightman_uniqueness` in `Wightman/Reconstruction/Main.lean`.

It should be read together with:
- `docs/gns_pipeline_blueprint.md`,
- `docs/gns-pipeline-sorries.md`.

## 1. The live theorem

The theorem surface is:

```lean
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
```

It is not on the reconstruction critical path, but it is the clean endgame
companion to `wightman_reconstruction`.

## 2. Mathematical route

The standard GNS uniqueness proof should be formalized exactly as:

1. define a map on the cyclic word vectors
   `φ₁(f₁)...φ₁(fₙ)Ω₁ ↦ φ₂(f₁)...φ₂(fₙ)Ω₂`,
2. prove the map is well-defined using equality of all smeared n-point
   functions,
3. prove it preserves inner products on the dense cyclic subspaces,
4. extend it by continuity to a unitary on the completed Hilbert spaces,
5. prove it sends vacuum to vacuum and intertwines the field operators.

## 3. Exact prerequisites

The uniqueness theorem depends on:

1. cyclicity for each QFT,
2. the reproducing identity for vacuum matrix elements,
3. the field-domain description by cyclic word vectors,
4. density of the cyclic span in both Hilbert spaces.

So if `gns_cyclicity` is still open, the later implementation must either:

1. prove uniqueness in a general abstract GNS uniqueness library first, or
2. finish cyclicity before attempting `wightman_uniqueness`.

The docs should assume option (2), since that keeps the route closest to the
current codebase.

## 4. Theorem-slot inventory

```lean
def cyclicWordVector
    (qft : WightmanQFT d) :
    List (SchwartzSpacetime d) → qft.HilbertSpace

lemma cyclicWordVector_nil
lemma cyclicWordVector_cons

def uniquenessDenseMap
    (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n fs, qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    CyclicDenseSubspace qft₁ →ₗ[ℂ] CyclicDenseSubspace qft₂

lemma uniquenessDenseMap_wellDefined
lemma uniquenessDenseMap_inner_preserving
lemma uniquenessDenseMap_isometry
lemma uniquenessDenseMap_denseRange
lemma uniquenessDenseMap_extends_to_unitary
lemma uniquenessUnitary_maps_vacuum
lemma uniquenessUnitary_intertwines_field

theorem wightman_uniqueness
```

The later implementation should also isolate the dense-core bookkeeping
explicitly:

```lean
lemma cyclicWordVector_mem_domain
def cyclicWordSpan (qft : WightmanQFT d) : Submodule ℂ qft.HilbertSpace
lemma cyclicWordSpan_eq_vacuum_algebraicSpan
lemma cyclicWordSpan_dense
lemma uniquenessDenseMap_maps_cyclicWord
```

Without these helper theorems, the later proof will keep rediscovering the same
domain and density facts.

## 5. Exact proof decomposition

### 5.1. Well-definedness

To prove the map on cyclic words is well-defined:

1. expand the inner product of two cyclic words on the first QFT,
2. rewrite it entirely as an `(n+m)`-point vacuum expectation,
3. apply the hypothesis `h`,
4. identify the same number as the inner product of the corresponding cyclic
   words on the second QFT.

The proof should not invoke abstract operator-algebra uniqueness theorems at
this stage. It should use the repo’s explicit Wightman-function interface.

### 5.1.1. Exact quotient/descent mechanism

The implementation should not leave the descent step implicit. The correct
order is:

1. define a pre-map on the free finite span of cyclic words,
2. prove that if `ξ` has zero norm in `qft₁`, then its image has zero norm in
   `qft₂`,
3. descend from the pre-Hilbert quotient by the null space,
4. only then package the descended map as `uniquenessDenseMap`.

So the actual theorem slots should be thought of as:

```lean
def uniquenessPreMap :
    FreeCyclicWordSpan qft₁ →ₗ[ℂ] FreeCyclicWordSpan qft₂

lemma uniquenessPreMap_inner_formula
lemma uniquenessPreMap_null_of_null
def uniquenessDenseMap :
    CyclicDenseSubspace qft₁ →ₗ[ℂ] CyclicDenseSubspace qft₂
```

The key proof of `uniquenessPreMap_null_of_null` is:

1. assume `‖ξ‖ = 0` in the quotient on the `qft₁` side,
2. rewrite `‖ξ‖²` as `⟪ξ, ξ⟫`,
3. rewrite that inner product using the vacuum `(n+m)`-point expansion,
4. transfer the value to the `qft₂` side by `h`,
5. conclude the image also has norm square zero.

This is the only non-formal descent step. Once it is proved, the quotient map
is honest.

### 5.1.2. Exact cyclic-word inner-product formula

The implementation should explicitly prove the formula:

```lean
lemma cyclicWordVector_inner_cyclicWordVector
    (Fs : List (SchwartzSpacetime d)) (Gs : List (SchwartzSpacetime d)) :
    ⟪cyclicWordVector qft Fs, cyclicWordVector qft Gs⟫_ℂ
      =
    qft.wightmanFunction (Fs.length + Gs.length)
      (joinedConjugatedTestFamily Fs Gs)
```

The proof is by induction on `Fs`, pushing adjoints across the vacuum and using
the Wightman hermiticity/domain axioms already packaged in `WightmanQFT`.

That theorem is the real heart of uniqueness. All later inner-product
preservation statements should be short corollaries of it.

### 5.2. Isometry

Once well-definedness is proved, isometry is formal:

1. the map preserves inner products on the dense cyclic subspaces,
2. hence it preserves norms,
3. hence it extends uniquely to an isometry on the Hilbert completion.

The later Lean file should split that into:

```lean
lemma uniquenessDenseMap_inner_preserving
lemma uniquenessDenseMap_norm_preserving
lemma uniquenessDenseMap_isometry
```

so that the completion-extension theorem can consume the isometry theorem
directly, with no hidden algebra.

### 5.3. Surjectivity / unitary

There are two standard routes:

1. show the same construction in the reverse direction and prove the two
   extensions are mutual inverses;
2. or show the image contains the dense cyclic subspace of `qft₂`.

The documentation-standard route should use (2), because it avoids building a
second abstract map.

### 5.3.1. Exact dense-range proof

The dense-range proof should be written literally as:

1. every cyclic word vector in `qft₂` is the image of the corresponding cyclic
   word vector in `qft₁`,
2. therefore `cyclicWordSpan qft₂` is contained in the range of
   `uniquenessDenseMap`,
3. `cyclicWordSpan qft₂` is dense by cyclicity,
4. hence the range of `uniquenessDenseMap` is dense,
5. an isometry with dense range extends to a unitary.

This avoids ever needing a second inverse construction.

The theorem slots should therefore be:

```lean
lemma cyclicWord_in_range_of_uniquenessDenseMap
lemma cyclicWordSpan_le_range_uniquenessDenseMap
lemma uniquenessDenseMap_denseRange
lemma uniquenessDenseMap_extends_to_unitary
```

### 5.4. Intertwining the field

The field intertwining theorem should be proved only after the unitary exists.

Exact route:

1. first prove the intertwining identity on cyclic vectors in the field domain,
2. then lift it to the stated domain theorem in `Main.lean`.

### 5.4.1. Exact field-domain proof transcript

The later Lean proof should not try to prove intertwining on an arbitrary
domain vector first. The correct order is:

1. prove
   `U (fieldWordAction qft₁ f ξ) = fieldWordAction qft₂ f (U ξ)`
   on the cyclic-word span,
2. identify the cyclic-word span as a core inside `qft₁.field.domain`,
3. use closedness/continuity of the field operators on their domains to extend
   the intertwining identity from the core to every `ψ ∈ qft₁.field.domain`.

So the actual theorem-slot inventory should include:

```lean
lemma uniquenessUnitary_intertwines_field_on_cyclic_core
lemma cyclicWordSpan_is_field_core
lemma uniquenessUnitary_intertwines_field
```

This keeps the domain argument honest and prevents the final theorem from
hiding an unproved graph-closure step.

## 6. Lean-style pseudocode

```lean
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
      qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    ∃ U : qft₁.HilbertSpace →ₗᵢ[ℂ] qft₂.HilbertSpace,
      U qft₁.vacuum = qft₂.vacuum ∧
      (∀ (f : SchwartzSpacetime d) (ψ : qft₁.HilbertSpace),
        ψ ∈ qft₁.field.domain →
        U (qft₁.field.operator f ψ) = qft₂.field.operator f (U ψ)) := by
  let T := uniquenessDenseMap qft₁ qft₂ h
  have hT_iso : Isometry T := uniquenessDenseMap_isometry qft₁ qft₂ h
  have hT_dense : DenseRange T := uniquenessDenseMap_denseRange qft₁ qft₂ h
  obtain ⟨U, hU_ext⟩ := uniquenessDenseMap_extends_to_unitary qft₁ qft₂ h hT_iso hT_dense
  refine ⟨U, ?_, ?_⟩
  · exact uniquenessUnitary_maps_vacuum qft₁ qft₂ h hU_ext
  · intro f ψ hψ
    exact uniquenessUnitary_intertwines_field qft₁ qft₂ h hU_ext f ψ hψ
```

## 7. Do not do this

1. Do not re-prove the whole GNS construction in the uniqueness theorem.
2. Do not hide the dense cyclic subspace inside an opaque quotient argument.
3. Do not use a theorem about “same Wightman functions implies same GNS space”
   unless it is made explicit in the repo under a named theorem.
4. Do not mix this theorem with the `R -> E` or `E -> R` routes.

## 8. What counts as implementation-ready

This uniqueness blueprint should be considered ready only when:

1. the dense cyclic-word map is explicitly named,
2. well-definedness/isometry/dense-range/unitary-extension are split,
3. the dependency on cyclicity is stated openly,
4. the field intertwining is documented as a post-unitary theorem, not hidden
   in the existence proof.

## 9. Recommended implementation order and size

The later Lean work should attack this file in the following order:

1. cyclic-word core definitions and domain lemmas,
2. cyclic-word inner-product formula,
3. pre-map and quotient descent,
4. dense-range/unitary extension,
5. field-core intertwining,
6. final assembly theorem.

Rough expected size:

1. cyclic-word core and density: 120-180 lines,
2. inner-product formula and descent: 120-180 lines,
3. unitary extension and intertwining: 80-140 lines,
4. final assembly theorem: 20-40 lines.

This note is implementation-ready once those six steps are read as the literal
construction order rather than as a high-level summary.
