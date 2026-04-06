# Theorem 4 Cluster Blueprint

Purpose: this note is the theorem-specific implementation blueprint for the
live `E -> R` cluster frontier

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_F_clusterCanonicalEventually_translate`.

It is not a paper summary. It is the implementation ledger for the current
production route on `main`.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 8,
- `docs/theorem3_os_route_blueprint.md`,
- `docs/os2_detailed_proof_audit.md` only for the already-used k=2
  continuation background.

## 1. The live theorem and its consumers

The live frontier theorem is:

```lean
private theorem bvt_F_clusterCanonicalEventually_translate
```

in `OSToWightmanBoundaryValues.lean`.

Its immediate consumers are:

1. `bvt_F_clusterCanonicalEventually`
   in `OSToWightmanBoundaryValues.lean`,
2. `bvt_W_cluster`
   in the same file,
3. the public transfer theorem
   `bv_cluster_transfer_of_canonical_eventually`,
4. the exported Wightman axiom
   `HasClusterProperty` through `bvt_W_cluster`.

So theorem 4 is not a leaf theorem. It is the unique live bridge from the
Euclidean/OS cluster package to the public reconstructed Wightman cluster
axiom.

## 2. OS-paper reading of theorem 4

OS I Section 4.4 proves cluster by the same three-layer pattern already used in
Section 4.3:

1. Euclidean cluster on ordered positive-time test data,
2. reinterpretation as an OS Hilbert-space matrix-element statement,
3. transport of that matrix-element statement back to the reconstructed
   Wightman pairing after the positivity/isometry bridge is already available.

So theorem 4 is downstream of theorem 3 in the strict OS route.

This has two immediate implementation consequences.

1. Theorem 4 must consume the theorem-3 one-factor comparison statements.
   It must not try to replace theorem 3.
2. The honest new mathematics in theorem 4 is the Euclidean large-spatial
   factorization and its transport through the already-built boundary-value
   comparison layer. It is not a new continuation problem.

## 3. Exact production theorem hooks already available

The current codebase already contains almost all of the genuine cluster
mathematics.

In `OSToWightmanBoundaryValuesBase.lean`:

1. `schwinger_cluster_osConjTensorProduct_translate_spatial_right_local`
   is the exact Euclidean cluster theorem on the translated single-split shell.
2. `osInner_single_translate_spatial_right_cluster_local`
   rewrites that Schwinger theorem as an OS Hilbert-space matrix-element
   factorization.
3. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
   gives the small-`t` continuity leg on the boundary-value side.
4. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger`
   gives the same limit with the Schwinger target already identified.
5. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
   upgrades the BV-side `xiShift` limit to the translated single-split
   Euclidean identity.
6. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   is the zero-translation specialization.
7. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`
   says large-spatial factorization of the translated OS Hilbert matrix element
   is enough for the translated BV cluster shell.
8. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`
   removes the explicit Hilbert-space matrix element from that theorem.
9. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
   says that once the two one-factor comparisons are known, theorem 4 follows
   on the exact positive-time single-split shell.

In `OSToWightmanBoundaryValues.lean`:

1. `bv_cluster_transfer_of_canonical_eventually`
   is already the public boundary-value-to-Wightman transfer theorem.
2. `bvt_F_clusterCanonicalEventually`
   is just the translated-`g_a` wrapper.
3. `bvt_W_cluster`
   is just `bv_cluster_transfer_of_canonical_eventually` instantiated with
   `bvt_W` and `bvt_F`.

So the current production picture is:

1. the Euclidean cluster theorem exists,
2. the Hilbert-space rewrite exists,
3. the single-split BV shell theorem exists modulo two one-factor comparison
   hypotheses,
4. the public transfer theorem exists,
5. the only live frontier is the missing production connection between those
   pieces.

## 4. Honest remaining gap

The exact already-proved support theorem

```lean
bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison
```

still asks for two hypotheses:

```lean
hleft  : bvt_W OS lgc n f = OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj))
hright : bvt_W OS lgc m g = OS.S m (ZeroDiagonalSchwartz.ofClassical g)
```

with the usual ordered-positive-time and compact-support assumptions on `f` and
`g`.

These hypotheses are now known to be the wrong theorem surface. They are the
same false same-shell comparison pattern already quarantined in theorem 3:

1. the Wightman side is built from the Borchers/Fourier involution;
2. the OS side is built from the Euclidean/Laplace involution
   `osConjTensorProduct`;
3. these are not equal on the same literal test-function input in general.

So theorem 4 splits into two mathematically separate layers.

Layer A: the positive-time single-split cluster core.
- This is reduced to supplying a **corrected** one-factor transport statement,
  not the false same-shell identities `hleft` and `hright`.

Layer B: the public canonical boundary-value theorem
`bvt_F_clusterCanonicalEventually_translate`.
- This still hides the adapter from the public canonical BV shell to the
  positive-time single-split core.

The documentation must keep those two layers separate. If later Lean work
cannot point to an exact theorem name for one of them, that should be treated
as a genuine missing theorem, not hidden inside a long proof.

## 5. What theorem 3 should supply to theorem 4

Theorem 4 should not invent new positivity infrastructure. It should consume
the already-documented theorem-3 comparison package.

The old same-shell factor identities are withdrawn. The corrected theorem-slot
inventory needed by theorem 4 is:

```lean
lemma cluster_left_factor_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    -- theorem-3 / Section-4.3 transport statement identifying the
    -- left one-factor Wightman pairing with the corresponding transported
    -- OS Hilbert-space matrix element
    ... := by

lemma cluster_right_factor_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    -- same transport statement on the untranslated right factor
    ... := by
```

Those should be the exact hypotheses of the **corrected** theorem-4 bridge.

If the current theorem
`bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
continues to demand the false same-shell identities, then that theorem itself
must be treated as deprecated legacy infrastructure and replaced by a corrected
transport-input variant before theorem 4 can be considered settled.

### 5.1. Exact derivation route for the one-factor identities

The needed one-factor transport statements should **not** be described as if
they fell out of theorem 3 by simply "setting one factor equal to the vacuum."
The corrected theorem-3 route no longer supplies same-shell identities at all.
The one-factor cluster inputs arise only after the degree-zero bookkeeping and
the Section-4.3 transport package are both made explicit.

The relevant already-proved production surfaces are:

1. `WightmanInnerProduct_right_single`
2. `OSInnerProduct_right_single`
3. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
4. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right`

The intended paper-faithful route is:

1. choose an auxiliary positive-time Borchers vector concentrated in right
   degree `0`;
2. rewrite the Wightman and OS inner products against that right-single degree
   `0` vector using `WightmanInnerProduct_right_single` and
   `OSInnerProduct_right_single`;
3. observe that the positive-degree `m > 0` shell comparisons supplied by
   theorem 3 are now vacuous, because the auxiliary right vector has no
   positive-degree components;
4. supply the remaining `m = 0` comparison explicitly as the normalized
   zero-degree bookkeeping theorem;
5. read off the desired one-factor identity.

The exact additional theorem-slot inventory is therefore:

```lean
def normalizedZeroDegreeRightVector (d : ℕ) : PositiveTimeBorchersSequence d := by
  exact
    PositiveTimeBorchersSequence.single 0 degreeZeroUnit
      (by
        -- degree 0 has no time coordinates, so ordered-positive-time support is automatic
        simpa using degreeZeroUnit_orderedSupport (d := d))

lemma normalizedZeroDegreeRightVector_bound
    (d : ℕ) :
    (normalizedZeroDegreeRightVector d : BorchersSequence d).bound = 0

lemma normalizedZeroDegreeRightVector_funcs_zero
    (d : ℕ) :
    ((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs 0) = degreeZeroUnit

lemma normalizedZeroDegreeRightVector_funcs_pos
    (d : ℕ) :
    ∀ m > 0,
      ((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs m) = 0

lemma normalizedZeroDegreeRightVector_is_unit_normalized
    (d : ℕ) :
    degreeZeroEvaluation
      (((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs 0)) = 1

lemma zeroDegree_right_single_wightman_extracts_factor
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (f : SchwartzNPoint d n) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d)
      =
      bvt_W OS lgc n f := by
  -- unfold `WightmanInnerProduct_right_single` and the chosen normalization

lemma zeroDegree_right_single_os_extracts_factor
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ) (f : SchwartzNPoint d n) :
    OSInnerProduct d OS.S
      (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d)
      =
      OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj)) := by
  -- unfold `OSInnerProduct_right_single` and the same normalization

lemma zero_degree_component_comparison_for_normalized_right_vector
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    ∀ n,
      -- corrected theorem surface still to be settled:
      -- identify the zero-right component after theorem-3 transport, not by a
      -- same-shell `bvt_W = OS.S` equality
      ... := by
```

The crucial documentation point is that
`normalizedZeroDegreeRightVector` should be the literal degree-zero unit
generator, not an abstract existential placeholder. The four structural lemmas
above should be proved immediately after the definition so the later theorem-4
file can avoid repeated unfolding.

Once those structural lemmas are in place, the remaining theorem-4 input is no
longer a same-shell factor identity. It is a transport statement:

```lean
lemma cluster_left_factor_transport
    ... :
    -- corrected theorem surface still to be settled from theorem 3 Package I:
    -- identify the left one-factor Wightman pairing with the corresponding
    -- transported OS Hilbert-space matrix element
    ... := by
```

The right-factor theorem is the same argument with the nontrivial factor moved
to the right.

So the honest theorem-4 dependency is:

1. theorem 3 gives the corrected Section-4.3 transport package,
2. the degree-zero bookkeeping theorem supplies the missing `hzero` input,
3. the one-factor transport statements are extracted by the right-single
   inner-product lemmas,
4. only then can
   the theorem-4 single-split core be stated on the correct transport-input
   surface.

This is exactly the point where the theorem-4 route touches the "Hermitian
zero-right repair" style bookkeeping already visible in the theorem-3
production chain. The docs should keep that dependency explicit.

### 5.2. Exact `m > 0` versus `m = 0` case split

The later Lean implementation should not leave the zero-degree bookkeeping
inside a single opaque proof term. The route should be documented as an actual
case split.

For the corrected left-factor transport theorem:

1. fix `F_left := PositiveTimeBorchersSequence.single n f hf_ord`,
2. fix `G0 := normalizedZeroDegreeRightVector d`,
3. use theorem 3 only through the corrected transport package, not through any
   same-shell positive-time comparison theorem,
4. observe that every positive-degree right shell comparison is vacuous because
   `(G0 : BorchersSequence d).funcs m = 0` for `m > 0`,
5. provide the unique surviving `m = 0` transport-side bookkeeping theorem;
6. rewrite the resulting Wightman and OS Hilbert-space matrix elements by the
   right-single extraction lemmas;
7. finally rewrite the normalization constants away via the degree-zero unit
   bookkeeping lemmas.

The right-factor identity is the same argument with the nontrivial component on
the right and the normalized degree-zero vector on the left. No new analytic
continuation theorem appears here; the entire step is algebraic/bookkeeping
above theorem 3.

The old same-shell pseudocode is withdrawn. The corrected theorem surface is:

1. theorem 3 supplies the transport package from Section 4.3;
2. theorem 4 adds the degree-zero bookkeeping;
3. right-single extraction turns that transport identity into the one-factor
   transport statements needed by the cluster core.

## 6. Positive-time single-split core

Once the two corrected one-factor transport statements are available, the
positive-time
single-split cluster theorem is already formal.

The exact theorem slot is:

```lean
theorem bvt_cluster_positiveTime_singleSplit_core
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- use the corrected theorem-4 bridge consuming the transport statements,
  -- not the legacy same-shell factor-comparison theorem
  ...
```

This is the theorem that should be proved first once theorem 3 is available.
No new analytic continuation is needed here, but the theorem surface must be
repaired away from the false same-shell inputs before production resumes.

## 7. Public theorem-shape still missing

The public frontier theorem in `OSToWightmanBoundaryValues.lean` does not ask
for ordered-positive-time support or compact support. So after the
single-split core closes, one more wrapper layer still remains.

The documentation should record that layer honestly as:

```lean
theorem bvt_cluster_canonical_from_positiveTime_core
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            ‖(∫ x : NPointDomain d (n + m),
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- exact adapter from the public canonical shell to the positive-time
  -- single-split core
```

At the current repo state, this adapter theorem is not yet isolated under a
separate production name. The docs should therefore not pretend it is already
mechanical. But it should also not treat it as a new Euclidean cluster theorem.
It is a wrapper/adaptation problem sitting strictly above the already-proved
single-split core.

## 8. Exact proof decomposition for theorem 4

The later Lean proof should be carried out in this order.

1. Supply the two one-factor comparison theorems from the theorem-3 package.
2. Apply
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
   to close the positive-time single-split cluster core.
3. Write the explicit adapter from the public canonical BV shell to that
   positive-time core.
4. Reuse the already-proved wrapper
   `bvt_F_clusterCanonicalEventually`.
5. Apply `bv_cluster_transfer_of_canonical_eventually` to get `bvt_W_cluster`.

The later implementation should not invert that order.

## 9. Exact theorem-name dictionary for theorem 4

The theorem names that should appear in the eventual proof script are:

1. `schwinger_cluster_osConjTensorProduct_translate_spatial_right_local`
2. `osInner_single_translate_spatial_right_cluster_local`
3. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
4. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger`
5. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
6. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
7. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`
8. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`
9. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
10. `bvt_F_clusterCanonicalEventually`
11. `bv_cluster_transfer_of_canonical_eventually`

If the eventual implementation does not visibly use that chain, it is likely
drifting away from the current production route.

## 10. Do not do this

1. Do not reopen theorem 3 inside theorem 4.
2. Do not invent a new same-shell Euclidean/Minkowski comparison theorem.
3. Do not bypass the already-proved Euclidean cluster theorem with an ad hoc
   dominated-convergence argument on the boundary-value integral.
4. Do not mix the reverse-direction `R -> E` cluster notes from
   `docs/cluster_property_analysis.md` into this forward theorem-4 route.
5. Do not hide the public canonical-to-positive-time adapter inside the final
   `sorry` proof. If it needs a theorem, name it explicitly first.

## 11. Minimal Lean pseudocode for the full closure

```lean
private theorem bvt_F_clusterCanonicalEventually_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            ‖(∫ x : NPointDomain d (n + m),
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- Step A: close the ordered positive-time single-split core
  have hcore := bvt_cluster_positiveTime_singleSplit_core (d := d) (OS := OS) (lgc := lgc)
  -- Step B: write the exact public canonical-shell adapter
  exact bvt_cluster_canonical_from_positiveTime_core (d := d) (OS := OS) (lgc := lgc)
```

The point of this pseudocode is not that the final theorem is one line. The
point is that every real mathematical ingredient has already been named above.

## 12. Signature cross-checks and implementation contract

The theorem-4 blueprint should now be explicit about which signatures have
already been checked against production and which new local objects must be
introduced exactly as documented below.

### 12.1. Confirmed existing theorem signatures

The following two reduction theorems are already present with the exact
single-right-factor shape needed here:

```lean
theorem WightmanInnerProduct_right_single
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F : BorchersSequence d) {m : ℕ} (g : SchwartzNPoint d m) :
    WightmanInnerProduct d W F (BorchersSequence.single m g) =
      ∑ n ∈ Finset.range (F.bound + 1),
        W (n + m) ((F.funcs n).conjTensorProduct g)
```

```lean
theorem OSInnerProduct_right_single
    (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F : BorchersSequence d) {m : ℕ} (g : SchwartzNPoint d m) :
    OSInnerProduct d S F (BorchersSequence.single m g) =
      ∑ n ∈ Finset.range (F.bound + 1),
        S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((F.funcs n).osConjTensorProduct g))
```

So the later theorem-4 port should not invent any custom right-single lemma.
The existing production theorems already have the correct shape.

### 12.2. Fixed specification of `normalizedZeroDegreeRightVector`

The doc-level object

```lean
normalizedZeroDegreeRightVector : PositiveTimeBorchersSequence d
```

should be implemented only with the following exact semantic properties:

1. `(normalizedZeroDegreeRightVector d : BorchersSequence d).bound = 0`;
2. `((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs 0)` is the
   degree-zero Schwartz function equal to the scalar `1`;
3. `((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs m) = 0` for
   all `m > 0`;
4. the ordered-positive-time support condition is automatic because degree `0`
   has no time coordinates.

The Lean definition should therefore be "the positive-time single concentrated
at degree `0` with value `1`," and the implementation should prove those four
properties immediately and then use only those lemmas. The theorem-4 port
should not rely on unfolding the definition away from those structural lemmas.

### 12.3. Exact theorem package for the one-factor extraction

The later Lean port should build theorem 4 through the following exact theorem
package names unless an exact compile failure forces a local renaming. If that
happens, the docs must be updated at the same time.

```lean
def normalizedZeroDegreeRightVector (d : ℕ) : PositiveTimeBorchersSequence d

lemma normalizedZeroDegreeRightVector_bound
lemma normalizedZeroDegreeRightVector_funcs_zero
lemma normalizedZeroDegreeRightVector_funcs_pos

lemma zeroDegree_right_single_wightman_extracts_factor
lemma zeroDegree_right_single_os_extracts_factor
lemma zero_degree_component_comparison_for_normalized_right_vector
lemma cluster_left_factor_eq_schwinger
lemma cluster_right_factor_eq_schwinger
```

The line `zero_degree_component_comparison_for_normalized_right_vector` is the
only genuinely theorem-4-specific new shell datum. All the rest is bookkeeping
around existing theorem-3 and inner-product infrastructure.

### 12.4. Estimated Lean line counts

The theorem-4 closure is now explicit enough to estimate file size honestly.

1. `normalizedZeroDegreeRightVector` definition plus the three structural
   lemmas:
   roughly `20-45` lines.
2. `zeroDegree_right_single_wightman_extracts_factor`:
   roughly `20-40` lines.
3. `zeroDegree_right_single_os_extracts_factor`:
   roughly `20-45` lines.
4. `zero_degree_component_comparison_for_normalized_right_vector`:
   roughly `25-55` lines.
5. `cluster_left_factor_eq_schwinger`:
   roughly `40-80` lines.
6. `cluster_right_factor_eq_schwinger`:
   roughly `40-80` lines.
7. the positive-time single-split cluster core wrapper:
   roughly `20-40` lines.
8. the final public canonical-shell adapter:
   roughly `25-60` lines.

So theorem 4 should now be thought of as an approximately `210-445` line
package, and most of that is algebraic extraction/bookkeeping rather than new
analytic continuation.

### 12.4.1. Exact theorem package for the public canonical-shell adapter

The positive-time cluster core and the public canonical-shell statement should
be connected by a named adapter package rather than by hidden rewrites in the
final `sorry`.

```lean
lemma canonical_shell_rewrites_to_singleSplit_core
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    canonical_cluster_shell_statement (d := d) OS lgc ->
      positiveTime_singleSplit_cluster_core_statement (d := d) OS lgc

lemma canonical_shell_limit_of_singleSplit_core
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    positiveTime_singleSplit_cluster_core_statement (d := d) OS lgc ->
      canonical_cluster_limit_statement (d := d) OS lgc

theorem bvt_cluster_canonical_from_positiveTime_core
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    canonical_cluster_limit_statement (d := d) OS lgc := by
  have hcore := bvt_cluster_positiveTime_singleSplit_core (d := d) (OS := OS) (lgc := lgc)
  exact
    canonical_shell_limit_of_singleSplit_core (d := d) OS lgc
      (canonical_shell_rewrites_to_singleSplit_core (d := d) OS lgc hcore)
```

The documentation point is that this public adapter should consume only:

1. the positive-time single-split core theorem,
2. the theorem-3 one-factor comparison package already extracted earlier in
   this blueprint,
3. the degree-zero normalization lemmas recorded below.

It should not contain any new analytic-continuation content.

### 12.4.2. Exact proof transcript for the public canonical-shell adapter

The later Lean implementation should write the public adapter as an explicit
three-stage rewrite/transport package:

1. rewrite the public canonical cluster integrand into the positive-time
   single-split shell using the existing canonical-direction / `xiShift`
   comparison lemmas,
2. rewrite the translated right factor into the single-split positive-time form
   used by
   `bvt_cluster_positiveTime_singleSplit_core`,
3. transport the eventual/limit statement through those two rewrites and then
   apply the already-proved positive-time core theorem.

So the actual theorem slots should be read as:

```lean
lemma canonical_cluster_integrand_eq_singleSplit_integrand
lemma canonical_translate_factor_eq_singleSplit_translate_factor
lemma canonical_cluster_eventually_of_singleSplit_core
theorem bvt_cluster_canonical_from_positiveTime_core
```

The proof order should be:

1. integrand-level rewrite,
2. pairing/integral-level rewrite,
3. `Filter.Eventually` transport,
4. final theorem application.

That is why this adapter is a wrapper package and not a new analytic theorem.
If the later Lean proof starts introducing contour or boundary-value arguments
here, it has drifted below the current documentation standard.

## 12.5. Exact hidden normalization identities

The theorem-4 doc should also make explicit the small identities that are easy
to suppress in prose but will matter in the later Lean file.

The normalized degree-zero vector only extracts the desired one-factor theorem
if all of the following are written down as explicit lemmas:

```lean
lemma conjTensorProduct_degreeZeroUnit_eq
    (f : SchwartzNPoint d n) :
    f.conjTensorProduct degreeZeroUnit = cast_to_degree_n f

lemma osConjTensorProduct_degreeZeroUnit_eq
    (f : SchwartzNPoint d n) :
    f.osConjTensorProduct degreeZeroUnit = cast_to_zeroDiagonal_degree_n f.osConj

lemma ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq
    (f : SchwartzNPoint d n) :
    ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct degreeZeroUnit) =
      ZeroDiagonalSchwartz.ofClassical f.osConj
```

The exact coercions/casts above may change in the later implementation, but the
semantic content must not be left implicit:

1. tensoring on the right by the normalized degree-zero unit does not change
   the left factor,
2. the same is true on the OS-conjugated side,
3. the zero-diagonal wrapper does not introduce an extra normalization
   constant.

### 12.5.1. Why these identities matter

Without them, the later port can still prove an equality of inner products, but
it may fail to extract the exact theorem-4 one-factor statement because of
hidden degree-zero casts or scalar constants. The documentation should therefore
force these normalization lemmas to exist under their own names.

### 12.5.2. Estimated Lean size

This hidden-normalization package should be small but explicit:

1. degree-zero unit definition:
   `5-15` lines.
2. two tensor-product normalization lemmas:
   `10-25` lines each.
3. zero-diagonal wrapper lemma:
   `10-20` lines.

So the normalization subpackage should be expected to cost another
`35-85` lines, and that cost should remain visible in the theorem-4 docs.
