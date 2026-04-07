# R-to-E Blueprint

Purpose: this note is the implementation blueprint for the current reverse
reconstruction direction on `main`.

It documents two different theorem surfaces:

1. the theorem that already exists in production,
2. the fuller OS I Section 5 theorem package that would verify the Euclidean
   axioms directly for the constructed Schwinger family.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 10,
- `docs/os2_detailed_proof_audit.md` only for the background BHW/continuation
  route,
- `docs/theorem3_os_route_blueprint.md` only for the warning against false
  same-pairing theorem shapes.

## 1. The current production theorem surface

The current theorem on `main` is:

```lean
theorem wightman_to_os_full
```

in `OSToWightmanBoundaryValues.lean`.

Its exact statement is:

1. construct `S := constructZeroDiagonalSchwingerFunctions Wfn`,
2. prove every `S n` is continuous,
3. prove every `S n` is linear,
4. prove `IsWickRotationPair S Wfn.W`.

So current `main` does **not** claim "the constructed family already satisfies
all OS axioms as a packaged `OsterwalderSchraderAxioms` structure." It claims
the honest weaker bridge theorem `IsWickRotationPair`.

That theorem surface is already proved.

## 2. Exact production hooks already used

The current proof of `wightman_to_os_full` uses only:

1. `constructZeroDiagonalSchwingerFunctions`
   from `BHWTranslation.lean`,
2. `constructedSchwinger_tempered_zeroDiagonal`
   from `SchwingerTemperedness.lean`,
3. `constructedZeroDiagonalSchwinger_linear`
   from `SchwingerAxioms.lean`,
4. `W_analytic_BHW`
   from `BHWExtension.lean`,
5. `bhw_distributional_boundary_values`
   from `BHWTranslation.lean`.

So the currently proved theorem is a very clean OS-I Section 5 bridge:

1. build the common BHW holomorphic object,
2. Wick-restrict it to obtain the Euclidean family,
3. prove continuity and linearity,
4. prove the boundary-value pairing compatibility.

## 3. The exact constructed object

The Euclidean family used on the reverse route is

```lean
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f => wickRotatedBoundaryPairing Wfn n f.1
```

and

```lean
abbrev constructZeroDiagonalSchwingerFunctions (Wfn : WightmanFunctions d) :
    ZeroDiagonalSchwingerFunctions d := constructSchwingerFunctions Wfn
```

in `BHWTranslation.lean`.

So the reverse route is already faithful to OS I Section 5 at the level of the
basic object: the Schwinger family is defined by Wick restriction of the common
holomorphic Wightman object, not by an unrelated algebraic formula.

## 4. What is already done versus what is still a larger theorem package

The current production theorem already proves:

1. the constructed Euclidean family exists,
2. it is continuous,
3. it is linear,
4. it is paired correctly with the given Wightman family through
   `IsWickRotationPair`.

The fuller OS I Section 5 theorem package would additionally verify:

1. Euclidean invariance,
2. Euclidean symmetry,
3. reflection positivity,
4. cluster,
5. the full `E0` temperedness estimate in the Euclidean axioms sense.

Those are not the same theorem surface, and the docs should keep them separate.

## 5. Honest current route constraints

There is a false route still present elsewhere in `SchwingerAxioms.lean`:

1. `schwingerExtension_os_term_eq_wightman_term`
2. `schwingerExtension_os_inner_product_eq_wightman`
3. `schwingerExtension_os_inner_product_eq_wightman_positivity`

That chain is off-paper. It tries to prove reverse-direction positivity by
identifying the OS pairing with the Wightman pairing on the nose.

The current `wightman_to_os_full` theorem does **not** depend on that false
chain. The blueprint should therefore treat the present reverse route as:

1. BHW extension,
2. Wick restriction,
3. honest `IsWickRotationPair`,
4. later reuse of OS I Section 4.3 and 4.4 if a stronger reverse theorem
   surface is desired.

## 6. Exact theorem-slot inventory for a fuller Section 5 formalization

If the repo later wants a stronger theorem such as

```lean
theorem wightman_to_os_axioms_full :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.schwinger = constructSchwingerFunctions Wfn := by
```

then the documentation-standard theorem slots should be:

```lean
lemma constructSchwinger_e0_tempered
    (Wfn : WightmanFunctions d) :
    ∀ n, Continuous (constructSchwingerFunctions Wfn n) := by
  -- Proposition 5.1 / `constructedSchwinger_tempered_zeroDiagonal`

lemma constructSchwinger_linear
    (Wfn : WightmanFunctions d) :
    ∀ n, IsLinearMap ℂ (constructSchwingerFunctions Wfn n) := by
  -- already current production theorem

lemma constructSchwinger_euclidean_invariant
    (Wfn : WightmanFunctions d) :
    EuclideanInvariance (constructSchwingerFunctions Wfn) := by
  -- transport covariance through the BHW extension and Wick restriction

lemma constructSchwinger_symmetric
    (Wfn : WightmanFunctions d) :
    EuclideanSymmetry (constructSchwingerFunctions Wfn) := by
  -- transport permutation symmetry through the same common holomorphic object

lemma constructSchwinger_positive
    (Wfn : WightmanFunctions d) :
    ReflectionPositive (constructSchwingerFunctions Wfn) := by
  -- reuse the Section 4.3 transport package, not the false OS=W chain

lemma constructSchwinger_cluster
    (Wfn : WightmanFunctions d) :
    EuclideanCluster (constructSchwingerFunctions Wfn) := by
  -- reuse the Section 4.4 transport package
```

## 7. Exact proof decomposition for the current theorem

The later maintainer reading `wightman_to_os_full` should understand its proof
as:

1. define the Euclidean family by Wick restriction,
2. obtain continuity from the already-proved temperedness theorem,
3. obtain linearity from the already-proved linearity theorem,
4. obtain the analytic continuation witness from `W_analytic_BHW`,
5. obtain the boundary-value statement from
   `bhw_distributional_boundary_values`.

No positivity theorem, cluster theorem, or Euclidean symmetry theorem is used
in that current proof.

## 8. Where Proposition 5.1 fits

OS I Section 5 is technically centered on Proposition 5.1, the Schwartz bound
for the Wick-restricted pairing on off-diagonal compactly supported tests.

In the current production route:

1. the minimal theorem surface uses only the already-packaged continuity theorem
   `constructedSchwinger_tempered_zeroDiagonal`,
2. the detailed Proposition 5.1 decomposition is documented in
   `docs/os1_detailed_proof_audit.md`,
3. later strengthening from `IsWickRotationPair` to full Euclidean axioms
   should call that Proposition 5.1 package explicitly rather than re-proving
   continuity ad hoc.

So the reverse blueprint should treat Proposition 5.1 as the technical heart of
any future strengthening, even though the current minimal theorem does not
mention it explicitly.

## 9. Exact theorem-name dictionary for the reverse route

The current proof should visibly use:

1. `constructSchwingerFunctions`
2. `constructZeroDiagonalSchwingerFunctions`
3. `constructedSchwinger_tempered_zeroDiagonal`
4. `constructedZeroDiagonalSchwinger_linear`
5. `W_analytic_BHW`
6. `bhw_distributional_boundary_values`
7. `IsWickRotationPair`

The fuller Section 5 route should additionally reuse the Section 4 theorem
packages documented in `docs/os1_detailed_proof_audit.md`.

## 10. Do not do this

1. Do not claim the current theorem already packages the full OS axioms.
2. Do not use the false
   `schwingerExtension_os_inner_product_eq_wightman` route as if it were the
   reverse-direction positivity proof.
3. Do not detach the Euclidean family from the common holomorphic object.
4. Do not re-externalize a large hypothesis list for `wightman_to_os_full`;
   the current theorem surface on `main` is already smaller and cleaner than
   the older hypothesis-heavy drafts.

## 11. Minimal Lean pseudocode for the current theorem and the stronger future one

Current theorem:

```lean
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  · exact current_BHW_boundary_value_proof
```

Future stronger theorem surface:

```lean
theorem wightman_to_os_axioms_full (Wfn : WightmanFunctions d) :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.schwinger = constructSchwingerFunctions Wfn := by
  -- Step A: build the Schwinger family by Wick restriction
  -- Step B: prove E0 via Proposition 5.1
  -- Step C: prove E1/E2 by transporting covariance and permutation symmetry
  -- Step D: prove E3/E4 by reusing the Section 4 positivity/cluster transport
```

## 12. Exact status of the currently existing stronger reverse theorems

The later implementation should distinguish three categories of already-present
theorems in `SchwingerAxioms.lean`.

### 12.1. Directly reusable on the paper route

These are already on the right theorem shape and should be treated as genuine
inputs or model proofs for a future stronger reverse theorem.

1. `wickRotatedBoundaryPairing_symmetric`
2. `wickRotatedBoundaryPairing_reality`
3. `F_ext_permutation_invariant`
4. `bhw_euclidean_reality_ae`

These are all honest Euclidean-side statements about the BHW extension or the
Wick-restricted pairing. They do not identify the OS pairing with the
Wightman pairing on the nose.

### 12.2. Present in the file, but *not* documentation targets

These theorems exist, but their current proof route is off-paper or depends on
an earlier false theorem shape and therefore should not be copied into a future
faithful implementation plan.

1. `schwingerExtension_os_term_eq_wightman_term`
2. `schwingerExtension_os_inner_product_eq_wightman`
3. `schwingerExtension_os_inner_product_eq_wightman_positivity`
4. `wickRotatedBoundaryPairing_reflection_positive`

The future reverse-direction positivity proof should *not* cite those theorems.
It should instead be documented as a fresh transport of the OS I Section 4.3
positivity package to the constructed Schwinger family.

### 12.3. Present, but still incomplete because they sit on other open inputs

These theorems are useful as route indicators, but they are not yet a clean
implementation target because their current proofs depend on open blockers or
axioms elsewhere in the repo.

1. `bhw_pointwise_cluster_forwardTube`
2. `W_analytic_cluster_integral`
3. `wickRotatedBoundaryPairing_cluster`

So the `R -> E` blueprint should document cluster as a future Section 4.4
transport package, not as "already done modulo plumbing."

## 13. Exact OS-I-style theorem-slot inventory for E0-E4

If the repo later strengthens `wightman_to_os_full` to a full
`OsterwalderSchraderAxioms` theorem, the documentation should keep the axiom
fields separated exactly as follows.

### 13.1. E0 temperedness / continuity / linearity

Current production already covers the continuity/linearity surface:

1. `constructedSchwinger_tempered_zeroDiagonal`
2. `constructedZeroDiagonalSchwinger_linear`

The later stronger theorem should simply repackage those under the axiom-field
names, not re-prove them from scratch.

### 13.2. E1 Euclidean invariance

This is not yet isolated in production under a final theorem name. The proof
package should be documented as:

```lean
lemma constructSchwinger_translation_covariant
    (Wfn : WightmanFunctions d) :
    EuclideanTranslationInvariant (constructSchwingerFunctions Wfn) := by
  -- transport real translation covariance of `W_analytic_BHW` through Wick

lemma constructSchwinger_rotation_covariant
    (Wfn : WightmanFunctions d) :
    EuclideanRotationInvariant (constructSchwingerFunctions Wfn) := by
  -- transport the Lorentz/Poincare covariance package to Euclidean rotations

lemma constructSchwinger_euclidean_invariant
    (Wfn : WightmanFunctions d) :
    EuclideanInvariance (constructSchwingerFunctions Wfn) := by
  exact combine_translation_and_rotation_covariance
    (constructSchwinger_translation_covariant Wfn)
    (constructSchwinger_rotation_covariant Wfn)
```

The important documentation point is that E1 should be proved by *transport of
covariance through the common holomorphic object*, not by a direct calculation
on the Wick-restricted integral.

### 13.3. E3 symmetry

This one is already largely present on the correct theorem shape:

```lean
theorem wickRotatedBoundaryPairing_symmetric
```

So the future implementation step for E3 should mostly be a packaging theorem
that re-expresses the existing permutation-invariance result in the exact axiom
field format.

### 13.4. E2 reflection positivity

This is the main reverse-direction trap. The future theorem slot should be
documented as:

```lean
lemma constructSchwinger_positive
    (Wfn : WightmanFunctions d) :
    ReflectionPositive (constructSchwingerFunctions Wfn) := by
  -- do *not* use `schwingerExtension_os_inner_product_eq_wightman`
  -- reuse the OS I Section 4.3 transport package on the Wick-restricted family
```

The reverse blueprint should treat this as a transport theorem from the
already-understood OS-I positivity package, not as a fresh spectral/semigroup
construction and not as an algebraic identity of pairings.

This should also be documented explicitly as a reverse-direction transport:

1. start from Wightman data,
2. build the Wick-restricted Schwinger family,
3. apply the OS I Section 4.3 positivity architecture to that constructed
   Euclidean family.

So the later Lean proof should not cite the forward `E -> R` positivity theorem
as if it automatically runs backward. It should construct the reverse theorem
with the same Section 4.3 proof shape, now applied on the Euclidean family
produced from the Wightman input.

### 13.5. E4 cluster

The future theorem slot should be documented as:

```lean
lemma constructSchwinger_cluster
    (Wfn : WightmanFunctions d) :
    EuclideanCluster (constructSchwingerFunctions Wfn) := by
  -- reuse the OS I Section 4.4 transport package
```

Again, the documentation should prefer the clean Section 4 transport route over
the currently half-open `W_analytic_cluster_integral` lane.

## 14. Exact implementation order for a future full reverse theorem

The later Lean implementation should proceed in this order.

1. Keep `wightman_to_os_full` as the minimal bridge theorem.
2. Repackage the already-proved continuity and linearity theorems as E0.
3. Package E2 from `wickRotatedBoundaryPairing_symmetric`.
4. Package the honest Euclidean-reality lemmas as support input for E3.
5. Prove E3 by transporting the Section 4.3 positivity package.
6. Prove E4 by transporting the Section 4.4 cluster package.
7. Only after E0/E2/E3/E4 are honest should the repo decide whether a full E1
   Euclidean invariance structure is needed at the same theorem surface.

This order matters because it keeps the route faithful to the currently proved
bridge and avoids rebuilding the reverse direction around the false positivity
chain.

## 15. Implementation-ready pseudocode for the stronger theorem surface

```lean
theorem wightman_to_os_axioms_full (Wfn : WightmanFunctions d) :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.schwinger = constructSchwingerFunctions Wfn := by
  let S := constructSchwingerFunctions Wfn
  have hE0_cont : ∀ n, Continuous (S n) := by
    intro n
    simpa [S, constructSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  have hE0_lin : ∀ n, IsLinearMap ℂ (S n) := by
    intro n
    simpa [S, constructSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  have hE2 : EuclideanSymmetry S := by
    intro n σ f g hfg
    simpa [S, constructSchwingerFunctions] using
      wickRotatedBoundaryPairing_symmetric Wfn n σ f g hfg
  have hE3 : ReflectionPositive S := by
    exact constructSchwinger_positive (d := d) Wfn
  have hE4 : EuclideanCluster S := by
    exact constructSchwinger_cluster (d := d) Wfn
  have hE1 : EuclideanInvariance S := by
    exact constructSchwinger_euclidean_invariant (d := d) Wfn
  exact ⟨{
    E0_continuous := hE0_cont
    E0_linear := hE0_lin
    E1_invariant := hE1
    E2_symmetric := hE2
    E3_positive := hE3
    E4_cluster := hE4
  }, rfl⟩
```

This pseudocode is intentionally explicit about the trusted and untrusted
pieces:

1. the E0/E2 slots already point to honest current theorem surfaces;
2. the E3/E4 slots are future targets that must reuse the Section 4 transport
   packages;
3. the old false OS=`Wightman` positivity chain does not appear anywhere in
   the target proof script.

## 16. Concrete proof sketches and route classification for E0-E4

The reverse-direction blueprint should now be explicit about which packages are
already close to implementation and which ones remain theorem-level work.

### 16.1. E0 proof sketch

The E0 package should be a pure repackaging theorem.

1. take `S := constructSchwingerFunctions Wfn`,
2. for continuity use the already-proved
   `constructedSchwinger_tempered_zeroDiagonal`,
3. for linearity use
   `constructedZeroDiagonalSchwinger_linear`,
4. repackage these results under the `E0_*` axiom fields.

Estimated size: `20-40` Lean lines.

### 16.2. E1 proof sketch

E1 should be proved through the common holomorphic object, not by direct
integration on the Wick-restricted side.

1. prove translation covariance of `W_analytic_BHW`,
2. prove rotation covariance of `W_analytic_BHW`,
3. show Wick rotation intertwines the restricted Lorentz subgroup with the
   Euclidean symmetry acting on the Schwinger side,
4. descend those two covariance theorems to `constructSchwingerFunctions Wfn`,
5. combine them into Euclidean invariance.

Estimated size: `80-160` Lean lines, most of which are rewriting and group-
action bookkeeping.

### 16.3. E2 proof sketch

E2 is now an honest packaging theorem around the already-correct symmetry
surface.

1. use `wickRotatedBoundaryPairing_symmetric`,
2. rewrite it into the exact axiom-field format used by the OS structure,
3. discharge any zero-diagonal adapters explicitly.

Estimated size: `20-50` Lean lines.

### 16.4. E3 proof sketch

E3 must *not* go through the false OS=`Wightman` positivity chain.

The honest route is:

1. identify the Wick-restricted family as the Euclidean image of the OS I
   Section 4.3 transport object,
2. prove the diagonal OS form equals the Hilbert norm square on the initial
   positive-time core,
3. extend by polarization/density if the axiom field needs the full
   sesquilinear form,
4. conclude reflection positivity.

Estimated size: `120-220` Lean lines after the OS I Section 4.3 transport
package is implemented under exact theorem names.

### 16.5. E4 proof sketch

E4 should reuse the OS I Section 4.4 cluster transport package.

1. prove the Wick-restricted cluster pairing equals the transported
   Minkowski-side cluster form on the initial core,
2. feed that into the already-proved cluster theorem on the Minkowski side,
3. package the result as Euclidean cluster.

Estimated size: `120-220` Lean lines, again assuming the Section 4 transport
package exists under exact names.

## 17. Classification of current reverse-direction theorem surfaces

The current reverse-direction file should distinguish three statuses:

1. `KEEP`: correct theorem surface that should remain in production.
2. `QUARANTINE`: theorem surface may be mathematically meaningful, but the
   current proof depends on a false or off-paper route and should not be used
   as trusted infrastructure.
3. `DELETE`: theorem surface itself encodes the false route and should not be
   used going forward.

### 17.1. DELETE from the active route

These theorem surfaces encode the false "OS pairing = Wightman pairing"
positivity route and should not appear in later reverse-direction proofs.

1. `schwingerExtension_os_term_eq_wightman_term`
2. `schwingerExtension_os_inner_product_eq_wightman`
3. `schwingerExtension_os_inner_product_eq_wightman_positivity`

If the repo keeps them temporarily for historical reasons, the docs should
still classify them as deleted from the active route.

### 17.2. QUARANTINE until re-proved on the honest route

These theorems are not themselves the false route, but they currently sit
downstream of it and should not be consumed as trusted infrastructure until the
proofs are rerouted.

1. `wickRotatedBoundaryPairing_reflection_positive`

The right long-term fate is to re-prove this theorem from the Section 4.3
transport package and then move it back into the `KEEP` class.

### 17.3. KEEP as honest current surfaces

These are on the right theorem shape and should remain the documentation
targets.

1. `constructSchwingerFunctions`
2. `constructedSchwinger_tempered_zeroDiagonal`
3. `constructedZeroDiagonalSchwinger_linear`
4. `wickRotatedBoundaryPairing_symmetric`
5. `bhw_euclidean_reality_ae`
6. `wightman_to_os_full`

## 18. Estimated Lean line counts for a future full reverse theorem

The reverse blueprint is now detailed enough for rough sizing.

1. E0 packaging:
   `20-40` lines.
2. E1 transport package:
   `80-160` lines.
3. E2 packaging:
   `20-50` lines.
4. E3 honest positivity transport:
   `120-220` lines.
5. E4 honest cluster transport:
   `120-220` lines.
6. final `wightman_to_os_axioms_full` wrapper:
   `20-40` lines.

So the honest route to a full reverse-direction axiom theorem should be thought
of as an approximately `380-730` line package, with almost all of the real
work in the E3/E4 transport theorems rather than in the final wrapper.

## 19. Exact dependency chain for E1/E3/E4

The reverse-direction doc should now write the theorem dependencies in a way
that prevents accidental reuse of the false positivity route.

### 19.1. E1 dependency chain

The later implementation should proceed through these theorem slots:

```lean
lemma W_analytic_BHW_translation_covariant
lemma W_analytic_BHW_rotation_covariant
lemma wickRotate_intertwines_translation_action
lemma wickRotate_intertwines_rotation_action
lemma constructSchwinger_translation_covariant
lemma constructSchwinger_rotation_covariant
theorem constructSchwinger_euclidean_invariant
```

The key documentation constraint is that the action should always be pushed
through the common holomorphic object first, and only then restricted to the
Wick-rotated Euclidean slice.

### 19.2. E3 dependency chain

The later positivity proof should be forced through the following package:

```lean
lemma wickRotatedBoundaryPairing_on_positive_core
lemma wickRotatedBoundaryPairing_eq_transport_inner_on_core
lemma wickRotatedBoundaryPairing_nonneg_on_core
lemma wickRotatedBoundaryPairing_nonneg_by_density
theorem constructSchwinger_positive
```

The docs should continue to ban any route that tries to prove E3 by asserting a
direct equality of the OS form with the Wightman form.

### 19.2.1. Exact proof transcript for the E3 transport package

The later Lean proof should make the transport mechanism literal:

1. define the positive-time Euclidean core generated by Wick-restrictions of
   ordered positive-time Minkowski test data,
2. prove the Wick-restricted pairing on that core agrees with the OS-I
   Section 4.3 transport inner product,
3. deduce nonnegativity on the core from the already-packaged Section 4.3
   positivity theorem,
4. prove the core is dense in the relevant Euclidean positive-time subspace,
5. extend the nonnegativity statement from the core to the closure,
6. repackage the resulting quadratic-form nonnegativity as reflection
   positivity.

So the theorem slots should be read as:

```lean
def wickRotated_positiveTimeCore
lemma wickRotatedBoundaryPairing_eq_transport_inner_on_core
lemma wickRotatedBoundaryPairing_nonneg_on_core
lemma wickRotated_positiveTimeCore_dense
lemma wickRotatedBoundaryPairing_nonneg_by_density
theorem constructSchwinger_positive
```

This is the point where the docs must remain strict: the proof is a transport
and density theorem, not a direct comparison of Euclidean and Minkowski
pairings.

### 19.3. E4 dependency chain

The later cluster proof should be split as:

```lean
lemma wickRotatedBoundaryPairing_cluster_on_core
lemma wickRotatedBoundaryPairing_cluster_transport
lemma wickRotatedBoundaryPairing_cluster_by_density
theorem constructSchwinger_cluster
```

Again, the point is to document cluster as a Section 4.4 transport theorem,
not as a fresh direct integral estimate in `SchwingerAxioms.lean`.

### 19.3.1. Exact proof transcript for the E4 transport package

The later Lean proof should proceed as:

1. define the same Wick-rotated positive-time core used in E3,
2. prove the Euclidean cluster functional on that core agrees with the
   transported Minkowski cluster functional,
3. invoke the OS-I Section 4.4 cluster theorem on the transported Minkowski
   side,
4. deduce the cluster statement on the core,
5. extend from the core to the full Euclidean test space by density and
   continuity of the cluster pairings,
6. package the result as the `E4` axiom field.

So the theorem slots should be:

```lean
lemma wickRotatedBoundaryPairing_cluster_transport_on_core
lemma wickRotatedBoundaryPairing_cluster_on_core
lemma wickRotatedBoundaryPairing_cluster_core_dense
lemma wickRotatedBoundaryPairing_cluster_by_density
theorem constructSchwinger_cluster
```

That keeps the reverse cluster route parallel to the reverse positivity route:
transport on a core first, then density closure.

### 19.4. Implementation consequence

If a later reverse-direction Lean proof tries to jump directly from:

1. `constructSchwingerFunctions`,
2. `wickRotatedBoundaryPairing_symmetric`,
3. `bhw_euclidean_reality_ae`,

to the full E3 or E4 axiom fields without the intermediate transport theorems
above, the docs should be updated first. The current note should no longer
permit hidden large steps in the reverse direction.
