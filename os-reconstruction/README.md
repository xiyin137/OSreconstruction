# Osterwalder-Schrader Reconstruction in Lean

Distributional Euclidean-to-relativistic and relativistic-to-Euclidean
reconstruction, for every positive spatial dimension `d` (spacetime dimension
`d + 1`). Euclidean data act on zero-diagonal Schwartz tests; Wightman
distributions act on full Schwartz space.

## Statements

- [Specification](OSReconstruction/Specification.lean): OS axioms, growth
  conditions, Wick pairing, and the forward/reverse target propositions.
- [Wightman definitions](OSReconstruction/Specification/Wightman.lean): the
  full output record, including spectral support, positivity, and locality.
- [Main theorems](OSReconstruction/Wightman/Reconstruction/Main.lean): the
  public interface and its connections to the separate specification.

`os_to_wightman` assumes the OS axioms and arity-dependent linear growth.
`os_to_wightman_osii_original` additionally concludes the uniform OS II
coordinate-norm bound and uniqueness of the Wick-paired Wightman family.
`OSReconstruction.wightman_to_os_axioms` proves the OS axioms for the actual
Schwinger constructor. The reverse theorem does not assert E0-prime growth.

## Inhabitants

The forward theorem takes `OsterwalderSchraderAxioms d` together with
`OSLinearGrowthCondition d OS`. Neither is inhabited in this package. The
growth condition this package replaces is retained as
`OSFixedOrderGrowthCondition`; `OSFixedOrderGrowthCondition.sobolev_index_eq_zero`
shows that normalization forces its Schwartz order to zero, so it cannot
express the intended positive-order estimates. It is not empty: the trivial
field `S₀(f) = f(0)`, `Sₙ = 0` for `n > 0` satisfies the OS axioms and the
legacy bound with order zero. But at order zero it excludes the theories it
was meant for: the massive free field in spatial dimension 3 violates it
(`gffOS_no_linearGrowth`, by a dilated two-point family whose Schwinger
function grows like `R⁴` against a bounded sup norm), while it satisfies the
corrected condition. Those facts, and a second inhabitant of the corrected
input — the Wick square of the massive Proca field (`procaWickSquareOS`,
`procaWickSquareArityGrowth`) — are formalized in the companion project
`math-commons/yang-mills` (`YangMills/OSRecon/GFF/`,
`YangMills/Continuum/ProcaScalar/`; revision `03bb758`), which vendors this
package's records and checks them declaration by declaration against
`Specification.lean` and `Specification/Wightman.lean`. That repository is
private at the time of writing; access is available on request. Both
inhabitation proofs use only `propext`, `Classical.choice`, and
`Quot.sound`.

See [proof structure](docs/PROOF_STRUCTURE.md) and
[mathematical contract changes](docs/CONTRACT_CHANGES.md).
Operator/GNS reconstruction is not an endpoint of this package.

## Build and Verify

Install Lean using elan. The toolchain is pinned to Lean 4.29.0; Lake dependency
revisions are pinned in `lake-manifest.json`.

```sh
lake exe cache get
bash verification/check.sh full
```

The verification scripts require Bash and Ruby, in addition to Lean/Lake.
They work in an extracted source archive without Git history. `quick` checks
the source import closure and direct admission/axiom census; `contracts`
builds the main interface and runs the Lean guard; `full` performs both checks
and builds the entire default target.

The guard checks the exact target propositions and every loaded project
declaration, including private and generated declarations. It rejects
admissions and project-specific axioms, and permits only the standard
foundations `propext`, `Classical.choice`, and `Quot.sound` in transitive axiom
dependencies. This is not a claim that Lean uses no foundational axioms.

## Source Distribution

The source tree contains the reconstruction dependency closure, including
declarations required to elaborate the retained proofs. Build products,
dependency source trees, Git history, research notes, and development records
are not included. Dependencies are fetched from the public repositories pinned
by Lake. Existing copyright and author notices are retained.

Licensed under [Apache 2.0](LICENSE).
