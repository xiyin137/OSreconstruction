# Proof Structure

The package proves distributional reconstruction in both directions. The
canonical definitions do not import the reconstruction proofs:

```text
Specification/Wightman.lean
          |
Specification.lean
          |
forward and reverse construction lemmas
          |
Wightman/Reconstruction/Main.lean
```

All module paths below the interface are relative to
`OSReconstruction/Wightman/Reconstruction/WickRotation/`.

## Euclidean to Relativistic

Input: `OsterwalderSchraderAxioms d` on zero-diagonal Schwartz space and an
arity-dependent growth bound. The principal steps are:

1. Use reflection positivity to construct Hilbert-space data and time
   evolution from the Euclidean family. The `OSToWightmanOSIIChapterV*`
   modules develop the generated analytic kernels and their estimates.
2. Continue the kernels through increasing analytic domains, controlling
   their growth and distributional boundary values. The
   `OSToWightmanOSIIChapterVI*` modules assemble the full-Schwartz family.
3. Prove normalization, covariance, positive spectral support, the analytic
   tube condition, adjacent locality, coupled positivity, hermiticity, and
   clustering. `OSToWightmanOSIIChapterVINativeReconstruction.lean` collects
   these results in `exists_osii_native_reconstruction`.
4. `OSToWightmanReconstruction.lean` builds `WightmanFunctions` and proves
   `os_to_wightman_full`. `Main.lean` exposes its qualitative public theorem
   `os_to_wightman`.
5. `OSIIQuantitativeReconstruction.lean`, `OSIIOriginalGrowth.lean`, and
   `OSIIQuantitativeEndpoint.lean` supply the original-coordinate R0-prime
   estimate and equivalence of input growth conventions. Uniqueness of a
   Wick-paired family transfers the bound to the public constructor.

The quantitative endpoint chooses positive constants and one positive
integer order before the arity. It bounds every full Schwartz test at each
positive arity and includes uniqueness among families satisfying the same
Wick-pairing contract. Locality and clustering are conclusions, not additional
assumptions supplied by callers.

## Relativistic to Euclidean

Input: `WightmanFunctions d`, including the explicit positive spectral support
and analytic boundary-value conditions.

1. Form the Wick-restricted Schwinger family and prove continuity and
   linearity on zero-diagonal Schwartz tests.
2. `RToEWickPair.lean` establishes that its analytic kernel recovers the
   original full-Schwartz Wightman distributions.
3. `RToEReflectionPositivity.lean` proves the coupled OS positivity condition.
   `RToEIntegralClustering.lean` proves the complete E4 clustering statement.
   The supporting lemmas also establish reality, Euclidean covariance, and
   permutation symmetry.
4. `RToEReconstruction.lean` assembles
   `constructOsterwalderSchraderAxioms` and proves
   `OSReconstruction.wightman_to_os_axioms`.

The conclusion identifies the literal constructor:
`OS.S = constructSchwingerFunctions Wfn`, and proves Wick pairing with
`Wfn.W`. It does not claim that arbitrary Wightman input satisfies the
additional quantitative E0-prime hypothesis of the forward theorem.

## Analytic Support and Checks

`SCV/` supplies Schwartz-space analysis, Fourier-Laplace transforms, boundary
values, and analytic continuation. `ComplexLieGroups/` and `Wightman/Groups/`
supply covariance geometry. The retained `vNA/` modules provide operator and
semigroup infrastructure used in constructing or elaborating the forward
proof; this does not extend the public theorem to operator reconstruction.

`verification/Contracts.lean` ties the public theorems to their independent
target propositions, exercises dimension one and empty-block cases, checks
source availability, and audits the entire loaded declaration environment.
The source census and the transitive axiom audit are separate checks: absence
of an admission at an endpoint alone would not certify all retained sources.
