# Mathematical Contract Changes

The comparison point is the public repository
[`xiyin137/OSreconstruction` at `135ed13df64ab2ba777475358e8d66ee983c291b`](https://github.com/xiyin137/OSreconstruction/tree/135ed13df64ab2ba777475358e8d66ee983c291b).
The current formalization establishes a corrected specification, not that
older theorem with every definition literally unchanged.

1. **Euclidean growth.** The exact seminorm `p_(s,s)` at every arity was
   replaced by `P_(n,s) = max_(k,l <= n*s) p_(k,l)`. The bound is
   `|S_n(f)| <= alpha * beta^n * (n!)^gamma * P_(n,s)(f)`.
   The older normalized condition forced `s = 0`; the corrected condition
   does not.
2. **Analytic growth.** The Wightman record uses polynomial growth uniformly
   over each compact set of admissible imaginary parts, rather than a single
   polynomial bound on the entire forward tube. For each such compact `K`,
   `|F_n(x+iy)| <= C_K (1+|x|)^N_K` for all real `x` and `y` in `K`.
   Holomorphy and full-Schwartz distributional boundary recovery remain.
3. **Spectrum.** Positive spectral support of the reduced distributions is
   an explicit required Wightman field. Reconstruction proves it; this is not
   an additional hypothesis on the OS data.
4. **Full conclusion.** The forward result produces `WightmanFunctions`,
   not only `WightmanFunctionsCore`. Locality and clustering are proved for
   the constructed family.
5. **Quantitative conclusion.** The OS II endpoint chooses one positive
   integer `w` and positive `A,B` before `n`, then proves
   `|W_n(f)| <= A * B^(n^2) * Q_(n*w)(f)` for all `n >= 1` and full Schwartz
   tests. `Q_r` is the original Euclidean-weighted coordinate-derivative norm.
   The original-input growth convention is equivalent to the arity-dependent
   convention after uniform changes of constants. Wick-paired family
   uniqueness is included.

The E0--E4 record, zero-diagonal and full Schwartz test spaces, normalization,
positivity, Wick pairing, cone conventions, and positive spatial-dimension
assumption are unchanged from that comparison point. Locality was already
adjacent-swap locality; its explicit name is a compatibility rename. The
compact-growth compatibility field already constrained the same chosen
kernel and now has a derived default. The current constructor is not
definitionally the older repository's `bvt_W` constructor.

The reverse endpoint supplies all OS axioms and equality with the actual
Schwinger constructor. It does not assert E0-prime growth.

Separating the specification and pruning unused source declarations do not
make further mathematical corrections. The canonical Lean statements in
`OSReconstruction/Specification.lean` are authoritative; this document is a
guide to the differences, not a replacement for those statements.

## Inhabitants of the corrected input

The change in item 1 is not only a relaxation on paper. The older normalized
condition forces its Schwartz order to zero and so cannot express the intended
positive-order estimates; it is inhabited by the trivial field, but violated by
the massive free field. The corrected condition is inhabited by the massive
free field and by the Wick square of the massive Proca field, both formalized
against this package's records in `math-commons/yang-mills` (see the README,
"Inhabitants").

## Retained declarations

Of the 3812 declarations that the package shares by module path and name with
the comparison point, 3789 have identical statements. The 23 that differ are:

- seven uses of the locality predicate, renamed to
  `IsAdjacentLocallyCommutativeWeak` (`toWightmanFunctions`,
  `bargmann_hall_wightman`, and five lemmas in
  `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`);
- `os_to_wightman`, which now returns `WightmanFunctions`;
- two lemmas whose analytic-growth hypothesis changed from the global tube
  bound to the compact-height bound of item 2
  (`W_analytic_lorentz_on_tube_of_restrictedCovariance`,
  `W_analytic_lorentz_bv_agree_of_restrictedCovariance`);
- nine lemmas in `WickRotation/OSToWightmanSemigroup.lean` and one in
  `ComplexLieGroups/SOConnected.lean` that dropped a growth hypothesis, were
  restated in the corrected seminorm, or lost a `private` modifier;
- three declarations that differ only in the spelling of a proof term inside a
  type (a cast in `WickRotation/OSToWightmanBoundaryValueLimits.lean`, and
  namespace-local names in `Wightman/Groups/Lorentz.lean`).

The per-file note "retained mathematical statements unchanged" is accurate
for the declarations outside this list.

