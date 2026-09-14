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
