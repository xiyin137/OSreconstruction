# OS Reconstruction: Status and Remaining Work

## The roundtrip

The OS reconstruction establishes an equivalence between Euclidean (Schwinger)
and Minkowski (Wightman) formulations of QFT. The formal roundtrip consists of
two theorems:

| Direction | Theorem | Status |
|-----------|---------|--------|
| E→R | `os_to_wightman` : OS axioms + linear growth → Wightman functions | Proof assembled, **6 sorrys** in subtheorems |
| R→E | `wightman_to_os` : Wightman functions → Schwinger functions | Proof assembled, **depends on 3 axioms + sorrys in BHW chain** |

Both theorem statements are proved in `Main.lean` from their respective
assembly functions. The sorrys are in the private subtheorems that verify
the individual Wightman/OS axioms.

### Axiom dependencies (from `#print axioms`)

**`os_to_wightman`** depends on:
- `sorryAx` (6 sorrys in W1–W6)
- `tube_boundaryValueData_of_polyGrowth` (SCV axiom: BV existence)

**`wightman_to_os`** depends on:
- `sorryAx` (sorrys in BHW connectivity, Jost/PET, cluster integral)
- `bv_implies_fourier_support` (VT bridge axiom)
- `fl_representation_from_bv` (VT bridge axiom)
- `reduced_bargmann_hall_wightman_of_input` (BHW bridge axiom)

## What can be granted as non-QFT textbook results

The following sorrys/axioms encode standard results from SCV, functional analysis,
algebraic geometry, or topology that are not specific to quantum field theory:

| Item | Nature | Action |
|------|--------|--------|
| `bochner_tube_extension` | SCV (Hörmander 2.5.10) | Already axiomatized |
| `bv_implies_fourier_support` | SCV (Vladimirov 25.1) | Already axiomatized |
| `fl_representation_from_bv` | SCV (Vladimirov 25.5) | Already axiomatized |
| `schwartz_clm_fubini_exchange` | FA (Fréchet Bochner) | Already axiomatized |
| `tube_boundaryValueData_of_polyGrowth` | SCV (Vladimirov 25.2) | Already axiomatized |
| `tube_boundaryValue_of_vladimirov_growth` | SCV (BV existence M>0) | Already axiomatized |
| `dense_submodule_isometry_extension` | FA (BLT, Reed-Simon I §I.7) | Already axiomatized |
| `wickRotation_not_in_PET_null` (W11) | Geometry (Jost §IV.4) | **Grant as axiom** |
| `isPreconnected_baseFiber` (W10) | Topology (PET connectivity) | **Grant as axiom** |
| `isConnected_sliceIndexSet` (PermFlowBlocker) | Topology (Bogolyubov 9.7) | **Grant as axiom** |
| `reduced_bargmann_hall_wightman_of_input` | SCV/topology (BHW bridge) | Already axiomatized |
| `schwartz_nuclear_extension` | FA (nuclear spaces) | Proved in gaussian-field, needs import |
| `exists_continuousMultilinear_ofSeparatelyContinuous` | FA (Banach-Steinhaus) | Proved in gaussian-field, needs import |

Granting all of these, the **R→E direction becomes sorry-free** modulo:
- W8 (`schwingerExtension_os_term_eq_wightman_term`): quarantined/false — should be deleted
- W9 (`W_analytic_cluster_integral`): cluster integral, may be closable from remaining infrastructure

## QFT-specific sorrys: the irreducible core

After granting all non-QFT textbook results, exactly **6 sorrys** remain on the
E→R path. These ARE the OS reconstruction — the mathematical content that
establishes the Euclidean-to-Minkowski bridge.

### W2: Positivity (`bvt_W_positive`) — THE main theorem

**Statement:** The Wightman inner product `⟨F, F⟩_W` is non-negative for all
Borchers sequences F.

**Proof strategy (OS I §4.3):**
1. The OS reflection positivity gives `⟨u, u⟩_OS ≥ 0` for OS Hilbert vectors u.
2. The boundary value identification: for positive-time Euclidean data,
   `⟨F, F⟩_W = ‖u(F)‖²_OS` where u(F) is the OS Hilbert vector.
3. Extend to general Borchers sequences by density + continuity.

**Current status:** The route goes through "Package I" (OS I §4.3 transformed-image
theorem). Packages A-B (one-variable support infrastructure) are proved. The
active frontier is the boundary-value identification step: showing the Wightman
inner product matches the OS inner product on a dense core.

**Difficulty:** Hard. This is the deepest result in the reconstruction. The proof
requires: (a) constructing the OS→Wightman isometry on the positive-time core,
(b) identifying boundary values with OS inner products via analytic continuation,
(c) extending to all Borchers sequences by density. Xiyin's stage 5 work is
actively building infrastructure for this.

**Estimate:** Weeks of focused work, with the boundary-value identification as the
critical bottleneck.

### W1: Locality (`bvt_W_swap_pairing_of_spacelike`) — swap symmetry

**Statement:** For spacelike-separated test functions related by a coordinate
swap, the reconstructed boundary-value functional satisfies
`bvt_W OS lgc n f = bvt_W OS lgc n g`.

**Proof strategy (OS I §4.2):**
1. The OS Euclidean covariance gives permutation symmetry of Schwinger functions.
2. Analytic continuation preserves this symmetry on the extended tube.
3. For spacelike separations, the points lie in the PET (Jost's theorem),
   so the BHW extension gives F(σ·z) = F(z), and the BV pairing commutes.

**Current status:** Depends on the BHW permutation chain (mostly proved, modulo
W10 and the PermutationFlowBlocker sorrys which are grantable as topology).
The remaining work is connecting the BHW permutation symmetry F(σ·z) = F(z)
to the distributional BV swap identity.

**Difficulty:** Medium. The BHW chain is mostly in place. The gap is the
distributional-level swap identity from the pointwise tube identity.

**Estimate:** Days to weeks, depending on how much BHW infrastructure carries through.

### W3: Cluster (`bvt_F_clusterCanonicalEventually_translate`) — factorization

**Statement:** As spatial separation grows, the (n+m)-point BV pairing factorizes
into the product of n-point and m-point pairings.

**Proof strategy (OS I §4.4):**
1. The OS cluster axiom gives factorization of Schwinger functions at large
   spatial separation.
2. Analytic continuation to the tube preserves this asymptotic factorization.
3. The BV limit exchanges with the spatial translation limit.

**Current status:** Depends on W11 (Jost/PET measure zero, grantable) for the
pointwise factorization on the tube, and Fubini for the integral decomposition.

**Difficulty:** Medium. The cluster argument is parallel to the positivity argument
but simpler — no density/closure step is needed, just the limit exchange.

**Estimate:** Days, once the limit-exchange machinery from W2 is available.

### W4: Product tensor witness (`exists_acrOne_productTensor_witness`)

**Statement:** For each arity k, there exists a scalar holomorphic witness on
ACR(1) that reproduces the OS Schwinger functions on product test functions and
satisfies the required symmetry/growth properties.

**Proof strategy:**
1. Start from the OS semigroup construction (already proved via HY/contraction).
2. Build the analytic continuation to ACR(1) using iterated Cauchy integrals.
3. Verify the Euclidean reproduction, symmetry, and growth properties.

**Current status:** The semigroup-to-ACR(1) chain is partially built in
`OSToWightmanSemigroup.lean`. The gap is the product-tensor-specific witness
construction that packages all properties together.

**Difficulty:** Medium. The individual pieces (semigroup, Cauchy integrals,
growth bounds) exist; the challenge is assembling them coherently.

**Estimate:** Days to a week.

### W5: Euclidean kernel package (`acrOne_productTensor_witness_euclidKernelPackage`)

**Statement:** The ACR(1) witness from W4 correctly reproduces the OS Schwinger
functions when composed with Wick rotation and integrated against test functions.

**Proof strategy:**
1. The ACR(1) witness agrees with the semigroup construction on the positive-time
   region (by construction).
2. The semigroup construction reproduces the OS Schwinger functions (proved in
   `OSToWightmanSemigroup.lean`).
3. Chain the two identities.

**Current status:** Depends on W4 for the witness. Once W4 is available, this is
a composition of existing identities.

**Difficulty:** Easy-medium, contingent on W4.

**Estimate:** Hours to days after W4.

### W6: Density (`compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSet`)

**Statement:** The admissible product tensor set (product test functions in the
zero-diagonal Schwartz space) is dense in the full zero-diagonal Schwartz space.

**Proof strategy:**
1. Compactly supported zero-diagonal functions can be approximated by products
   (Stone-Weierstrass type argument on the product structure).
2. The zero-diagonal condition is preserved under this approximation.

**Current status:** The admissible set is defined. The density argument needs
the approximation machinery.

**Difficulty:** Medium. This is a functional analysis / approximation theory result.
It might be axiomatizable as non-QFT textbook if we classify Stone-Weierstrass
on Schwartz spaces as standard FA.

**Estimate:** Days.

## Summary: path to sorry-free OS reconstruction

| Phase | What | Sorrys eliminated | Effort |
|-------|------|-------------------|--------|
| 0 (done) | Grant non-QFT textbook results | R→E direction clean | — |
| 1 | W4-W6: base-step assembly | 3 sorrys | 1-2 weeks |
| 2 | W1: locality via BHW chain | 1 sorry | days-weeks |
| 3 | W3: cluster via limit exchange | 1 sorry | days |
| 4 | W2: positivity (Package I) | 1 sorry (THE theorem) | weeks |

Total estimated effort to sorry-free E→R: **4-8 weeks** of focused work.
The critical path is W2 (positivity), which is the mathematical heart of
OS reconstruction and cannot be shortened by granting textbook results.
