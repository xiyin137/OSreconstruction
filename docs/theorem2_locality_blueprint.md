# Theorem 2 Locality Blueprint

Purpose: this note is the theorem-specific implementation blueprint for the
live `E -> R` locality frontier

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_F_swapCanonical_pairing`.

This is the current theorem-2 `main` route. It supersedes older gap notes that
were written before `edge_of_the_wedge` was proved as a theorem.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 9,
- `docs/theorem3_os_route_blueprint.md` only for route discipline,
- `docs/edge_of_the_wedge_proof_plan.md` and
  `docs/edge_of_the_wedge_gap_analysis.md` only as historical reference.

## 1. The live theorem and its consumers

The live frontier theorem is:

```lean
private theorem bvt_F_swapCanonical_pairing
```

in `OSToWightmanBoundaryValues.lean`.

Its immediate consumers are:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   in `OSToWightmanBoundaryValuesComparison.lean`,
2. `bvt_locally_commutative`
   in `OSToWightmanBoundaryValues.lean`,
3. the public Wightman axiom field `locally_commutative` in
   `os_to_wightman_full`.

So theorem 2 is the unique boundary-value bridge from the analytic permutation
package to the public locality axiom.

## 2. OS-paper reading of theorem 2

OS I Section 4.5 proves locality by:

1. Euclidean symmetry on the real side,
2. analytic continuation to overlapping permuted tube domains,
3. a uniqueness / edge-of-the-wedge step,
4. passage to boundary values.

This means theorem 2 belongs to the BHW / PET / Jost / edge-of-the-wedge lane.
It is not part of the theorem-3 positivity / semigroup lane.

## 3. Exact production hooks already available

The current code already contains the major analytic ingredients.

In `OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_F_perm`
   gives permutation invariance of the analytic boundary-value continuation
   `bvt_F`.

In `BHWExtension.lean`:

1. `W_analytic_swap_boundary_pairing_eq`
   gives adjacent-swap equality of boundary pairings for compactly supported
   tests whose real support already lies in the extended tube.
2. `analytic_extended_local_commutativity`
   gives pointwise adjacent-swap equality on real ET overlap points for the BHW
   extension.
3. `analytic_boundary_local_commutativity_of_boundary_continuous`
   descends that pointwise equality from `BHW.extendF W_analytic` to raw
   boundary values of `W_analytic`, provided the needed boundary continuity is
   available at the two real ET points.
4. `W_analytic_BHW`
   packages the BHW extension used by the reverse-direction side and by any
   later uniqueness comparison.

In `AnalyticContinuation.lean` and `SCV/TubeDomainExtension.lean`:

1. `edge_of_the_wedge`
   is a proved theorem, not an axiom.
2. `SCV.edge_of_the_wedge_theorem`
   is the underlying multi-dimensional theorem.
3. `jost_lemma`
   packages the real-point spacelike geometry on the extended tube.

In `OSToWightmanBoundaryValuesComparison.lean`:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   is already the public transfer theorem from the canonical BV swap pairing to
   locality of the reconstructed Wightman distribution.

So theorem 2 does not lack edge-of-the-wedge infrastructure any more. The live
gap is the last boundary-pairing adapter that feeds the existing transfer
theorem.

## 4. Honest remaining gap

The current frontier theorem asks directly for equality of the two canonical BV
pairings

```lean
∫ bvt_F(... canonical shift ...) * g
=
∫ bvt_F(... canonical shift ...) * f
```

under:

1. adjacent spacelike separation on the support of `f`,
2. `g = f ∘ swap(i,j)`.

The BHW package already proves the analogous statement for `BHW.extendF` or for
raw `W_analytic` values at real ET points, but only after the following data
have been supplied explicitly:

1. the support points lie in the extended tube,
2. the swapped support points also lie in the extended tube,
3. the relevant boundary values of the analytic representative are continuous
   from the forward tube.

So the remaining theorem-2 task is not "prove locality from scratch." It is:

1. identify the exact analytic representative behind `bvt_F`,
2. prove the support-to-ET geometry needed by the BHW theorems,
3. prove the boundary continuity hypotheses on the canonical real support,
4. transfer the resulting BHW swap theorem back to the raw canonical BV
   pairing.

## 5. Exact theorem-slot inventory still needed

The documentation-standard theorem slots are:

```lean
lemma canonical_support_mem_extendedTube_of_adjacent_spacelike
    (f : SchwartzNPoint d n)
    (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n := by
  -- Jost / ET geometry for the real support

lemma canonical_swap_support_mem_extendedTube_of_adjacent_spacelike
    (f g : SchwartzNPoint d n)
    (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j))
    (hswap : ∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) :
    ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n := by
  -- same geometry on the swapped support

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- boundary continuity of the analytic representative at the real support

theorem bvt_F_swap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i j : Fin n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (f x) := by
  -- invoke `W_analytic_swap_boundary_pairing_eq` or
  -- `analytic_boundary_local_commutativity_of_boundary_continuous`
```

The last theorem is not yet the live frontier theorem because the public
canonical pairing uses the canonical imaginary cone shift. So one final adapter
is still needed.

### 5.1. Concrete proof strategy for the boundary-continuity slot

The continuity theorem above should not remain a bare placeholder. There is a
concrete current candidate route in the repo:

1. [boundary_function_continuous_forwardTube_of_flatRegular](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean#L652)
   proves continuity of the real trace of a forward-tube holomorphic function,
   provided one has a regular flattened Fourier-Laplace package
   `SCV.HasFourierLaplaceReprRegular`.
2. The later theorem-2 implementation should therefore aim first for a regular
   flattened package for `bvt_F OS lgc n`, not for pointwise continuity by raw
   epsilon-delta arguments.

So the preferred theorem-slot inventory is:

```lean
lemma flattened_bvt_F_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n))

lemma flattened_bvt_F_has_boundary_distribution
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma flattened_bvt_F_has_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n

lemma bvt_F_boundary_continuous_on_real_trace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    Continuous (fun x : NPointDomain d n => bvt_F OS lgc n (fun k μ => (x k μ : ℂ))) := by
  exact
    boundary_function_continuous_forwardTube_of_flatRegular
      (d := d) (n := n)
      (bvt_F_holomorphic OS lgc n)
      (bvt_F_hasFlatRegularRepr (d := d) OS lgc n)

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- derive `ContinuousWithinAt` from the global real-trace continuity theorem,
  -- together with the forward-tube approach geometry at real points
```

This is the right current route because it uses already-proved transport
results in `ForwardTubeDistributions.lean` rather than inventing a new local
boundary continuity argument.

If `bvt_F_hasFlatRegularRepr` turns out not to be obtainable from the current
production growth package, then that regular package itself is the honest
theorem-2 blocker and should be documented under that exact name before any
locality proof resumes.

The key documentation correction is:

1. there is no current repo theorem named
   `SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth`,
2. the actual missing theorem package is the constructor
   `flatRegular_of_boundary_distribution_and_polyGrowth`,
3. the later locality proof should therefore treat the regular constructor as
   the hard analytic input and the continuity theorem as a downstream consumer.

### 5.2. Exact subpackages behind `bvt_F_hasFlatRegularRepr`

The regular flattened package should itself be documented as a small theorem
suite, not as one unexplained miracle theorem.

The later Lean port should split it into:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n)) := by
  -- transport `bvt_F_holomorphic` through the flattening equivalence

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap) := by
  -- flattened form of the existing boundary-value package for `bvt_F`

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  -- transport the current growth package for `bvt_F`

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n
```

This is the correct level of explicitness for theorem 2 because the
`ForwardTubeDistributions` package already proves the final transport theorems.
What remains open is the *input package* for `bvt_F`, not the continuity
conclusion itself.

The constructor theorem should be read as an actual future file target:

1. prove the flattened holomorphic theorem,
2. prove the flattened boundary-distribution theorem,
3. prove the flattened polynomial-growth theorem,
4. combine those three inputs in a new SCV/forward-tube regularity constructor,
5. only then specialize to `bvt_F_hasFlatRegularRepr`.

### 5.3. Exact route from continuity to the raw-boundary swap pairing

Once the regular flattened package is in place, the later proof should not jump
straight to the canonical shifted pairing. There is an intermediate raw-boundary
theorem surface:

```lean
theorem bvt_F_swap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i j : Fin n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * g x
        =
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * f x := by
  intro f g hf_compact hg_compact hsep hswap
  have hf_ET := canonical_support_mem_extendedTube_of_adjacent_spacelike
    (d := d) (n := n) f i j hsep
  have hg_ET := canonical_swap_support_mem_extendedTube_of_adjacent_spacelike
    (d := d) (n := n) f g i j hsep hswap
  have hcont := bvt_F_boundary_continuous_at_real_support (d := d) OS lgc n
  exact
    analytic_boundary_local_commutativity_of_boundary_continuous
      (d := d) (n := n) (W_analytic_BHW := ?_)  -- existing BHW analytic input
      hf_compact hg_compact hf_ET hg_ET hcont hswap
```

Only after this raw-boundary theorem is in place should the later file prove
the canonical-shift adapter. That final adapter should be documented as a
separate wrapper theorem because it changes the evaluation surface from
`x ↦ x` to `x ↦ x + i ε η_can`, and that change is not part of the BHW
locality theorem itself.

### 5.4. Exact support-to-ET geometry route

The ET-support lemmas should also not remain black boxes. The current repo
already contains the geometric package that should drive them:

1. `JostSet`, `ForwardJostSet`, and `realEmbed` in
   `ComplexLieGroups/JostPoints.lean`;
2. `forwardJostSet_subset_extendedTube`, the actual Jost lemma theorem;
3. the distributional adjacent-swap package in
   `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`,
   especially
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`.

The intended theorem-2 support route should therefore be:

```lean
lemma canonical_support_mem_forwardJost_of_adjacent_spacelike
    (f : SchwartzNPoint d n) (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      x ∈ ForwardJostSet d n hd := by
  -- strengthen the support hypothesis from adjacent spacelike separation to the
  -- forward-Jost condition needed by the existing Jost lemma package

lemma canonical_support_mem_extendedTube_of_adjacent_spacelike
    (f : SchwartzNPoint d n) (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n := by
  intro x hx
  exact
    forwardJostSet_subset_extendedTube (d := d) (n := n) hd x
      (canonical_support_mem_forwardJost_of_adjacent_spacelike
        (d := d) (n := n) f i j hsep x hx)
```

There are two honest possibilities here, and the docs should keep them distinct:

1. the current support hypothesis already implies the needed forward-Jost
   condition after a local normalization of the adjacent pair, in which case
   `canonical_support_mem_forwardJost_of_adjacent_spacelike` is provable;
2. or the present theorem surface is slightly too weak, and theorem 2 must be
   routed through the already existing distributional adjacent-swap theorem in
   `AdjacencyDistributional.lean`, whose ET hypotheses are stated directly.

The documentation-standard rule is:

1. first try to prove the support theorem from the current locality hypothesis;
2. if that fails, document the exact missing geometric strengthening explicitly
   rather than hiding it inside the closing `sorry`.

### 5.5. Lean-style endgame script with all remaining theorem slots visible

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * g x
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  intro n i j f g ε hε hsep hswap
  have hraw :
      ∫ x : NPointDomain d n, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * g x
        =
      ∫ x : NPointDomain d n, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * f x := by
    exact
      bvt_F_swap_boundary_pairing_eq_of_ET_support
        (d := d) (OS := OS) (lgc := lgc) n i j f g
        (schwartz_compactSupport_if_needed ...)
        (schwartz_compactSupport_if_needed ...)
        hsep hswap
  exact
    bvt_F_swapCanonical_pairing_from_raw_boundary_locality
      (d := d) (OS := OS) (lgc := lgc) n i j f g ε hε hraw
```

This is the closure standard the docs should now enforce:

1. ET support geometry named,
2. boundary continuity package named,
3. raw-boundary swap theorem named,
4. canonical-shift adapter named.

If any one of those four is missing in a later Lean proof, then theorem 2 is
still underdocumented.

## 6. Canonical-shift adapter required by the frontier theorem

The consumer
`bv_local_commutativity_transfer_of_swap_pairing`
expects the canonical shifted pairing, not the raw real-support pairing.

So the last theorem slot should be:

```lean
theorem bvt_F_swapCanonical_pairing_from_raw_boundary_locality
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- transport the raw-boundary theorem through the actual canonical BV
  -- boundary-value formula
```

At the current repo state, the exact theorem implementing that last transport
has not yet been isolated under a separate name. The docs should therefore keep
it visible as a genuine final adapter theorem rather than hiding it inside the
closing `sorry`.

## 7. Exact proof decomposition for theorem 2

The later Lean proof should run in this order.

1. Use Jost / ET geometry to show the real supports of `f` and `g` lie in the
   extended tube.
2. Supply the same ET geometry for the swapped support.
3. Supply the boundary-continuity theorem for the chosen analytic
   representative behind `bvt_F`.
4. Apply `W_analytic_swap_boundary_pairing_eq` or
   `analytic_boundary_local_commutativity_of_boundary_continuous`.
5. Transport that raw-boundary theorem to the canonical shifted pairing
   statement.
6. Feed the result into
   `bv_local_commutativity_transfer_of_swap_pairing`.

The theorem should not be attacked by re-proving edge-of-the-wedge or by
opening a new permutation-continuation front in the middle of
`OSToWightmanBoundaryValues.lean`.

## 8. Historical docs that are no longer frontier guidance

The following docs are historical and should not be used as primary route
guidance for theorem 2:

1. `docs/edge_of_the_wedge_proof_plan.md`
2. `docs/edge_of_the_wedge_gap_analysis.md`

Both were written before the theorem

```lean
SCV.edge_of_the_wedge_theorem
```

was proved. They are still useful for mathematical context, but they do not
describe the current production frontier on `main`.

## 9. Exact theorem-name dictionary for theorem 2

The later proof should visibly use:

1. `bvt_F_perm`
2. `bv_local_commutativity_transfer_of_swap_pairing`
3. `W_analytic_swap_boundary_pairing_eq`
4. `analytic_extended_local_commutativity`
5. `analytic_boundary_local_commutativity_of_boundary_continuous`
6. `edge_of_the_wedge`
7. `SCV.edge_of_the_wedge_theorem`
8. `jost_lemma`

If those names do not appear in the route, the implementation is likely
drifting back toward a stale or over-optimistic locality plan.

## 10. Do not do this

1. Do not reintroduce edge-of-the-wedge as an axiom or a missing theorem.
2. Do not mix theorem 2 with theorem 3 positivity reductions.
3. Do not claim locality directly from permutation invariance of `bvt_F` alone;
   the real issue is boundary pairing and ET/Jost support geometry.
4. Do not use the historical edge-of-the-wedge gap notes as if they still
   described `main`.
5. Do not hide the raw-boundary-to-canonical adapter inside the closing
   `sorry`.

## 11. Minimal Lean pseudocode for the full closure

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- Step A: prove the raw-boundary swap theorem from the BHW package
  have hraw :=
    bvt_F_swap_boundary_pairing_eq_of_ET_support (d := d) (OS := OS) (lgc := lgc)
  -- Step B: transport raw-boundary locality to the canonical shifted BV pairing
  exact
    bvt_F_swapCanonical_pairing_from_raw_boundary_locality
      (d := d) (OS := OS) (lgc := lgc)
```

## 12. The regular-input constructor theorem that is actually missing

The current blueprint should now be explicit about one important fact:

```lean
SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth
```

does **not** exist anywhere in the current repo.

What *does* exist is the downstream package that *consumes*
`HasFourierLaplaceReprRegular`:

1. `boundary_function_continuous_forwardTube_of_flatRegular`,
2. `boundary_value_recovery_forwardTube_of_flatRegular`,
3. `distributional_uniqueness_forwardTube_of_flatRegular`,
4. `polynomial_growth_forwardTube_of_flatRegular`.

So the theorem-2 route should be documented as requiring a new constructor
package, not as a one-line application of an already-existing helper.

The honest theorem-slot inventory is:

```lean
lemma flattened_bvt_F_has_boundary_distribution
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma flattened_bvt_F_has_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
```

The first two are already the theorem shapes the blueprint was using. The third
is the real missing theorem. Only the fourth is an adapter name specialized to
`bvt_F`.

### 12.1. What the constructor proof must look like

The later Lean proof should be documented as:

1. prove holomorphy of the flattened function from `bvt_F_holomorphic`,
2. prove distributional boundary values of the flattened function using the
   existing `bvt_W` boundary package,
3. prove polynomial growth on the flattened tube from the already-constructed
   growth package for `bvt_F`,
4. package those three inputs into a new regular constructor theorem,
5. only then call the forward-tube continuity/recovery theorems.

The critical point is that Step 4 is a real theorem package, not a missing
`simpa`.

### 12.2. Estimated Lean line counts for the regular package

1. flattened boundary-value adapter:
   roughly `25-60` lines.
2. flattened growth adapter:
   roughly `20-50` lines.
3. regular constructor theorem
   `flatRegular_of_boundary_distribution_and_polyGrowth`:
   roughly `60-120` lines if done directly in the flattened SCV language.
4. specialization to `bvt_F_hasFlatRegularRepr`:
   roughly `10-25` lines.

So the honest continuity package here is roughly `115-255` lines, and the
central missing theorem is the regular constructor, not the continuity theorem
itself.

## 13. Exact support-to-ET geometry proof sketch

The theorem-2 docs should also write the support route at theorem-script level,
because the geometry package is already largely present.

The later proof should proceed as follows.

1. Start from the support hypothesis
   `∀ x, f.toFun x ≠ 0 -> AreSpacelikeSeparated d (x i) (x j)`.
2. Upgrade it to forward-Jost membership on the support via the explicit Jost
   predicate in `ComplexLieGroups/JostPoints.lean`.
3. Convert forward-Jost membership to extended-tube membership by the proved
   theorem
   `forwardJostSet_subset_extendedTube`.
4. Push the same argument through the swapped test function using the support
   equality hypothesis.
5. Feed the resulting ET support theorems to the already-proved analytic
   boundary locality theorem.

In Lean-style pseudocode:

```lean
lemma canonical_support_mem_extendedTube_of_adjacent_spacelike
    (f : SchwartzNPoint d n) (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n := by
  intro x hx
  have hxFJ :
      x ∈ ForwardJostSet d n (by omega) := by
    exact support_mem_forwardJost_of_adjacent_spacelike (d := d) (n := n) f i j hsep x hx
  exact
    forwardJostSet_subset_extendedTube (d := d) (n := n) (by omega) x hxFJ
```

This is a `20-40` line theorem once the forward-Jost support lemma is written.
The forward-Jost support lemma itself should be roughly `15-35` lines.

## 14. Exact proof sketch for the raw-boundary-to-canonical adapter

The theorem

```lean
bvt_F_swapCanonical_pairing_from_raw_boundary_locality
```

should not be left as a slogan. The later Lean proof should be a named three-
step adapter.

1. apply the raw-boundary theorem to the underlying real-edge test functions;
2. rewrite the canonical shifted pairing as the raw pairing against the
   boundary trace by the boundary-value recovery theorem;
3. use the same rewrite on both `f` and `g` and conclude by transitivity.

The theorem-slot inventory should therefore be:

```lean
lemma canonical_shell_pairing_eq_raw_boundary_pairing
lemma swapped_canonical_shell_pairing_eq_swapped_raw_boundary_pairing
theorem bvt_F_swapCanonical_pairing_from_raw_boundary_locality
```

Estimated Lean size:

1. first rewrite lemma:
   `20-40` lines;
2. swapped rewrite lemma:
   `10-25` lines;
3. final adapter theorem:
   `15-35` lines.

So the theorem-2 endgame above the raw-boundary theorem is now only a
`45-100` line adapter package, and that should stay explicit in the docs.

## 15. The `d = 1` / forward-Jost subtlety must stay explicit

The locality blueprint should now record one genuine geometry subtlety that is
easy to lose sight of in pseudocode:

1. `ForwardJostSet d n hd` is defined by a condition on **every consecutive
   difference**,
2. the theorem-2 locality hypothesis only names one adjacent pair of indices,
3. so the implication
   "adjacent spacelike support hypothesis ⇒ support lies in `ForwardJostSet`"
   is **not** automatic at the theorem surface as currently written.

This matters most in `d = 1`, but the documentation should treat it as a
general theorem-shape issue, not as a one-dimensional anomaly.

### 15.1. What is safe to claim

The docs may safely claim:

1. if the support is already known to lie in an open edge `V` with
   `realEmbed '' V ⊆ ExtendedTube`,
   then the BHW pairing theorem can be applied directly;
2. if a stronger support theorem is proved that upgrades the locality support
   hypothesis to `ForwardJostSet` membership, then
   `forwardJostSet_subset_extendedTube` closes the geometry step;
3. the current theorem-2 route does **not** require us to prove the stronger
   forward-Jost statement first, because the pairing theorem
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
   already accepts ET-support hypotheses as inputs.

### 15.2. What is *not* safe to claim

The docs should not claim, without a new theorem:

1. one adjacent spacelike-separation hypothesis automatically implies
   `ForwardJostSet` membership on the whole support;
2. the theorem-2 geometry step is already reduced to
   `forwardJostSet_subset_extendedTube` alone;
3. the `d = 1` case is a cosmetic special case of the same argument.

### 15.3. Honest theorem-slot split for the geometry step

So the later Lean port should separate the geometry package into two possible
routes.

#### Route A: stronger forward-Jost support theorem

```lean
lemma support_mem_forwardJost_of_adjacent_spacelike
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      x ∈ ForwardJostSet d n hd
```

This route is strongest but also most delicate, because the conclusion is a
statement about all consecutive differences.

#### Route B: direct ET-support theorem on the actual open edge

```lean
lemma support_mem_real_open_edge_of_adjacent_spacelike
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, realEmbed x ∈ ExtendedTube d n)

lemma swap_support_mem_real_open_edge_of_adjacent_spacelike
    ...
```

Route B is closer to the already-proved theorem surface in
`AdjacencyDistributional.lean`, because that file works directly with an open
real edge `V` and ET-support hypotheses.

### 15.4. Recommended route

The later implementation should prefer Route B unless a clean forward-Jost
support theorem is already available under an exact production name. That keeps
the locality proof closer to the actual existing BHW package:

1. choose/open an appropriate real edge `V`,
2. prove the support of `f` and the swapped support of `g` lie in `V`,
3. use the existing ET hypotheses accepted by the pairing theorem,
4. avoid overclaiming global `ForwardJostSet` membership.

This preference should be treated as part of the implementation guidance, not
as a casual remark:

1. **Primary route**: Route B through an explicit real open edge `V` and ET
   support, because that is the theorem surface already consumed by
   `AdjacencyDistributional.lean`.
2. **Fallback route only**: Route A through `ForwardJostSet`, to be used only
   if a clean theorem upgrading the current hypothesis to global forward-Jost
   membership is actually proved under an exact production name.

So if the later Lean port begins without any new geometric breakthrough, it
should start on Route B immediately. It should not spend time trying to rescue
Route A first.

### 15.4.1. Exact Route-B theorem package on the real open edge

Route B should itself be written as a small theorem package, not as the vague
instruction "pick a convenient open edge." The later Lean file should target
something like:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)

lemma real_open_edge_embeds_in_extendedTube
    {V : Set (NPointDomain d n)}
    (hV : ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) :
    ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n

lemma swapped_real_open_edge_embeds_in_extendedTube
    {V : Set (NPointDomain d n)}
    (g : SchwartzNPoint d n)
    (hsuppg : tsupport (g : NPointDomain d n → ℂ) ⊆ V)
    (hV : ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) :
    ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n
```

This is the safest geometry route because it matches the current production
pairing theorem surface in `AdjacencyDistributional.lean` directly:

1. actual open real edge,
2. actual ET embedding of that edge,
3. support inclusion of both test functions into that edge.

### 15.4.2. Exact proof transcript for the primary Route-B geometry package

The later Lean file should implement Route B in the following explicit order.

1. Start from the support hypothesis on the adjacent pair.
2. For each support point `x`, choose a small real neighborhood `V_x` on which
   the same adjacent spacelike inequality remains true by openness of the
   spacelike region.
3. Use compactness of `tsupport f` to extract finitely many such neighborhoods.
4. Define `V := ⋃_{r=1}^N V_{x_r}`.
5. Prove `V` is open and contains `tsupport f`.
6. Prove every point of `V` still lies in the BHW extended tube after real
   embedding.
7. Use the swap hypothesis to prove `tsupport g ⊆ swap(i,j) ⁻¹' V`.
8. Prove that swapped open edge also embeds into the extended tube.
9. Feed those two ET-support statements to the already-proved distributional
   locality theorem.

So the Route-B theorem slots should be read operationally as:

```lean
lemma local_spacelike_open_edge_around_support_point
lemma compact_support_finite_open_edge_cover
lemma finite_open_edge_union_embeds_in_extendedTube
lemma swapped_support_lies_in_swapped_open_edge
lemma swapped_open_edge_embeds_in_extendedTube
theorem raw_boundary_locality_from_primary_open_edge_route
```

This is the actual proof mechanism that makes Route B preferable: it is local,
compact-support-based, and uses openness of the spacelike relation, rather
than a global combinatorial Jost-set upgrade.

### 15.5. Estimated Lean size for the subtlety-aware geometry package

1. Route-A forward-Jost theorem:
   `30-70` lines if true on the current theorem surface,
   possibly more if the theorem surface itself must be strengthened.
2. Route-B open-edge support package:
   `35-80` lines total across the two support lemmas.

The docs should therefore treat Route B as the safer implementation target
until Route A is proved honestly.
