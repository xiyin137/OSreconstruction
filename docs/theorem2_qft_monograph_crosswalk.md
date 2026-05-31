# Theorem 2: QFT Monograph OSR Crosswalk

Source inspected:

```text
/Users/xiyin/QFT/monograph/tex/volumes/volume_iv/chapter02_osterwalder_schrader_reconstruction.tex
references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf
```

Relevant monograph proof nodes:

- `Definition~\ref{def:os-lorentzian-boundary-value-package}` separates the
  OS-II analytic payload into holomorphic forward-tube functions, polynomial
  tempered boundary estimates, and permuted-tube/Jost edge-of-the-wedge
  continuation.
- `Proposition~\ref{prop:os-ii-analytic-route-to-boundary-package}` says the
  OS-II `A_N/P_N` continuation plus growth package supplies those boundary
  values.
- `Proposition~\ref{prop:os-boundary-package-consequences}`, part (b), is the
  theorem-2 locality step: in reduced difference variables, the Jost/EOW
  equality is first proved on the mixed analytic edge and then passed to
  boundary distributions; compact smearing is handled afterward.

2026-05-30 current leaf:

- The relevant monograph proof body is part (b), lines 1356-1374 of the local
  reference copy: Jost real edges, equality of the two holomorphic functions by
  Euclidean permutation symmetry plus the identity theorem, distributional EOW,
  then partition-of-unity smearing over Jost neighborhoods.
- In Lean, the next non-wrapper input should be the Wick-section compact-test
  transport for the deterministic adjacent branch:

```lean
∀ φ : SchwartzNPoint d n,
  HasCompactSupport (φ : NPointDomain d n → ℂ) →
  tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
  ∫ u : NPointDomain d n,
    extendF (bvt_F OS lgc n)
      (permAct P.τ (fun k => wickRotatePoint (u k))) * φ u =
  ∫ u : NPointDomain d n,
    bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u
```

- This is the proof body consumed by
  `BHW.os45CommonEdge_sourceRepresentsZero_of_initialOverlap_adjacentBranch`.
  The source-side zero representation remains the paper-facing Path-2 input;
  `Hdiff` is the Lean envelope, and the reduced sign-flip form is downstream
  bookkeeping.

2026-05-30 Claude recommendation reconciliation:

- Route A through `AdjacentReducedRuelleDistributionalLimit` is formally
  legacy/diagnostic for theorem 2.  It must not be used as the active producer
  when supplied through `BHW.localSPrime_twoSectorBranch_of_EOW_BHW`.
- The active monograph node is Proposition
  `os-boundary-package-consequences` part (b): Jost real-edge equality,
  distributional EOW, then compact smearing by Jost-neighborhood partition.
- The Lean chain after the current leaf is already present:

```text
finite-height source-side branch/current transport
  -> D.zeroHeightPairing_of_tendsto_sourceSide_extendF_difference_zero
  -> os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM_overlapConnected
  -> os45CommonEdge_transported_wick_pairing_of_compactFigure24WickPairingEq
  -> os45CommonEdge_sourceRepresentsZero_of_compactFigure24WickPairingEq
```

- Therefore the remaining non-wrapper lemma is not another input gate.  It is
  the OS-I `(4.12)`-`(4.14)` finite-height Wick-section transport that compares
  the actual branch integrals

```lean
∫ u,
  extendF (bvt_F OS lgc n)
    (os45FlatCommonChartSourceSide d n 1 1 ε η u) *
    D.toSideZeroDiagonalCLM 1 1 ε η φ u
```

  and the adjacent `-` analogue with the OS source-current integrals already
  controlled by

```lean
BHW.OS45Figure24SourceCutoffData
  .sourceSide_ordinaryPlus_adjacentMinus_difference_tendsto_zero
```

  Once that finite-height branch/current comparison is proved, the existing
  reverse endpoint theorem supplies the zero-height common-edge pairings.

2026-05-30 endpoint audit after the Claude recommendation:

- Checked local scratch
  `test/proofideas_os45_source_branch_current_transport.lean` with:

```lean
BHW.proofideas_branch_current_transport_iff_zeroHeight_schwinger
```

- The theorem proves that, once the neutral moving-test endpoint limits are
  available, the ordinary `+` and adjacent `-` finite-height branch/current
  transport limits are equivalent to the two zero-height common-edge branch
  pairings being equal to the Schwinger CLM:

```text
finite-height branch/current comparison
  <-> zero-height flat common-edge pairing = OS.S on both sides
```

- This rules out the endpoint/DCT shortcut as a theorem-2 producer.  The
  remaining mathematical body is exactly the monograph part-(b) Jost/EOW
  common-boundary statement that identifies the flat common real edge with the
  Wick/Schwinger boundary distribution before smearing.  Producing more
  Path-2 input gates would not shrink this leaf.

Lean map, updated after the Path 2 source-transfer audit:

- The active theorem-2 algebra is now:

```lean
local source-side common-edge zero representation
  -> local moving-source Hdiff / horizontal branch-difference carrier
  -> reduced-normal sign-flip bookkeeping
  -> ReducedLocalAdjacentBoundaryCLMInvariant
  -> ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
  -> bvt_W_swap_pairing_of_spacelike
```

- The older Route A through `AdjacentReducedRuelleDistributionalLimit` is now a
  diagnostic/regression route only.  It should not be used as the theorem-2
  producer because it can pull the old `BHW.localSPrime_twoSectorBranch_of_EOW_BHW`
  trust boundary downstream.

- The paper-facing Path 2 input is the local source-side common-edge branch
  transfer, formalized in Lean as a zero distributional representation:

```lean
SCV.RepresentsDistributionOn
  (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
  (fun u =>
    adjacentPulledRealBranch u - ordinaryPulledRealBranch u) U
```

  `Hdiff` is the Lean transport envelope after this source transfer is proved.
  The reduced sign-flip statement is downstream reduced-normal bookkeeping, not
  the OS-paper-facing input.

- The most faithful consumed Lean target remains the local boundary-CLM
  invariant already consumed by:

```lean
reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_reducedBoundaryCLMInvariant
```

Namely, for compact reduced Schwartz tests supported in the selected adjacent
spacelike edge:

```lean
bvt_reducedWightmanCLM χ m
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE m (Equiv.swap i j)) φ)
  =
bvt_reducedWightmanCLM χ m φ
```

Why this helps:

- The monograph confirms that the finite local-envelope/Figure-2-4 route is not
  the full theorem-2 producer for arbitrary adjacent-spacelike support.
- It points to the Jost p.83--84 mixed-tube proof: keep the selected adjacent
  difference real spacelike, keep the other difference variables in the forward
  tube, prove equality of the two holomorphic representatives there, then take
  the tempered distributional boundary value.
- This is exactly stronger than the current forward-Jost/PET support theorem,
  and exactly weaker than any false claim that the whole real adjacent
  spacelike edge lies in PET.

Smallest non-wrapper Lean leaves suggested by the monograph:

1. A mixed-tube adjacent-transposition equality theorem for reduced variables:
   selected adjacent difference real spacelike, all other differences in the
   ordered tube, equality of the canonical and adjacent-swapped holomorphic
   representatives.
2. A boundary-value passage theorem: mixed-tube equality plus polynomial tube
   bounds implies the reduced boundary-CLM invariant on compact tests supported
   in `reducedSpacelikeSwapEdge`.
3. A local finite-cover/partition step only if the boundary theorem is stated
   locally. This must cover the compact support by neighborhoods where the
   mixed-tube theorem applies; it must not replace the mixed-tube theorem.

Circularity guard:

- Do not prove the boundary-CLM invariant from `bvt_W_swap_pairing_of_spacelike`
  or from any public locality theorem. That would feed theorem 2 into itself.
- Do not route through pointwise real PET membership of
  `reducedSpacelikeSwapEdge`; the monograph and Jost argument use a mixed
  boundary-value theorem instead.

## Jost/PCT Cross-Check

The PCT book reference supports the same theorem shape.

- Chapter 2, Theorem 2-12 characterizes real Jost points of the extended tube:
  all nonzero positive linear combinations of the difference variables are
  spacelike.
- Immediately after that theorem, the book notes that Jost points form a real
  environment and introduces permuted extended tubes.  Around Figure 2-4 it
  constructs a common real Jost environment for an adjacent transposition.  This
  is the local edge used to start the EOW/Jost comparison.
- Chapter 2, Theorem 2-16 is the distributional edge-of-the-wedge theorem: if
  the two holomorphic wedges have the same compact-test distributional boundary
  value on the real edge, the analytic continuations glue.
- Chapter 2, Theorem 2-17 is the uniqueness corollary: a holomorphic function
  whose distributional boundary value is zero on a real environment vanishes in
  the wedge.
- Chapter 4, Theorem 4-1 is the global nature of local commutativity.  It is the
  warning against proving arbitrary spacelike locality by falsely declaring
  every adjacent-spacelike point to be a Jost point.  The proof propagates from
  a Jost/common-real-environment statement to all spacelike separations by the
  standard analytic continuation/Ruelle argument.

Lean consequence:

- A pointwise PET/Jost support theorem is a sufficient special case but not the
  theorem-2 producer.
- The faithful producer is a Ruelle/Jost distributional theorem whose output is
  local reduced boundary-CLM invariance, or equivalently local vanishing of the
  adjacent-after-swap minus canonical reduced boundary distribution.
- The theorem should cite Jost/PCT Theorems 2-12, 2-16, 2-17 and the Chapter 4
  local-commutativity propagation theorem, plus OS I §4.5 and OS II IV.2.

## Current Lean-Ready Seam (2026-05-27)

Fresh checks confirm the frontier:

- `OSToWightmanBoundaryValues.lean` exits 0 with the known theorem-2 locality
  `sorry` and the separate cluster `sorry`.
- `OSToWightman.lean` exits 0 with the known
  `exists_acrOne_productTensor_witness` `sorry`.
- `OSToWightmanReducedForwardJostRuelle.lean` and
  `test/proofideas_reduced_boundary_clm_invariance.lean` exit 0.

The theorem-2 production seam should be the reduced boundary-distribution
invariant, not an all-real-point boundary-value assertion.  The exact theorem
surface consumed by production is:

```lean
∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
  (φ : SchwartzNPoint d m),
  HasCompactSupport (φ : NPointDomain d m → ℂ) →
  Function.support (φ : NPointDomain d m → ℂ) ⊆
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
  bvt_reducedWightmanCLM (d := d) OS lgc χ m
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realPermOnReducedDiffCLE (d := d) m
          (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
    bvt_reducedWightmanCLM (d := d) OS lgc χ m φ
```

This is exactly the `hinv` input of
`reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_boundaryCLM_invariant`.
Once the local invariant is proved, the already-checked chain closes theorem-2
adjacent locality through
`bvt_W_swap_pairing_of_spacelike_from_closedSupportCanonicalInvariant`.

Do not replace this step by an unconditional
`AdjacentReducedRuelleDistributionalLimit` producer.  That route is retained as
a checked consumer/diagnostic path, not as the current axiom-light theorem-2
closure.  The current Path 2 input is the source-side common-edge zero
representation above; any `Hdiff` or sign-flip form should be introduced only
as a direct consumer of that representation.

The recently checked pointwise reduced-edge consumers remain useful only as
sufficient reductions for settings where pointwise boundary limits are actually
available.  They should not replace the book proof for arbitrary compact
spacelike support: the monograph's proof first obtains equality of tempered
boundary distributions on Jost neighborhoods and only then smears and glues by
partition of unity.  Treating every point of `reducedSpacelikeSwapEdge` as
having a pointwise boundary value would be stronger than the classical
argument and is not the route to the live production `sorry`.

## Current Scratch Bridge (2026-05-27)

Checked scratch:

```text
test/proofideas_theorem2_local_reduced_clm_invariant.lean
lake env lean -DmaxHeartbeats=1200000 test/proofideas_theorem2_local_reduced_clm_invariant.lean
# exit 0
```

This file proved the downstream assembly for the older diagnostic formulation:

```lean
ProofIdeas.LocalReducedAdjacentBoundaryCLMInvariant OS lgc χ
  -> local adjacent-after-swap boundary packet
  -> bvt_W adjacent-swap locality
```

The scratch should remain diagnostic, not a production wrapper.  The real
mathematical leaf has since been sharpened: prove the local reduced
branch-difference/sign-flip input on adjacent spacelike collars, feed it to
`ReducedLocalAdjacentBoundaryCLMInvariant`, and then use the checked
closed-support reduced boundary route.  The current Gemini Deep Research sanity
check for the older mixed-tube theorem shape is:

```text
v1_ChdZcVVYYXRMMkM3NmFfdU1QcmNITnNBNBIXWXFVWGF0TDJDNzZhX3VNUHJjSE5zQTQ
```
