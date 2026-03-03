# d=1, n=2 Blocker Audit

## Active Blocker
- `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`

This asks for swap-difference vanishing of the invariant kernel on the doubly light-cone-witnessed quadric locus.

## What Has Been Proven Around It
- Invariant factorization machinery on `FT_{1,2}` is present.
- Realizable/light-cone/forwardizable equivalences are present.
- Reduction from blocker to paired-chart anchor connectivity is present.

## Failed Attempts (Documented)

### 1. EOW/open-anchor closure for d=1
Status: rejected for this blocker path.

Reason:
- The d=1 geometry constraints make the direct real-anchor EOW strategy nonproductive for the required invariant-only closure.

### 2. Full-quadric involution from source package alone
Status: false in general.

Formal counterexample exists:
- `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`.

Meaning:
- source constraints determine values on realizable image, but do not force arbitrary off-image values of an auxiliary `f` on the whole quadric.

### 3. Fixed-anchor chart route (`v0=i`, etc.)
Status: too rigid / not adopted.

Reason:
- insufficient flexibility for the paired realizability needed by the blocker domain.

## Counterexample/Obstruction Summary
- Off-image freedom of `f` prevents deriving global quadric involution from source data alone.
- Therefore the proof must stay on the doubly witnessed/relevant locus and propagate there.

## Accepted Remaining Gap
The unproved step is:
- derive paired-chart anchor connectivity for the sourced field from the source package.

Once this is shown, the blocker closes by existing reduction lemmas.

## Sanity Constraints
- Keep statements mathematically true on their declared domains.
- Avoid strengthening conclusions beyond realizable/light-cone witness hypotheses unless new hypotheses are explicitly added.
