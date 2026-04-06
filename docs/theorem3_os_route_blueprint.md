# Theorem 3 OS-Route Blueprint

Purpose: this note is the implementation blueprint for the live `E -> R`
frontier theorem

- `OSToWightmanBoundaryValues.lean`, private theorem `bvt_W_positive`.

This document is not a historical summary. It is the route specification to be
followed during Lean work. If the code seems to suggest a different route, the
docs must be repaired first and Lean work must pause.

This note should be read together with:

- `docs/os1_detailed_proof_audit.md`
- `docs/os2_detailed_proof_audit.md`
- `docs/mathlib_gap_analysis.md`
- `docs/sorry_triage.md`

## 1. The live theorem and the current production situation

The live theorem is:

```lean
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re
```

The current production files still expose an older reduction chain through
boundary-ray / Schwinger / compact-approximation consumer interfaces. Those
surfaces are part of the current code graph, but they are **not** the theorem-3
blueprint any more. They are legacy consumers.

The theorem-3 blueprint now has exactly one endorsed route:

1. keep Packages A-B as valid one-variable support infrastructure;
2. do **not** use Package C / `hschw`, because that theorem surface is false;
3. build the OS I Section 4.3 transformed-image package:
   positive-time Euclidean data -> dense Minkowski image -> OS Hilbert vector;
4. prove the quadratic identity on that transformed-image core, not on the same
   raw `BorchersSequence d` viewed on both sides;
5. extend positivity to arbitrary `BorchersSequence d` only afterwards, by the
   density/continuity closure supplied by the Section 4.3 image theorem.

That is the route Claude directed in `agents_chat.md`, and it is now the only
route this document endorses.

Implementation discipline:

1. the legacy `hschw` consumer interface may remain in production as deprecated
   dead-end infrastructure, but it is not an endorsed target theorem surface;
2. Package I is now the only endorsed theorem-3 closure route;
3. the old raw same-input theorem slogan for Package I is withdrawn;
4. if future work wants a different production endpoint than Package I, this
   blueprint must be rewritten first.

### 1.1. Exact current local status on that route

The theorem-3 docs must distinguish three things:

1. what the route is in principle,
2. what is already implemented locally in production,
3. what exact theorem is still missing.

As of the current local branch state:

1. Package A is already implemented in
   `OSToWightmanPositivity.lean` as
   `identity_theorem_right_halfplane`;
2. Package B is already implemented there as
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`;
3. Package C / `hschw` has now been settled as false at the exact theorem
   surface; see `agents_chat.md` Entries `#283`, `#285`, `#286`;
4. the later positive-time / compact-approximation consumers still exist in
   `OSToWightmanBoundaryValuesBase.lean`,
   `OSToWightmanBoundaryValuesCompactApprox.lean`, and
   `OSToWightmanBoundaryValues.lean`, but they are legacy consumers rather than
   endorsed theorem-3 route definitions;
5. the live theorem-3 frontier is now the corrected Package-I theorem surface;
6. the older raw theorem slogan
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` for the same raw
   `BorchersSequence d` on both sides is not endorsed and is under
   correction.

So the current frontier is not “find a theorem-3 route.” The route is fixed.
The current frontier is:

1. keep Packages A-B as valid support infrastructure,
2. stop treating Package C as a live theorem to prove,
3. repair Package I to the actual Section 4.3 transformed-image theorem
   surface,
4. only then implement the resulting transport / density / closure package.

## 2. Exact existing theorem hooks already available

The current code already provides the main ingredients for the endorsed route.
The later Lean port should consume these exact theorem surfaces instead of
inventing new theorem shapes.

### 2.1. Holomorphic / boundary-value package

In `OSToWightmanBoundaryValueLimits.lean`:

- `bvt_singleSplit_xiShiftHolomorphicValue`
- `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
- `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
- `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
- `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`

These theorems already package the one-variable holomorphic object attached to a
single/split pair and the relevant `z -> 0+` limit statements.

In `OSToWightmanPositivity.lean`:

- `identity_theorem_right_halfplane`
- `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`

These are the current local production implementations of Packages A and B.
Note that the implemented Package-B theorem currently uses the simpler surface
`OSInnerProductTimeShiftHolomorphicValue` specialized to positive-time singles,
not the broader `...ExpandBoth` wrapper. That is fine and should be treated as
the canonical current production start point.

### 2.2. OS inner-product package

In `SchwingerOS.lean`:

- `PositiveTimeBorchersSequence`
- `PositiveTimeBorchersSequence.single`
- `PositiveTimeBorchersSequence.osInner`
- `PositiveTimeBorchersSequence.osInner_nonneg_self`
- `PositiveTimeBorchersSequence.osInner_eq_sum_right_singles`
- `OSInnerProduct_single_single`
- `OSInnerProduct_right_single`
- `OSInnerProduct_eq_sum_right_singles`
- `OSInnerProduct_zero_right`
- `OSInnerProduct_hermitian`

This is the OS-side algebraic package the theorem-3 proof should use.

### 2.3. Semigroup / time-shift package

In `OSToWightmanSemigroup.lean` and `OSToWightman.lean`:

- `OSInnerProductTimeShiftHolomorphicValue`
- `OSInnerProductTimeShiftHolomorphicValue_differentiableOn`
- `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single`
- `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift`

This is the OS-side holomorphic family to compare against
`bvt_singleSplit_xiShiftHolomorphicValue`.

### 2.4. Compact-approximation package

In `OSToWightmanBoundaryValuesCompactApprox.lean`:

- `compactApproxPositiveTimeBorchers`
- `compactApproxPositiveTimeBorchers_component_compact`
- `tendsto_compactApproxPositiveTimeBorchers_term`
- `tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`

These theorems can still be used as **consumer interfaces** once the direct
positive-time semigroup bridge has been proved. They are not the route
definition.

### 2.5. Continuity package

In `OSToWightmanBoundaryValuesBase.lean` and nearby files:

- `bvt_W_continuous`
- `wightmanInner_eq_osInner_of_orderedPositive_termwise`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right`
- `bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero`
- finite-sum expansions of `WightmanInnerProduct`
- right-single and zero-right reduction lemmas

This is the continuity package already used by the legacy positive-time
consumer chain. It is no longer the endorsed final theorem-3 closure route.

## 3. What the OS papers require here

OS I and OS II both point to the same theorem shape:

1. identify the correct one-variable scalar holomorphic object;
2. prove equality of the Minkowski-side and OS-side scalar functions on the
   right half-plane from equality on positive reals;
3. take the `z -> 0+` limit to recover the boundary pairing identity;
4. sum the single/split identities to obtain equality of quadratic forms on the
   positive-time class;
5. extend positivity to the full Borchers space by the Section 4.3 transport
   map and Hilbert-norm identity.

So the actual theorem-3 content is **not**:

- a contour-deformation theorem,
- a `K2VI1` comparison theorem,
- a new shell wrapper,
- or a raw algebraic-core theorem on `Submodule ℂ (BorchersSequence d)`.

The actual theorem-3 content is:

- positive-time semigroup identity,
- positive-time positivity,
- Section 4.3 transformed-image map to `OSHilbertSpace OS`,
- Hilbert-norm realization of the Wightman quadratic form on that transformed
  image, followed by density/continuity closure.

## 4. Route that is explicitly forbidden

The later Lean implementation must not drift back to any of the following:

1. `hpath` / contour-deformation / boundary-ray route.
2. `hschw` as the **target theorem shape**.
3. k=2-specific common-kernel transport as theorem-3 infrastructure.
4. defining `bvtInitialCore : Submodule ℂ (BorchersSequence d)`.
5. adding ad hoc `AddCommGroup`, `Module ℂ`, or topology instances to raw
   `BorchersSequence d` just to mimic paper notation.
6. inventing any new reduction theorem whose only purpose is to repackage the
   same positivity seam.

Historical note:

- the current production consumer theorem
  `bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
  may still be used after the positive-time semigroup bridge is proved;
- but the proof should **arrive** at that theorem from the positive-time
  semigroup route, not target `hschw` as the mathematical endpoint.

## 5. Corrected theorem package

The theorem-3 proof package should now be implemented in the following order.
This order is mathematical, not merely organizational.

### 5.1. Package A: one-variable identity theorem

The first theorem slot is:

```lean
theorem identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z
```

This theorem is local complex analysis only. It should be proved once and then
reused.

Primary use in theorem 3:

- `f z = bvt_singleSplit_xiShiftHolomorphicValue ... z`
- `g z = OSInnerProductTimeShiftHolomorphicValue ... z`

### 5.2. Package B: compact positive-time single/split bridge

For compactly supported positive-time components, prove the direct one-variable
identity:

```lean
theorem bvt_singleSplit_eq_osTimeShift_on_rightHalfPlane
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hm : 0 < m) :
    ∀ z : ℂ, 0 < z.re →
      bvt_singleSplit_xiShiftHolomorphicValue (d := d) OS lgc hm
        f hf_ord hf_compact g hg_ord hg_compact z
        =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) z
```

Proof transcript:

1. use
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
   and
   `OSInnerProductTimeShiftHolomorphicValue_differentiableOn`;
2. use
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
   for the Wightman-side real-axis formula;
3. use
   `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single`
   specialized to a positive-time single left factor, or equivalently
   the already implemented production theorem
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`;
4. check that both real-axis formulas equal the same positive-real Schwinger
   time-shift expression;
5. apply `identity_theorem_right_halfplane`.

This is the core analytic theorem. Everything after this is algebra and
continuity.

Exact current implementation note:

1. the current local production theorem for Package B is already
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` in
   `OSToWightmanPositivity.lean`;
2. later work should build on that theorem, not reprove Package B under a
   slightly different wrapper unless there is a compelling API reason.

### 5.3. Package C: false legacy theorem surface

Package C is **not** a live frontier any more. It is the old positive-real
same-shell theorem surface externalized as `hschw`, and it is mathematically
false.

The legacy theorem surface was:

```lean
theorem schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift_of_compact_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hm : 0 < m) :
    ∀ t : ℝ, 0 < t →
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
        =
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
```

This is the exact theorem externalized today as the hypothesis `hschw` in
`OSToWightmanBoundaryValueLimits.lean` and
`OSToWightmanBoundaryValuesCompactApprox.lean`.

Exact reason it is false:

1. for the free scalar field, the left-hand side evaluates to a Euclidean/OS
   Laplace-type quantity with factor `e^{-ω_p t}`;
2. the right-hand side evaluates to the reconstructed Wightman boundary-value
   pairing against a real Minkowski time translation, with oscillatory factor
   `e^{-i ω_p t}`;
3. the test functions also appear through different transforms on the two
   sides: Laplace on the OS side, Fourier on the Wightman side;
4. so the two sides do not agree on the exact intended theorem surface.

See `agents_chat.md` Entry `#283` for the exact free-field counterexample and
Entries `#285`-`#286` for the exact-surface verification against the repo
definitions.

Operational consequence:

1. the legacy `hschw` theorems may remain in production as logically valid
   implications from a false premise;
2. they should be marked deprecated/dead-end and not used to guide theorem-3
   proof work;
3. Package I is now the only endorsed theorem-3 route.

### 5.3.1. Existing theorem inventory still relevant after the correction

Existing production infrastructure already supporting this route:

1. `identity_theorem_right_halfplane` in `OSToWightmanPositivity.lean`;
2. `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` in
   `OSToWightmanPositivity.lean`;
3. `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` in
   `OSToWightmanBoundaryValueLimits.lean`;
4. `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   in `OSToWightmanSemigroup.lean`;
5. `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   in `OSToWightmanBoundaryValueLimits.lean`.

Core Wightman-side boundary-value infrastructure already present:

1. `full_analytic_continuation_boundaryValueData`;
2. `boundary_values_tempered`;
3. `bvt_W`;
4. `bvt_F`;
5. `bvt_W_continuous`;
6. `bvt_W_linear`;
7. `bvt_F_holomorphic`;
8. `bvt_boundary_values`.

These are important because the Package-C spectral/Laplace strategy does not
only need the OS-side semigroup object; it also needs the exact theorem surfaces
that realize the reconstructed Wightman pairing as the boundary value of the
forward-tube witness `bvt_F`.

Particularly relevant BV-side spectral/Laplace bridge theorems already in
`OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift`;
2. `bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_translate_spatial_right`;
3. `bvt_OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear_local`;
4. `bvt_OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial_right`.

These remain useful as support infrastructure for the corrected Section 4.3
transport-map route, but they should no longer be read as evidence that the old
same-shell Package-C theorem is true.

Useful transcript guides from older support files:

1. `schwinger_simpleTensor_timeShift_eq_xiShift`;
2. `OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift`;
3. `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift`.

These older theorems are valuable because they already write out the OS-side
positive-real / Euclidean-`xiShift` conversion in detail. They should be used
as proof transcripts, not as reasons to revert to an off-blueprint theorem
surface.

Zero-right and helper transport facts:

1. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian`
   still handles the `m = 0` repair only;
2. `boundary_ray_hermitian_pairing_of_F_negCanonical`,
   `bv_hermiticity_transfer_of_F_reflect`,
   `bv_timeReversal_transfer`,
   `boundary_ray_timeReversal_pairing_of_F_timeReversalCanonical`,
   and `tendsto_boundary_negReverse_pairing`
   remain helper transport theorems only.

They may assist a future proof, but they are not themselves the OS I Section 4.3
Fourier-Laplace mechanism.

### 5.3.2. What this correction means for the codebase

1. do not spend any further theorem-3 effort trying to prove the old
   `schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift` surface;
2. do not revive a same-shell bridge
   `bvt_W (f.conjTensorProduct g) = OS.S (f.osConjTensorProduct g)`;
3. keep Packages A-B as valid support lemmas;
4. treat the current `hschw` consumer theorems as deprecated legacy
   infrastructure only;
5. move directly to Package I.

Exact current handoff theorems after the correction:

1. the `hschw`-consuming compact-approximation theorems remain compiled legacy
   infrastructure but are no longer part of the endorsed route;
2. the live theorem-3 implementation target is now the Section 4.3 transport
   image / quadratic-identity / closure package from Package I;
3. the older theorems
   `bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   and
   `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   remain legacy consumers only and should not drive new theorem-3 production.

### 5.4. Package D: positive-time sesquilinear equality

Now sum the single/split equalities over the right factor and then over the left
factor:

```lean
theorem bvt_wightmanInner_eq_osInner_of_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (G : BorchersSequence d)
      =
    OSInnerProduct d OS.S
      (F : BorchersSequence d) (G : BorchersSequence d)
```

Exact current implementation note:

1. the abstract summation theorem already exists in
   `OSToWightmanBoundaryValuesBase.lean` as
   `wightmanInner_eq_osInner_of_orderedPositive_termwise`;
2. the older compact ordered-positive-time consumer chain also already exists as
   `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   and its zero-right/self variants;
3. therefore Package D does **not** need a fresh mathematical route once
   Package C is proved; it needs a clean adapter from the new Package-C theorem
   to these existing consumers.

Proof transcript if done directly:

1. use `OSInnerProduct_eq_sum_right_singles` and the analogous Wightman-side
   finite-sum expansion;
2. reduce each summand to the single/split theorem from Package C;
3. handle the `m = 0` right-factor summands by the existing zero-right theorems;
4. use hermitian symmetry to move any residual zero-left issues to the already
   documented zero-right theorems rather than introducing a separate left-zero
   package;
5. sum the equalities.

This theorem is the actual OS I style bridge theorem for the positive-time
class.

### 5.5. Package E: positive-time positivity

Once Package D exists, positivity on the positive-time class should be
immediate. Again, the current code already has consumer versions of this
statement through the compact-approximation chain, so the real frontier is still
Package C.

```lean
theorem bvt_positiveTime_self_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re
```

Proof transcript:

1. rewrite by Package D with `G = F`;
2. identify the result with `PositiveTimeBorchersSequence.osInner OS F F`;
3. apply `PositiveTimeBorchersSequence.osInner_nonneg_self`.

This theorem is the end of the analytic core.

### 5.6. Package F: ordered-positive-time density in each degree

Important route correction:

The naive raw-density slogan

```lean
Dense {f : SchwartzNPoint d n |
  tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
```

is not mathematically correct on the full Schwartz space. If
`x ∉ OrderedPositiveTimeRegion d n`, then point evaluation `f ↦ f x` is a
continuous linear functional and it vanishes on every function whose support is
contained in `OrderedPositiveTimeRegion d n`. So that set cannot be dense in
all of `SchwartzNPoint d n`.

Therefore the raw theorem surface originally written in this section is
quarantined and must not be implemented as stated.

This means the older density route is withdrawn, not merely awaiting repair.
The later Lean implementation should not start from a global topology on raw
`BorchersSequence d`, and it should not attempt to resurrect Package F as a
real theorem on full Schwartz space.

Quarantined theorem slots (recorded here only so later work does not
accidentally reintroduce them as if they were valid):

```lean
theorem orderedPositiveTime_dense_schwartzNPoint
    (n : ℕ) :
    Dense
      {f : SchwartzNPoint d n |
        tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

theorem exists_orderedPositiveTime_seq_tendsto
    (n : ℕ) (f : SchwartzNPoint d n) :
    ∃ g : ℕ → SchwartzNPoint d n,
      (∀ k, tsupport (g k : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
        ∧ Tendsto g atTop (𝓝 f)
```

Exact current implementation status:

1. there is **no** current production theorem implementing Package F yet;
2. the existing family `compactApproxPositiveTimeBorchers` in
   `OSToWightmanSpatialMomentum.lean` is **not** Package F:
   it approximates an already positive-time Borchers sequence by compactly
   supported positive-time Borchers sequences, but it does not approximate an
   arbitrary Schwartz component by ordered-positive-time data;
3. this section is retained only as a warning / historical quarantine, not as
   endorsed implementation guidance.

### 5.7. Package G: componentwise positive-time approximation of Borchers sequences

The original Package-G statement depended on the quarantined raw Package-F
statement above. So this section is also historical only, not a currently
endorsed theorem surface.

Recommended theorem slot:

```lean
theorem exists_positiveTime_componentwise_approximation
    (F : BorchersSequence d) :
    ∃ G : ℕ → PositiveTimeBorchersSequence d,
      (∀ n, Tendsto (fun k => ((G k : BorchersSequence d).funcs n)) atTop (𝓝 (F.funcs n)))
        ∧ (∀ k, (G k : BorchersSequence d).bound = F.bound)
```

What remains fixed is only the negative guidance:

1. do not force a raw topological structure on `BorchersSequence d`;
2. do not reintroduce raw support-density claims on full Schwartz space;
3. use Package I instead of trying to revive this approximation route.

Exact current implementation status:

1. there is **no** current production theorem implementing Package G, and none
   is currently endorsed;
2. `compactApproxPositiveTimeBorchers` should be treated only as an internal
   compact-support approximation inside the positive-time class;
3. it is not the final arbitrary-`BorchersSequence` approximation theorem and
   should not be documented or used as if it were.

### 5.8. Package H: withdrawn continuity-after-density route

This section records the old continuity-after-density plan only so it is not
accidentally revived as current blueprint guidance.

Recommended theorem slots:

```lean
theorem WightmanInnerProduct_tendsto_of_componentwise_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d)
    (G : ℕ → BorchersSequence d)
    (hbound : ∀ k, (G k).bound = F.bound)
    (hcomp : ∀ n, Tendsto (fun k => (G k).funcs n) atTop (𝓝 (F.funcs n))) :
    Tendsto
      (fun k => WightmanInnerProduct d (bvt_W OS lgc) (G k) (G k))
      atTop
      (𝓝 (WightmanInnerProduct d (bvt_W OS lgc) F F))

theorem re_WightmanInnerProduct_tendsto_of_componentwise_tendsto
    ...
```

Proof transcript:

1. expand `WightmanInnerProduct` as a finite double sum up to `F.bound`;
2. for each fixed pair `(n,m)`, use `bvt_W_continuous` and the product
   convergence of the component approximants;
3. move the limit through the finite sum.

This is where the route uses the finite-support nature of `BorchersSequence d`
instead of forcing a global topological structure.

Acceptable implementation helper:

1. if the eventual Lean code wants a helper theorem phrased as continuity of
   the real quadratic form on a **fixed-bound product space**
   `(n : Fin (B + 1)) → SchwartzNPoint d n`, that is acceptable;
2. such a theorem is still only a repackaging of the finite-sum argument above,
   because the bound `B` is fixed and the quadratic form expands to a finite
   double sum of already-continuous pairings;
3. what should still be avoided is restarting theorem 3 from a new global
   topological structure on raw `BorchersSequence d` itself.

Exact current implementation status:

1. the repo already contains a concrete model of this continuity argument for
   one specific approximation family:
   `tendsto_compactApproxPositiveTimeBorchers_term` and
   `tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self` in
   `OSToWightmanBoundaryValuesCompactApprox.lean`;
2. these theorems show that the finite-sum continuity route is formally viable
   on the current encoding of `BorchersSequence d`;
3. however, they are still only special-case continuity theorems for the
   compact-support truncation family, not the final general Package-H theorem.

### 5.9. Package I: final public closure via the OS I Section 4.3 transformed-image package

After the density-route correction, the final theorem-3 closure package is no
longer the withdrawn raw positive-time approximation theorem. But it is also
not the naive raw theorem

`(WightmanInnerProduct d (bvt_W OS lgc) F F).re = ‖u(F)‖ ^ 2`

for the same raw `BorchersSequence d` on both sides.

OS I Section 4.3 itself first constructs a dense positive-energy Schwartz image
`L` of transformed positive-time Euclidean test functions (Lemma 4.1), then
defines `u` on that image (Eq. (4.27)), and then proves the quadratic identity
there (Eq. (4.28)). Only afterwards does one recover the full public
positivity statement by density/continuity.

Just as importantly, the naive same-test-function identity is false even at
`t = 0`: one must transport Euclidean test functions on the Laplace side to the
positive-energy Minkowski test-function side before the Wightman quadratic form
matches the OS Hilbert norm.

So the old raw theorem slots are withdrawn. The corrected theorem slots are:

```lean
/-- The degree-`n` positive-time Euclidean domain used in OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. If the eventual
Lean implementation prefers an equivalent `Submodule ℂ (SchwartzNPoint d n)`
presentation rather than a subtype, that is acceptable, but it must represent
the same paper domain. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- The degree-`n` positive-energy Schwartz codomain from OS I Lemma 4.1.

This is not the full unrestricted Minkowski Schwartz space. It is the
positive-energy Schwartz-side space that the Section 4.3 Fourier-Laplace map
lands in after the Lemma-8.2 reduction. A Lean implementation may realize this
as a subtype, quotient, or equivalent closed subspace of `SchwartzNPoint d n`,
but it must represent the paper's positive-energy codomain rather than all of
`S(ℝ^{4n})`. -/
def PositiveEnergySchwartzComponent (d n : ℕ) [NeZero d] := ...

/-- The degree-`n` Section 4.3 Fourier-Laplace transport
(OS I (4.19)-(4.20), with the corrected codomain reading from Lemma 4.1). -/
noncomputable def os1TransportComponent
    (d n : ℕ) [NeZero d] :
    EuclideanPositiveTimeComponent d n →L[ℂ] PositiveEnergySchwartzComponent d n

/-- The degree-`n` Section 4.3 transformed positive-energy image. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (PositiveEnergySchwartzComponent d n) :=
  Set.range (os1TransportComponent d n)

/-- Additive closure of the Section 4.3 image. -/
theorem bvtTransportImage_add
    {n : ℕ} {f g : PositiveEnergySchwartzComponent d n} :
    f ∈ bvtTransportImage (d := d) n →
    g ∈ bvtTransportImage (d := d) n →
    f + g ∈ bvtTransportImage (d := d) n

/-- Scalar closure of the Section 4.3 image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ} {f : PositiveEnergySchwartzComponent d n} :
    f ∈ bvtTransportImage (d := d) n →
    c • f ∈ bvtTransportImage (d := d) n

/-- OS I Lemma 4.1: dense range of the degree-`n` transport component. -/
theorem os1TransportComponent_denseRange
    (n : ℕ) :
    DenseRange (os1TransportComponent d n)

/-- The Section 4.3 image is dense in the positive-energy Schwartz codomain. -/
theorem bvtTransportImage_dense
    (n : ℕ) :
    Dense (bvtTransportImage (d := d) n)

/-- Finite Borchers data whose every component lies in the Section 4.3 image. -/
def BvtTransportImageSequence (d : ℕ) [NeZero d] := ...

/-- Degreewise approximation of a bounded public Borchers sequence by
transformed-image sequences with the same finite support bound. -/
theorem exists_componentwise_transportImage_approx
    (F : BorchersSequence d) :
    ∃ Gseq : ℕ → BvtTransportImageSequence d,
      (∀ N, (Gseq N).1.bound ≤ F.bound) ∧
      ∀ n, Tendsto
          (fun N => (((Gseq N).1.funcs n : PositiveEnergySchwartzComponent d n) :
            SchwartzNPoint d n)) atTop
          (nhds (F.funcs n))

/-- The OS I Section 4.3 transport map on the transformed-image core. -/
noncomputable def bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    BvtTransportImageSequence d → OSHilbertSpace OS

/-- The transport map is independent of the Section 4.3 preimage choice. -/
theorem bvt_transport_to_osHilbert_onImage_wellDefined
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) :
    ...

/-- Additivity on the transformed-image core. -/
theorem bvt_transport_to_osHilbert_onImage_add
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage (d := d) OS lgc (F + G) =
      bvt_transport_to_osHilbert_onImage (d := d) OS lgc F +
      bvt_transport_to_osHilbert_onImage (d := d) OS lgc G

/-- Complex-linearity on the transformed-image core. -/
theorem bvt_transport_to_osHilbert_onImage_smul
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (c : ℂ) (F : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage (d := d) OS lgc (c • F) =
      c • bvt_transport_to_osHilbert_onImage (d := d) OS lgc F

/-- OS I Eq. (4.28) on the transformed-image core. -/
theorem bvt_wightmanInner_eq_transport_norm_sq_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.1 F.1).re =
      ‖bvt_transport_to_osHilbert_onImage (d := d) OS lgc F‖ ^ 2

/-- Final public theorem-3 closure by density/continuity from the transformed
image core. -/
theorem bvt_W_positive_of_transportImage_density
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re
```

Proof transcript:

1. define the degreewise transformed image `bvtTransportImage` exactly as in OS
   I Lemma 4.1, i.e. literally as the range of
   `os1TransportComponent d n`;
2. prove dense range of `os1TransportComponent d n` in the positive-energy
   Schwartz codomain (the actual density content of OS I Lemma 4.1);
3. do **not** implement `os1TransportComponent` as the naive unrestricted
   real-axis Laplace integral by itself; the paper route factors through the
   intermediate `(4.19)` space and Lemma 8.2, and that is exactly what keeps
   the codomain on the positive-energy Schwartz side rather than drifting to a
   tempered-only theorem surface or the full unrestricted Schwartz space;
4. derive additive/scalar closure of the image from linearity of
   `os1TransportComponent`;
5. package finite-support sequences in that image as
   `BvtTransportImageSequence d`;
6. define `bvt_transport_to_osHilbert_onImage` by the Section 4.3 preimage map
   followed by the existing OS Hilbert-space construction;
7. prove preimage-independence / well-definedness using the zero-kernel part of
   OS I Lemma 4.1;
8. prove `bvt_wightmanInner_eq_transport_norm_sq_onImage` by the Section 4.3
   Fourier-Laplace / spectral-integral computation on the transformed-image
   core;
9. turn that degreewise dense-range statement into
   `exists_componentwise_transportImage_approx` for arbitrary bounded public
   `BorchersSequence d`, using the inclusion of the positive-energy Schwartz
   codomain into the ambient `SchwartzNPoint d n`;
10. extend positivity from transformed-image sequences to arbitrary public
   `BorchersSequence d` by finite-sum continuity of `WightmanInnerProduct`.

This package is the actual theorem-3 closure target.

Exact current implementation status:

1. there is no current production theorem implementing Package I yet;
2. the current production file `OSToWightmanPositivity.lean` now honestly
   isolates Package I as one of the two remaining `sorry`s;
3. the old raw same-input theorem slogan is withdrawn and must not be
   implemented literally;
4. the theorem-3 blueprint now endorses only the transformed-image /
   density-closure reading of Section 4.3.

## 6. Exact relation to the current production consumers

The current legacy consumers can remain compiled, but they are not part of the
endorsed closure route.

Safe usage:

1. mine the current codebase only for reusable continuity / completion /
   positive-time Hilbert-space facts;
2. keep the deprecated `hschw` consumer chain compiled but untouched;
3. if a legacy theorem becomes useful later, re-justify it from the corrected
   transformed-image Package-I route rather than treating it as an input.

Unsafe usage:

1. introducing a new theorem whose primary conclusion is another `h*` consumer
   interface;
2. reentering the K2 common-kernel route;
3. implementing the old raw Package-I theorem surface on the same
   `BorchersSequence d` input without first fixing the transformed-image
   statement.

## 7. Minimal Lean pseudocode for the endorsed route

The later Lean implementation should use the following theorem-package names
unless an exact compile failure forces a local renaming. In that case the docs
must be updated at the same time; the names below are now part of the intended
implementation contract, not casual pseudocode.

```lean
/- Step A: one-variable identity theorem. -/
theorem identity_theorem_right_halfplane ... := by
  ...

/- Step B: compact positive-time single/split equality on {Re z > 0}. -/
theorem bvt_xiShift_eq_osInnerProduct_holomorphicValue_single ... := by
  apply identity_theorem_right_halfplane
  ...

/- Step C: z -> 0+ boundary pairing equality for compact single/split data. -/
theorem schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift ... := by
  ...

/- Step D: sum over components to get positive-time sesquilinear equality. -/
theorem bvt_wightmanInner_eq_osInner_of_positiveTime ... := by
  ...

/- Step E: positivity on the positive-time class. -/
theorem bvt_positiveTime_self_nonneg_from_packageC ... := by
  ...

/- Step F: withdrawn raw density route (historical, do not implement). -/
theorem orderedPositiveTime_dense_schwartzNPoint ... := by
  ...

theorem exists_orderedPositiveTime_seq_tendsto ... := by
  ...

/- Step G: withdrawn approximation bundling route (historical, do not implement). -/
theorem exists_positiveTime_componentwise_approximation ... := by
  ...

/- Step H: withdrawn continuity-after-density route (historical, do not implement). -/
theorem WightmanInnerProduct_tendsto_of_componentwise_tendsto ... := by
  ...

theorem re_WightmanInnerProduct_tendsto_of_componentwise_tendsto ... := by
  ...

/- Step I: final theorem-3 closure via Section 4.3 transformed image. -/
def bvtTransportImage ... := by
  ...

theorem bvtTransportImage_dense ... := by
  ...

def BvtTransportImageSequence ... := by
  ...

noncomputable def bvt_transport_to_osHilbert_onImage ... := by
  ...

theorem bvt_wightmanInner_eq_transport_norm_sq_onImage ... := by
  ...

theorem bvt_W_positive_of_transportImage_density ... := by
  ...
```

The current production file
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
already uses the exact names
`identity_theorem_right_halfplane`,
`bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`,
`schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift`,
and `bvt_positiveTime_self_nonneg_from_packageC`.
The transformed-image theorem names above should therefore be treated as the new
fixed guidance for the corrected Section 4.3 closure package. The older raw
same-input Package-I names are withdrawn.

## 8. Representation-gap note

The theorem-3 route above is the current-code realization of the OS proof.

The docs therefore record the following explicitly:

1. raw `BorchersSequence d` is a bounded finite-record representation;
2. this representation is enough for theorem 3 because
   `WightmanInnerProduct` is a finite sum;
3. therefore theorem 3 should be closed by the Section 4.3 transport-map
   realization, not by first imposing a `Submodule` / topology package on the
   raw type.

This is a local repo encoding fact, not a mathematical change to the OS route.

## 9. Support-work checklist

Before any later production proof resumes, the support work should verify:

1. no theorem-3 doc section still treats `hschw` as the target theorem shape;
2. no theorem-3 doc section still recommends `bvtInitialCore` on raw
   `BorchersSequence d`;
3. `mathlib_gap_analysis.md` classifies the raw `BorchersSequence` issue as a
   local representation gap, not an upstream gap;
4. any new test-file support work stays inside Package A through Package I
   above, and does not revive the withdrawn F/G/H density route as if it were
   endorsed.
5. the docs identify the exact current local frontier as the corrected
   transformed-image Package-I theorem surface, not as a generic
   “boundary-value limit”.
6. the docs explicitly record that Packages A-B are already implemented in
   `OSToWightmanPositivity.lean`;
7. no theorem-3 doc section still states the naive raw theorem
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` on the same raw public
   `BorchersSequence d` input as if it were already the correct Section 4.3
   theorem surface.

## 10. Bottom line

Theorem 3 is no longer a shell-comparison project.

Theorem 3 is now exactly this:

1. prove the positive-time semigroup bridge;
2. prove positivity on `PositiveTimeBorchersSequence d`;
3. define the Section 4.3 transformed Minkowski image and its OS Hilbert-space
   transport map;
4. identify the Wightman quadratic form with a Hilbert norm square on that
   transformed-image core;
5. extend positivity from the transformed-image core to arbitrary
   `BorchersSequence d` by density/continuity.

That is the only theorem-3 route this note now endorses.
