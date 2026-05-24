# E-to-R OS-II Payload Closure Plan

Status: active proof plan, 2026-05-22.

This note is the current detailed plan for closing the surviving direct
E-to-R `sorry`:

```lean
exists_acrOne_productTensor_witness
```

in
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean`.

It is deliberately narrower than `docs/general_k_continuation_blueprint.md`.
The purpose here is to drive the next Lean edits, not to archive every older
route attempt.

## Literature Anchors

Use these as binding route constraints.

1. OS I Section 4.1 constructs the OS Hilbert space, the positive
   self-adjoint time generator, and the holomorphic semigroup.  The real
   distribution identity is `(4.1)`; the one-variable semigroup continuation is
   `(4.10)`--`(4.12)`.
2. OS II Section IV.2 states the repaired E-to-R theorem.  The initial
   continuation is Theorem 4.1 `(A_0)`, and the full continuation/growth
   theorem is Theorem 4.3.
3. OS II Chapter V is continuation only.  The paper explicitly does not use the
   linear growth condition there.  The key local step is Chapter V.1:
   semigroup continuations in finitely many dual-cone directions, glued by
   Malgrange-Zerner, with the quantitative polydisc of Lemma 5.1.
4. OS II Chapter V.2 is the `(A_N)/(P_N)` ladder.  The base `(A_0) -> (P_0)`
   step is not a slogan: it upgrades a distributional real-slice scalar-product
   formula to a pointwise scalar-product formula by positive-time
   delta-smearing and passage to the limit.
5. OS II Chapter VI is growth.  The linear growth condition `E0'`, represented
   in Lean by `OSLinearGrowthCondition`, belongs here, not in the bare
   continuation theorem.  The current `exists_acrOne_productTensor_witness`
   includes a polynomial bound, so its final proof must combine the Chapter V
   witness with the Chapter VI bound.
6. OS II points to Vladimirov for the final Fourier-Laplace boundary-value
   extraction.  That is downstream of this `ACR(1)` payload; it must not be
   used to manufacture the payload itself.

The local resources used for this plan are:

```text
references/Reconstruction theorem I.pdf
references/reconstruction theorem II.pdf
references/general-theory-of-quantized-fields.pdf
references/rudin_edge_of_wedge.pdf
docs/os2_detailed_proof_audit.md
docs/general_k_continuation_blueprint.md
test/proofideas_acr_one_product_tensor_witness.lean
```

No new outside download was needed for this slice: the OS papers and the local
Jost/Rudin references are already present.

## Lean Target

The direct theorem currently asks for:

```lean
∃ S_prod,
  DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1) ∧
  product_tensor_reproduction ∧
  permutation_invariance ∧
  common_complex_translation_invariance ∧
  canonical_reflection_reality ∧
  polynomial_growth_on_ACR1
```

The checked downstream substrate is already in place:

1. `test/proofideas_acr_one_product_tensor_witness.lean` proves that an
   `ACROneProductTensorPayload` packages exactly this theorem surface.
2. `OSToWightmanBase.lean` has the Osgood/Hartogs flat-slice bridge:
   `differentiableOn_flatPositiveTimeDiffReal_of_slices` and
   `differentiableOn_acrOne_of_flat_slices`.
3. `OSToWightmanACRKernelPackage.lean` has the real-section sorting and
   polynomial kernel packaging from an ACR(1) witness with growth.
4. `OSToWightman.lean` has the dense extension from admissible product tensors
   to all `ZeroDiagonalSchwartz`.

Therefore the missing producer is not the density extension, the Euclidean
kernel packaging, or the flat-coordinate Osgood bridge.  It is the OS-II
Chapter V/VI construction of the payload.

## Deep Research Cross-Check

Pinned API-backed Deep Research interaction
`v1_ChdzQ29RYXB1a05zZUR2ZElQLXRydjBBSRIXc0NvUWFwdWtOc2VEdmRJUC10cnYwQUk`
completed on 2026-05-22.  Its route verdict agrees with the chapter split
above and sharpens the immediate priority:

1. do not prove the W4/E-to-R payload as one bundled induction;
2. split analyticity/properties from growth, following OS II Chapters V and VI;
3. the next major theorem package is OS II Lemma 5.1: the local
   Malgrange-Zerner polydisc from directional semigroup continuations;
4. Chapter VI growth should wait until the Chapter V local/domain package is in
   hand.

The delta-smearing bridge remains necessary for `(A_0) -> (P_0)`, but it is
not the next major obstruction once the one-variable semigroup machinery is
available.

A second API-backed Deep Research interaction
`v1_ChdtRW9RYXY2eElOYXFuc0VQM3NxWjJRdxIXbUVvUWF2NnhJTmFxbnNFUDNzcVoyUXc`
completed on 2026-05-22 and was saved to
`/tmp/osr_gemini_mz_report.md`.  Its useful route check is stricter about the
remaining analytic seam:

1. the flat-tube carriers are genuinely degenerate/non-open, so Osgood and
   ordinary open-cover gluing cannot replace Malgrange-Zerner;
2. the Lean route should scalarize the distribution-valued branches first,
   prove a scalar local MZ theorem, and then reassemble the CLM;
3. real-edge compatibility must be weak/scalarized agreement with the same
   Schwinger distribution, not pointwise equality of singular boundary values;
4. an explicit iterated-Cauchy/polydisc exhaustion proof is the faithful
   neutral SCV substrate if a new MZ theorem has to be developed.

This confirms that the next theorem-surface work should be the scalar local MZ
theorem with concrete flat-tube boundary-value hypotheses, not another wrapper
around the final ACR witness.

## Required Producer Packets

### Packet A: OS I Real Semigroup Scalar Product

Lean role: produce the real positive-time scalar-product formula before any
SCV gluing.

Expected theorem shape:

```lean
theorem osii_real_slice_product_tensor_semigroup_formula
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (fs : Fin k -> SchwartzSpacetime d)
    (hvanish : VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.productTensor fs)) :
    real_slice_scalar OS k fs hvanish =
      os_semigroup_scalar_product OS k fs := ...
```

Implementation notes:

1. It must be proved from the OS Hilbert-space construction and
   `OSInnerProduct_single_single`, not from `bvt_F`.
2. It may use the existing OS semigroup files:
   `OSToWightmanSemigroup.lean`, `OSToWightmanPositivity.lean`, and the
   Section 4.3 Fourier-Laplace carrier files.
3. The theorem must be real-slice only.  It should not mention
   `AnalyticContinuationRegion`.

### Packet B: Positive-Time Delta Smearing

Lean role: turn the distributional scalar-product identity into pointwise
product-tensor reproduction on the real positive-time slice.

Expected theorem slots:

```lean
theorem positive_time_delta_family_exists
theorem delta_smearing_recovers_continuous_value
theorem scalar_distribution_identity_stable_under_smearing
theorem base_step_pointwise_product_tensor_identity
```

Implementation notes:

1. Start in `test/proofideas_osii_delta_smearing.lean`.
2. The first checked lemma should be the neutral analysis fact:
   a normalized nonnegative compactly supported Schwartz sequence whose support
   shrinks to `0` recovers a continuous function value by translation.
3. Then specialize it to positive-time supports.  The repository already has
   one-point positive/negative approximate identities in
   `OSToWightmanK2BaseStep.lean`; the general-k version should use the same
   `ContDiffBump` normalization discipline, not an abstract Dirac delta.

### Packet C: Lemma 5.1 / Malgrange-Zerner Local Continuation

Lean role: produce the local complex representative from directional
semigroup continuations.

Expected theorem slots:

```lean
theorem cone_angle_from_positive_time
theorem dual_cone_basis_exists
theorem directional_semigroup_continuation
theorem malgrange_zerner_glue_directional_pieces
theorem local_polydisc_extension_from_A0_and_lemma51
```

Implementation notes:

1. This packet must follow OS II `(5.5)`--`(5.14)`:
   rotate each dual-cone direction to the time axis, continue one variable
   with the OS I semigroup, pass to logarithmic coordinates, glue by
   Malgrange-Zerner, then extract the explicit polydisc.
2. Do not replace this with generic separate holomorphy alone.  Osgood may
   enter only after the local directional continuation data has been produced.
3. If a neutral Malgrange-Zerner theorem is missing, develop it in SCV as a
   named theorem with the exact tube-envelope hypothesis, then use it here.

Concrete theorem surface for the missing analytic producer:

```lean
theorem osii_mz_scalar_log_representative_from_directional_semigroup
    -- fixed positive-time base point `ξ`, chosen dual-cone directions `eμ`,
    -- and a scalar test/pairing `Φ` against the distribution-valued
    -- Schwinger functional
    :
    ∃ Γ : (Fin (k * 4) -> ℂ) -> ℂ,
      DifferentiableOn ℂ Γ (osiiMZLogDomain (k * 4) (Real.pi / 2)) ∧
      -- on each one-coordinate flat tube, `Γ` agrees with the corresponding
      -- rotated OS semigroup continuation after `u = exp r`
      flatTube_agreement Γ directionalSemigroupBranch ∧
      -- on the real edge, `Γ` recovers the scalarized Schwinger distribution
      realEdge_agreement Γ scalarizedSchwingerDistribution
```

This is deliberately scalarized.  In OS II p. 292 the intermediate
`T_i^μ` are distribution-valued in the remaining real variables; in Lean the
faithful route is to pair with a fixed Schwartz test first, prove the scalar
MZ statement, and only then reassemble the continuous linear functional using
the existing CLM/distribution infrastructure.  The compatibility to prove on
overlaps is not a pointwise endpoint shortcut: neighboring branches agree
because each is the rotated semigroup continuation of the same real-edge
Schwinger distribution.

### 2026-05-23 Checked Scalar Flat-Tube Packet

The first scalarized V.1 packet is now checked in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIParametricFlatTubeBranch.lean
```

It constructs:

```lean
osiiParametricFlatTubeBranch
osiiTotalLogSemigroupBranch
```

and proves the key comparison:

```lean
osiiParametricFlatTubeBranch_coordinate_line_eq_total_log
```

This is the explicit semigroup version of the local flat-tube MZ compatibility:
on each one-coordinate strip through a real positive-time base point, the
choice-independent flat branch agrees with

```lean
r ↦ OSInnerProductTimeShiftHolomorphicValueExpandBoth OS lgc F G
      (∑ p, Complex.exp (r p))
```

The proof uses the one-variable totally-real identity theorem on the strip and
the real OS semigroup split; it does not identify endpoint values by fiat.  The
same file also proves that the explicit total branch is holomorphic on
`osiiMZLogDomain m (Real.pi / 2)` and has the common Schwinger real edge.

Next checked theorem should be a coordinate transport statement from the
abstract log variables back to the flattened positive-time-difference
coordinates used by `FlatPositiveTimeDiffReal k d`, followed by the product
tensor scalarization/reproduction identity.  Growth remains Chapter VI and
should still be attached after this continuation payload is in place.

### 2026-05-23 Checked Flat Positive-Time Coordinate Bridge

The coordinate transport step is now checked in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIFlatPositiveTimeBranch.lean
```

It constructs the explicit flattened branch

```lean
u ↦ OSInnerProductTimeShiftHolomorphicValueExpandBoth OS lgc F G
      (∑ i : Fin k, -Complex.I * u (finProdFinEquiv (i, 0)))
```

and proves:

```lean
differentiableOn_osiiFlatTotalTimeBranch_tube
isTimeHolomorphicFlatPositiveTimeDiffWitness_osiiFlatTotalTimeBranch
differentiableOn_acrOne_osiiFlatTotalTimeBranch
osiiFlatTotalTimeBranch_positive_imag_time_edge_eq_total
toDiffFlat_wickRotate_time_eq_I_mul_orderedTimeDiff
osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_total
osiiFlatTotalTimeBranch_single_positive_imag_time_edge_eq_schwinger_timeShift
osiiOrderedPositiveTimeDiff_sum_eq_last
osiiFlatTotalTimeBranch_wickRotate_ordered_edge_eq_last_time
osiiFlatTotalTimeBranch_single_wickRotate_ordered_edge_eq_schwinger_last_time
osiiFlatTotalTimeBranch_single_wickRotate_ordered_edge_eq_schwinger_timeShift
```

This is the missing geometric handoff from the abstract OS-II semigroup
parameter to the actual `ACR(1)` flat time-difference coordinates.  If
`u` lies in the flattened positive-time tube, then `∑ -i u_{i,0}` lies in the
right half-plane.  If `u = BHW.toDiffFlat k d (wickRotatePoint ∘ x)` for
`x ∈ OrderedPositiveTimeRegion d k`, the time slots are exactly
`I *` the successive Euclidean time differences, so the real-edge theorem
recovers the positive-time OS semigroup matrix element at their total.

The common-real-edge scalarization has also been sharpened in the log-domain
packet:

```lean
osiiTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
```

Thus both the MZ log representative and the flattened difference-coordinate
representative now expose their real edge as the concrete Schwinger functional
of an OS-conjugated simple tensor with the right factor shifted by the
appropriate total positive time.  The flat side additionally proves the
telescoping identity `sum_i Δt_i = t_last`, matching the cumulative-time
notation used in the classical OS II/Jost proof.

The next checked theorem should now be the distributional product-tensor
reassembly/reproduction identity that feeds these scalarized branches with the
correct OS-II left/right Borchers factors and delta-smearing real-edge data.
Do not replace that step with a hypothesis saying that the real edge already
agrees.

### 2026-05-23 Checked Positive-Orthant Delta-Smearing Packet

The multi-coordinate OS II V.2 delta-smearing substrate is now checked in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIDeltaSmearing.lean
test/proofideas_osii_positive_orthant_delta_family.lean
```

New facts:

```lean
exists_positiveOrthant_approx_identity_schwartz
exists_positiveOrthant_shrinking_schwartz_approx_identity_for_delta_bridge
translate_positiveOrthant_schwartz_mem
integral_mul_translated_schwartz_eq_integral_weighted_shift_fin
eq_of_positiveOrthant_distribution_eq_on_translated_delta_family
eq_of_positiveOrthant_distribution_eq
```

Mathematical content: OS II does not smear only one spacetime variable in the
general product-tensor step; it smears the finite family of positive
time-difference variables.  The new packet constructs normalized nonnegative
real-valued Schwartz bumps compactly supported inside the finite positive
orthant and shrinking to `0`.  It then proves the actual V.2 limit step: if two
continuous scalar edge candidates have the same distributional pairing against
every compactly supported positive-orthant Schwartz test, they agree pointwise
at every positive time-difference vector.  This is the checked bridge from weak
scalarized real-edge equality to the pointwise common Schwinger value.

The production theorem
`eq_osii_total_positive_time_real_edges_of_positiveOrthant_distribution_eq` now
applies `eq_of_positiveOrthant_distribution_eq` to the scalarized OS-II
product-tensor real-edge candidates.  The remaining nontrivial hypothesis is
exactly the real OS-II pairing equality for all positive-orthant compact tests;
the local integrability and continuity of the two scalar candidates are now
proved from compact support and the checked right-half-plane semigroup real
edge, not assumed.

### Packet D: Symmetry Transport

Lean role: carry the Euclidean OS symmetries to the selected `S_prod`.

Expected theorem slots:

```lean
theorem osii_payload_perm_invariant
theorem osii_payload_translation_invariant
theorem osii_payload_reflected_canonical
```

Implementation notes:

1. Permutation comes from OS `E3` on the real slice plus identity theorem on the
   connected ACR(1) domain.
2. Common complex translation invariance comes from OS `E1` real translation
   invariance plus identity theorem.
3. Reflection/canonical reality comes from OS reflection positivity/reality and
   the OS I reflected semigroup formula.

### Packet E: Chapter VI Growth

Lean role: attach the polynomial bound required by
`exists_acrOne_productTensor_witness`.

Expected theorem slots:

```lean
theorem osii_real_analytic_section_growth_from_lgc
theorem osii_acr1_growth_from_vi_regularization
```

Implementation notes:

1. This is where `OSLinearGrowthCondition.growth_estimate` enters.
2. The proof should follow OS II VI.1: regularize the distribution with a
   compact mollifier, express the regularized value as an OS Hilbert
   scalar product, bound the vectors by `E0'`, then use the same
   Malgrange-Zerner/maximum-principle envelope to control the analytic value.
3. Existing `K2VI1/Bounds.lean` and `K2VI1/Support.lean` contain the `k = 2`
   version of several scalar bound ingredients; general-k should reuse their
   norm-estimate pattern rather than inventing a new spectral shortcut.

## Production Order

1. Keep writing scratch/proof-plan artifacts until a packet theorem has a
   checked proof shape.
2. Promote neutral analysis lemmas first, only when they are real theorem
   content needed by Packet B or C.
3. Do not edit `exists_acrOne_productTensor_witness` until Packet A--E can
   construct the full payload, or until one theorem-level `sorry` can be
   replaced by a strictly smaller already-proved theorem.
4. After each packet promotion, run:

```text
lake env lean <touched-file>
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean
git diff --check -- <touched-files>
```

## Immediate Next Lean Step

## Claude #2146 Concern Response

Claude's #2146 review isolated five risks.  Current handling:

1. The OS-II `hreal` common-real-edge producer is still the hard W4 seam.  The
   local/frozen branch packet added after the review does not assume `hreal`:
   it proves the pointwise semigroup algebra at a matching real base and marks
   the remaining upgrade as the OS-II delta-smearing/distributional step.
2. The theorem-2 reduced lane still has a separate hard analytic seam:
   construct the reduced BHW extension/real-edge PET data and the compact
   collar packet.  Do not treat the OS-II delta-smearing work as closing that
   theorem-2 reduced boundary deformation.
3. `OSToWightmanReduced.lean` is large enough to freeze for further feature
   growth.  New reduced-direction support should land in companion modules
   unless a tiny local edit is required to keep imports coherent.
4. `SourceOrientedRealFullFrameKernel.lean` remains protected/unrelated in
   this lane.  Do not stash, commit, split, or clean it from the E-to-R work.
5. Hypothesis proliferation around `realEdge`/`hreal` is not accepted as a
   proof strategy.  Any next theorem must either construct the positive-time
   product-tensor/delta family or prove the smeared scalar equality needed by
   `eq_of_equal_shrinking_schwartz_approx_identity_integrals`.

Checked base-step substrate:

```text
test/proofideas_osii_delta_smearing.lean
```

It proves the neutral theorem:

```lean
tendsto_integral_shrinking_schwartz_approx_identity
```

stating that a normalized nonnegative Schwartz family with support shrinking
to zero recovers a continuous function value under translation.

This is the first genuine base-step sublemma behind OS II's
"smear with delta-sequences and take the limit"; it is not a wrapper around
the final ACR witness.

Checked Lemma 5.1 domain substrate:

```text
test/proofideas_osii_lemma51_geometry.lean
```

with:

```lean
lemma51_acrOne_local_ball
lemma51_flatPositiveTimeDiff_local_ball
```

These are only the qualitative local-domain guards.  The next real proof step
is the quantitative Lemma 5.1/Malgrange-Zerner producer:

```lean
directional_semigroup_continuation
malgrange_zerner_glue_directional_pieces
local_polydisc_extension_from_A0_and_lemma51
```

Do not promote the qualitative local-ball lemmas as if they were Lemma 5.1.
They are scaffolding for the genuine paper proof.

Checked OS II V.1 directional/gluing substrate:

```text
test/proofideas_osii_directional_semigroup.lean
test/proofideas_osii_lemma51_malgrange_zerner_glue.lean
test/proofideas_osii_mz_log_domain.lean
test/proofideas_osii_mz_flat_tube_envelope.lean
```

with:

```lean
osii_directional_semigroup_expandBoth_differentiableOn_upperHalfPlane
osii_directional_semigroup_expandBoth_positive_imag_eq_OSInnerProduct
osiiMZCoordinateLogStrip
osiiMZ_exp_apply_mem_rightHalfPlane
osii_log_semigroup_branch_differentiableOn_coordinateStrip
osii_log_semigroup_branch_real_edge_eq_OSInnerProduct
osiiMZ_l1LogCarrier_subset_coordinateLogStrip
osii_log_semigroup_branch_differentiableOn_l1LogCarrier
osii_mz_log_semigroup_representative_of_common_real_edge
osii_mz_log_semigroup_representative_of_common_real_edge_family
osii_real_edge_log_split_branch_agrees_total
timeShiftNonnegPositiveTimeBorchers
timeShiftNonnegPositiveTimeBorchers_hasCompactSupport
osiiLeftSplitPositiveBranch
osiiRightSplitPositiveBranch
osiiRightSplitPositiveBranch_hasCompactSupport
osii_real_edge_split_branch_agrees_combined
osii_real_edge_positiveBranch_agrees_combined
osii_real_edge_positiveBranch_agrees_combined_of_nonneg
osiiFrozenTimeUpdate
osiiFrozenSplitRealEdge
osiiFrozenDirectionalLogBranch
osii_frozen_directional_log_branch_differentiableOn_coordinateStrip
osii_frozen_directional_log_branch_real_edge_eq
osii_frozen_split_real_edge_matching_base_eq_total
osii_frozen_directional_log_branch_matching_base_real_edge_eq_total
tendsto_integral_shrinking_schwartz_approx_identity
eq_of_equal_shrinking_schwartz_approx_identity_integrals
flat_positive_time_witness_from_local_mz_patches
acrOne_holomorphic_from_local_mz_patches
mz_overlap_eqOn_of_real_slice_agreement
mz_patch_pairwise_eqOn_of_real_slice_agreement
flat_positive_time_witness_from_local_mz_patches_real_slice_agreement
osiiMZLogDomain
isOpen_osiiMZLogDomain
convex_osiiMZLogDomain
osiiMZLogRealEmbed_mem
isConnected_osiiMZLogDomain
osiiMZLogDomain_pi_half_connected
differentiableOn_osiiMZLogDomain_of_coordinate_slices
eqOn_osiiMZLogDomain_of_real_edge_agreement
osiiMZFlatImaginary
osiiMZFlatImaginaryUnion
osiiMZImaginaryL1Domain
osiiMZFlatLogTubeUnion
isOpen_osiiMZImaginaryL1Domain
convex_osiiMZImaginaryL1Domain
isConnected_osiiMZImaginaryL1Domain
mem_osiiMZFlatLogTubeUnion_iff
tubeDomain_flatImaginaryUnion_eq_flatLogTubeUnion
mem_osiiMZLogDomain_iff_mem_tube_l1
tubeDomain_l1Domain_eq_logDomain_set
osiiMZFlatImaginary_subset_l1Domain
convexHull_flatImaginary_subset_l1Domain
zero_mem_osiiMZFlatImaginaryUnion
l1Domain_subset_convexHull_flatImaginary
convexHull_flatImaginary_eq_l1Domain
flatLogTubeUnion_subset_logDomain_set
convex_logDomain_set
logDomain_set_subset_convexHull_flatLogTubeUnion
convexHull_flatLogTubeUnion_eq_logDomain_set
tubeDomain_convexHull_flatImaginary_eq_l1Tube
tubeDomain_convexHull_flatImaginary_eq_logDomain_set
flatLogTubeUnion_fin1_eq_logDomain_set
scalar_mz_fin1_from_flat_branch
```

These are the first checked Lean pieces on the actual OS II V.1 path:
the expanded OS semigroup matrix element gives the one-variable directional
upper-half-plane continuation, its positive imaginary-axis value is the real
Euclidean time-shift pairing, and pairwise-consistent local MZ patches on the
flattened positive-time tube glue to the flat witness/ACR(1) holomorphic
surface.  The directional file now also includes the OS-II log-coordinate
handoff: `u = exp r_q` maps the strip `|Im r_q| < π / 2` into the right
half-plane, the expanded semigroup matrix element composed with this map is
holomorphic on the one-coordinate log strip, and on the real log edge it
recovers the positive-time OS pairing at time `exp x_q`.  The final `l1`
log carrier `Σ |Im r_q| < π / 2` is checked to lie in every coordinate strip,
so each such directional branch restricts to the eventual convex-envelope
carrier.  The newer overlap theorems discharge the identity-theorem half of
the MZ consistency step: if
nonempty overlaps are connected and the local representatives agree on their
common real edge, then the pairwise `EqOn` family required for gluing follows
by the totally-real identity theorem.  The remaining hard Lemma 5.1 work is
now sharply localized to constructing the multi-coordinate scalarized MZ
representative from these one-coordinate log branches, and proving that the
branches agree as continuations of the same real-edge Schwinger distribution.
The scalar representative part is now checked in the theorem
`osii_mz_log_semigroup_representative_of_common_real_edge`, together with its
q-indexed family form
`osii_mz_log_semigroup_representative_of_common_real_edge_family`: once the
directional semigroup branches have a common Schwinger real-edge scalar, they
glue to a single holomorphic representative on `Σ |Im r_q| < π / 2`.  The
remaining Packet C gap is therefore the OS-specific common-real-edge identity,
proved faithfully by the positive-time delta-smearing/distributional argument,
and then the CLM/product-tensor reassembly.
The real-edge semigroup file now contributes the checked algebraic core of
that identity, `osii_real_edge_log_split_branch_agrees_total`: a branch split
around coordinate `q`, with right shift `exp x_q` composed after the later-time
shift, equals the total positive-time shift `Σ_p exp x_p` under the expected
admissibility hypotheses.  Thus the next missing piece is no longer the
semigroup-shift algebra; it is the OS-II construction of the product-tensor
real-edge scalar and the admissibility/support packet for the positive-time
branch family.
The endpoint-inclusive branch packet is now checked: nonnegative Euclidean
time shifts preserve positive-time Borchers support, and the OS-II left/right
split branches are honest positive-time vectors even when one side of the split
is empty.  The variable selected-time theorem
`osii_real_edge_positiveBranch_agrees_combined` is the form needed by the
one-variable semigroup continuation before specializing the selected parameter
or applying delta-smearing; its `_of_nonneg` version discharges the
admissibility hypotheses directly from positive-time support whenever the
selected time is nonnegative.
The local/frozen branch packet is now also checked.  For a fixed real
positive-time base vector `τ`, `osiiFrozenDirectionalLogBranch` is the
one-coordinate semigroup branch with all other real time variables absorbed
into the left/right positive-time vectors.  Its real-log boundary value is
`osiiFrozenSplitRealEdge`, i.e. the Schwinger scalar with only coordinate `q`
updated.  At the matching real base `τ p = exp (x p)`, every selected
coordinate branch has the same total real-edge value
`OSInnerProduct OS.S F (timeShiftBorchers (∑ p, exp (x p)) G)`.  This is the
pointwise semigroup algebra required by OS II V.1; it deliberately does not
pretend that the branch data is already fixed over all real variables.
The neutral delta-smearing bridge is now in production as well:
`tendsto_integral_shrinking_schwartz_approx_identity` recovers a continuous
point value from a normalized shrinking Schwartz approximate identity, and
`eq_of_equal_shrinking_schwartz_approx_identity_integrals` turns equality of
all such smearings into pointwise equality.  The remaining OS-specific step is
to construct the positive-time product-tensor/delta families and prove their
smeared scalar products agree with the Schwinger distribution.

The checked log-domain file records the exact convex geometry of the MZ
envelope before exponentiating back to coefficient variables:
`sum_i |Im r_i| < α` is open and convex, hence connected for positive aperture,
and it contains every real log-coordinate point.  This is the domain called
`sum |arg w_i^mu| < π/2` after the exponential change of variables in OS II
`(5.8)`.  It also now records the Osgood handoff on this exact carrier:
if the eventual MZ scalar is continuous on `Σ |Im r_i| < α` and holomorphic on
all induced coordinate-slice domains, then it is jointly holomorphic on the
whole log carrier.  A second exact-carrier theorem records the connected
real-edge identity principle on the same domain: two holomorphic
representatives agreeing on the full real log edge agree everywhere on the
carrier.

The checked flat-tube-envelope file records the faithful Malgrange-Zerner
convex-hull geometry behind this log domain: the convex hull of the union of
one-coordinate flat imaginary tubes `|t_q| < α` is exactly the `l^1`
imaginary domain `Σ_q |t_q| < α`; that `l^1` carrier is also checked open,
convex, and connected for positive aperture.  The nontrivial inclusion is
proved by the classical barycentric decomposition of a point into its signed
coordinate-axis points, with weights `|t_q| / Σ |t_q|`.  Thus the remaining MZ
producer no longer needs a new convex-envelope argument.  The same file now
also has the complex-domain bridge: the one-coordinate flat log-tube union is
the tube over the flat imaginary union, the final complex log carrier is convex,
the carrier is contained in the real convex hull of the complex flat log-tube
union by the same signed-axis barycentric decomposition with real parts held
fixed, and therefore
`convexHull ℝ (osiiMZFlatLogTubeUnion m α) = {r | Σ_q |Im r_q| < α}` for
positive aperture.  The remaining analytic MZ producer must construct the
directional flat-tube representatives and prove their common real-edge
identity.  The dimension-one base case of the scalar flat-tube theorem is also
checked: for one log coordinate, the flat-tube union is already the final `l1`
carrier, so a holomorphic flat branch itself supplies the convex-envelope
representative.

The current exact Hdiff diagnostic, from
`lake env lean -DmaxHeartbeats=1200000
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean`,
shows that the ordinary selector block has reduced to the compact-piece
boundary transport

```lean
Tendsto (fun ε => SourcePathMoving ε - WickPathMoving ε)
  (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0)
```

inside `hOrdPieceFixed_selected`.  The surrounding context already proves the
moving/fixed support DCT legs and the endpoint limits for both sides.  The
missing content is not an endpoint rewrite: it is the OS/Jost real-edge
transport identifying the source-path endpoint branch pairing with the Wick
Schwinger value on the compact piece.  This is the same kind of common
real-edge compatibility required by the scalarized MZ producer above.

Checked transport skeleton:

```text
test/proofideas_hdiff_edge_transport.lean
```

with:

```lean
integral_eventuallyEq_of_edge_packet
tendsto_integral_chain_of_edge_packets
```

This is the Lean contract for the missing Hdiff edge packets.  For each
neighboring chart edge it requires a shared `edgeApproach`, shared `edgeWeight`,
eventual rewrites from both neighboring integral expressions to that common
edge integral, and a support collar into the carrier intersection.  Once these
packets are constructed from the OS/Jost boundary-value theorem, the finite
chart chain transports the selected current limit without using a false
endpoint-current shortcut.

Checked OS II Lemma 5.1 coordinate extraction substrate:

```text
test/proofideas_osii_lemma51_coordinate_estimate.lean
```

with:

```lean
osiiLemma51CoeffMap4
osiiLemma51RightHalfPlane4
osiiLemma51NarrowSector4
osiiLemma51_coeff4_linear_identity
osiiLemma51_coeff4_re_pos_of_small_perturbation
osiiLemma51_coeff4_mem_narrowSector_of_small_perturbation
osiiLemma51_exists_coord_radius_coeff4_rightHalfPlane
osiiLemma51_exists_coord_radius_coeff4_narrowSector
osiiLemma51_local_polydisc_extension_differentiableOn
osiiLemma51_local_polydisc_sector_extension_differentiableOn
osiiLemma51ArgSumDomain4
osiiLemma51_abs_arg_eq_arctan_abs_im_div_re
osiiLemma51_narrowSector_subset_argSumDomain4
```

This formalizes the paper's four physical-coordinate algebra in
`(5.11)`--`(5.12)`: the explicit vectors
`(2T,1,1,1)`, `(2T,1,-1,-1)`, `(2T,-1,1,-1)`, and
`(2T,-1,-1,1)` reconstruct `xi + zeta` from `xi_hat` and the coefficients
`w^mu`, and a quantitative small-perturbation bound forces all coefficient
real parts to be positive.  The later radius and composition theorems turn
that pointwise estimate into a genuine local coordinate-polydisc statement:
for `xi^0 > 0`, a small polydisc is mapped into the product of coefficient
right half-planes, and any differentiable MZ-sector representative pulls back
to a differentiable representative near the original real point.

Important correction: OS II `(5.8)` is stronger than a product of right
half-planes; the paper needs a small argument-sum domain.  The checked theorem
`osiiLemma51_coeff4_mem_narrowSector_of_small_perturbation` is the faithful
`(5.13)`-style ratio estimate: if the real and imaginary perturbation pieces in
`(5.12)` are sufficiently small compared with the positive constant part, then
each coefficient lies in an arbitrarily narrow right sector.  The checked
radius theorem packages this as a genuine local coordinate-polydisc statement,
and the sector-composition theorem says that a differentiable representative on
the narrow coefficient sector pulls back to a differentiable representative on
that polydisc.  The checked theorem
`osiiLemma51_narrowSector_subset_argSumDomain4` now discharges the final
coordinate-estimate translation from the ratio-sector predicate to the paper's
explicit argument-sum bound in `(5.8)`/`(5.14)`: if the four arctangent widths
sum to less than `π / 2`, then `Σ |arg w^μ| < π / 2`.

This is the local half-plane/sector coordinate input needed after the
Malgrange-Zerner representatives have been constructed.  It still does not
provide those local representatives; the next hard step remains the
construction of the MZ carriers from the directional semigroup continuations
and the proof that they continue the same real-edge distribution on overlaps.

Checked OS II V.2 translated-delta substrate:

```text
test/proofideas_osii_positive_time_delta_family.lean
test/proofideas_osii_delta_smearing.lean
```

promoted to:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIDeltaSmearing.lean
```

with:

```lean
exists_positiveTime_shrinking_schwartz_approx_identity_for_delta_bridge
exists_positiveTimeCompactSupport_delta_submodule_sequence_for_delta_bridge
translate_positiveTime_schwartz_mem_positiveTimeCompactSupport
integral_mul_translated_schwartz_eq_integral_weighted_shift
eq_of_eventually_equal_shrinking_schwartz_approx_identity_integrals
eq_of_equal_positiveTime_translated_delta_smearings
eq_of_positiveTime_distribution_eq_on_translated_delta_family
```

This closes the neutral and positive-time test-function side of the
`(A_0) -> (P_0)` delta-smearing move: the bumps exist with positive-time
support, translate to honest `positiveTimeCompactSupportSubmodule` tests at
any positive-time center, equality of the translated smearings recovers the
point value, and equality of distributional pairings against all positive-time
compact-support tests now specializes to that translated-delta pointwise
recovery.  The remaining non-neutral proof obligation is now precise: derive
the positive-time compact-test pairing equality from the OS Schwinger/semigroup
identity for the scalar functions at hand.

Checked fixed-probe OS-II pointwise recovery:

```text
test/proofideas_osii_fixed_probe_pointwise_from_delta.lean
test/proofideas_osii_fixed_probe_auto_obligations.lean
test/proofideas_laplace_fourier_continuity.lean
```

promoted to:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIDeltaSmearing.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIFixedProbePointwise.lean
```

with:

```lean
fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge
integrable_weighted_shift_of_integrable_mul_translated
continuousAt_laplaceFourierKernel_of_nonnegEnergy_local
fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge_public
fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge_of_nonnegEnergy
fixed_probe_laplaceFourier_eq_translatedProductShell_of_nonnegEnergy
```

This closes the fixed one-probe instance of the non-neutral OS-II V.2
pointwise step.  The existing compact-test pairing identity
`integral_laplaceFourierKernel_mul_eq_translatedProductShell_integral_local`
now feeds the translated-delta bridge, the translated integrability
obligations are transported through the additive Haar invariance of Lebesgue
measure, the product-shell continuity/integrability is supplied by the VI.1
orbit bridge, and the Laplace-Fourier kernel continuity at a positive-time
center follows from dominated convergence using the nonnegative-energy support
of the Bochner measure.  The final closed form obtains the positive-time
delta-family internally from
`exists_positiveTime_shrinking_schwartz_approx_identity_for_delta_bridge`, so
callers no longer carry delta data for the fixed one-probe pointwise recovery.

The remaining OS-II/MZ producer is therefore no longer the fixed-probe
delta-smearing equality.  It is the multi-coordinate scalar representative:
construct the directional/local MZ carriers, prove their real-edge values are
the common scalar Schwinger distribution on overlaps, and then feed the checked
Lemma-5.1 coordinate packet and MZ gluing substrate.

### 2026-05-23 Checked Positive-Orthant Real-Edge Delta Instantiation

The multi-coordinate delta-smearing bridge now has its first OS-II real-edge
instantiation checked in:

```text
test/proofideas_osii_positive_orthant_real_edge_integrability.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIProductTensorRealEdge.lean
```

New checked support facts:

```lean
integrable_positiveOrthant_schwartz_mul_continuousOn_shift
continuousOn_osii_total_positive_time_real_edge_positiveOrthant
isOpen_positiveOrthant_fin
continuousAt_osii_total_positive_time_real_edge_positiveOrthant
integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_nonneg
integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
integral_osii_real_edge_positiveBranch_pairings_agree_of_tsupport_positive
eq_osii_total_positive_time_real_edges_of_positiveOrthant_distribution_eq
eq_osii_total_positive_time_real_edges_of_positiveBranch_pairings_eq
osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
integral_osii_real_edge_positiveBranch_single_eq_schwinger_timeShift
eq_schwinger_timeShift_single_of_positiveOrthant_pairings_eq
```

Mathematical content: compact positive-orthant Schwartz tests are now known to
be integrable against shifted OS-II real-edge scalar candidates, because their
support remains inside the positive orthant after shifting by a positive center.
The common total positive-time real edge is continuous directly in positive
time-difference coordinates, using the right-half-plane semigroup holomorphic
representative.  Therefore the finite-dimensional positive-orthant
delta-smearing theorem is now instantiated for two OS-II total real-edge
candidates.  The only remaining hypothesis in that instantiated theorem is the
genuine compact positive-orthant test-pairing equality, i.e. the OS
Borchers-factor/product-tensor identity, not any continuity or integrability
side condition.

The integrated split identity now carries the already-checked pointwise OS-II
semigroup split through compact positive-orthant test pairings:

```lean
integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
integral_osii_real_edge_positiveBranch_pairings_agree_of_tsupport_positive
```

This proves that the q-directional split branch and the total positive-time
edge have the same compact-test pairing whenever the test support lies in the
positive orthant, and hence q/q' split branches have the same compact-test
pairing.  The theorem
`eq_osii_total_positive_time_real_edges_of_positiveBranch_pairings_eq` now
packages the actual delta-smearing handoff: a compact-test distributional
identity for two directional split branches implies equality of the two total
positive-time real-edge values.  Thus the remaining theorem-specific
hypothesis is exactly the compact positive-orthant product-tensor/Fubini
pairing identity for those split branches.

For concentrated Borchers factors this interface has also been rewritten on
the Schwinger side:

```lean
osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
integral_osii_real_edge_positiveBranch_single_eq_schwinger_timeShift
eq_schwinger_timeShift_single_of_positiveOrthant_pairings_eq
```

The q-split compact pairing is now identified with
`∫ OS.S (n+r) (ZeroDiagonalSchwartz.ofClassical
  (f.osConjTensorProduct (timeShiftSchwartzNPoint (∑ τ) g))) * h τ`.
The theorem `eq_schwinger_timeShift_single_of_positiveOrthant_pairings_eq`
is the current sharp A0-to-P0 handoff for concentrated factors: equality of
these compact positive-orthant Schwinger shifted-shell pairings implies
pointwise equality of the shifted shells at any positive-time center.  The
remaining product-tensor pairing work is therefore not about the semigroup
split or delta recovery; it is to prove that compact-test Schwinger
shifted-shell equality from the actual product tensor by Fubini.

Important Lean substrate correction: the tempting route
`OS.S (∫ ZeroDiagonalSchwartz-valued shell) = ∫ OS.S shell` does not typecheck
here because `ZeroDiagonalSchwartz` is not available as a normed Bochner target.
The faithful route must follow the existing Section 4.3 finite-probe pattern:
scalarize through Schwartz/finite-probe functionals, prove the explicit
Fubini identity there, and only then feed the compact-test equality above.

### 2026-05-23: Product imaginary-axis kernel bridge

The next Section 4.3 finite-probe substrate has been proved in
`Section43FourierLaplaceTimeProduct.lean`:

```lean
section43TimeImagAxisProductKernel
section43TimeImagAxisProductKernel_apply_of_pos_of_nonneg
section43TimeImagAxisProductKernel_apply_mul_productSource_of_nonneg
section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral_kernel
section43TimeProductTensor_slot_scalar_fubini
section43PartialImagAxisProductFactors
section43PartialImagAxisProductTensor
section43PartialImagAxisProductTensor_empty
section43PartialImagAxisProductTensor_univ
section43PartialImagAxisProductTensor_slot_scalar_fubini
section43PartialImagAxisProductTensorIteratedScalar
section43PartialImagAxisProductTensor_eq_iteratedScalar
section43TimeProductTensor_allSlots_iteratedScalar
```

Mathematical content: the multitime raw exponential kernel used by
`section43IteratedLaplaceRaw` is now identified, on the compact strict-positive
source support, with the tensor product of the one-variable imaginary-axis
Paley-Wiener kernels.  The product-source representative theorem can therefore
be read in the same kernel language as the one-dimensional finite-probe
Fubini theorem.  In addition, any single tensor slot can now be scalarized by
composing an arbitrary scalar functional with
`SchwartzMap.productTensorUpdateCLM` and applying
`section43OneSidedLaplace_scalar_fubini_apply`.

The partial-kernel tensor gives an iteration-ready invariant: for a finite set
of already-transported slots, inserting one new slot is exactly the
one-dimensional scalar Fubini step.  The all-slots corollary now gives a
canonical nested-scalar-integral expression for the product of all one-sided
Laplace representatives.  This is still not the full compact-test Schwinger
shifted-shell equality.  The remaining local Fubini task is to flatten the
nested scalar integrals to the compact positive-orthant pairing used by
`eq_schwinger_timeShift_single_of_positiveOrthant_pairings_eq`.

### 2026-05-23: Product-kernel nested integral flattened modulo honest Fubini packet

The next scratch-first Section 4.3 step has been promoted into
`Section43FourierLaplaceTimeProduct.lean` and
`Section43FourierLaplaceFiniteProbe.lean`:

```lean
section43TimeImagAxisProductKernelIteratedScalar
section43PartialImagAxisProductTensorIteratedScalar_eq_kernelIteratedScalar
section43TimeProductTensor_allSlots_kernelIteratedScalar_finRange
finRangeWeightedIteratedIntegral
finRangeWeightedIteratedIntegral_map_succ
finRangeWeightedFlattenable
finRangeWeightedIteratedIntegral_finRange_eq_integral
section43TimeImagAxisProductKernelIteratedScalar_eq_weighted
section43TimeProductTensor_allSlots_flattened_of_flattenable
integrable_section43ImagAxisPsiKernel_source_apply_clm
```

Mathematical content: the all-slots scalarization no longer ends in an
implicit partial-tensor accumulator.  It is rewritten to a nested scalar
integral whose terminal leaf is exactly
`T (section43TimeImagAxisProductKernel τ)`.  A generic finite-coordinate
Fubini lemma then flattens the natural `List.finRange` slot-update recursion
to one product-space integral, but only under the explicit recursive
`finRangeWeightedFlattenable` hypotheses.  This keeps the real analytic
obligation visible rather than hiding it behind an unconditional wrapper.

The resulting theorem is the current product-source Fubini interface:

```lean
T (section43TimeProductTensor
    (fun i => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
  =
∫ τ : Fin n → ℝ,
  T (section43TimeImagAxisProductKernel τ) *
    (section43TimeProductSource gs).f τ
```

assuming the explicit recursive Fubini/integrability packet.  The
one-dimensional finite-probe machinery now also exposes the scalar
integrability fact
`integrable_section43ImagAxisPsiKernel_source_apply_clm`, which is the seed
for proving that packet in the compact-source case.

### 2026-05-23: Compact-source Fubini packet closed

The recursive packet above is now proved for compact positive-time product
sources.  The promoted facts are:

```lean
continuousOn_section43ImagAxisPsiKernel_Ioi
continuousOn_section43TimeImagAxisProductKernel_strictPositive
integrable_section43TimeImagAxisProductKernel_pair_source
section43TimeImagAxisProductKernel_flattenable
section43TimeProductTensor_allSlots_flattened
```

The genuine analytic point is the compact-support `hpair`: for the successor
split `ℝ × (Fin n → ℝ)`, the product-source support is contained in the
compact product of the one-variable topological supports, and that compact set
lies in the strict positive orthant.  On it, the tensor kernel is continuous in
Schwartz topology, so composing with an arbitrary continuous scalar functional
and multiplying by the product source gives an integrable scalar function.

Consequently the Section 4.3 product-source Fubini interface is now
unconditional for compact product sources:

```lean
T (section43TimeProductTensor
    (fun i => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
  =
∫ ξ : Fin n → ℝ,
  T (section43TimeImagAxisProductKernel ξ) *
    (section43TimeProductSource gs).f ξ
```

The next E-to-R consumer step is to plug this compact product-source identity
into the OS-II payload lane, replacing the former explicit Fubini-packet
assumption by `section43TimeProductTensor_allSlots_flattened`.

### 2026-05-23: Product-tensor Fubini reassembly promoted

The Section 4.3 compact-source identity has now been plugged into the OS-II
positive-orthant real-edge lane in:

```text
test/proofideas_osii_product_tensor_reassembly.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIProductTensorRealEdge.lean
```

New checked theorem surfaces:

```lean
section43_productSource_pairing_eq_of_productTensor_scalar_eq
eq_schwinger_timeShift_single_of_section43_productTensor_scalar_eq
```

Mathematical content: equality of one compact product tensor under two scalar
continuous linear probes, together with pointwise identification of the
imaginary-axis product kernel with the two Schwinger shifted-shell scalars,
implies equality of all compact positive product-source pairings.  Feeding this
into the existing positive-orthant delta theorem gives pointwise equality of
the two Schwinger shifted shells at any positive time-difference center.

This removes the explicit Fubini/integrability packet from the OS-II
product-source handoff.  The remaining producer is now sharper: construct the
two scalar probes from the actual product-tensor Schwinger functional, identify
their `section43TimeImagAxisProductKernel` values with the shifted shells, and
prove their equality on the single tensor of one-sided Laplace representatives.

### 2026-05-23: Schwinger scalar probes now factor through zero-diagonal time-shell CLMs

The scalar-probe producer has been sharpened in checked Lean:

```text
test/proofideas_section43_time_product_scalar_probe.lean
test/proofideas_section43_schwinger_time_multilinear.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTimeScalarProbe.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIProductTensorSchwingerFunctional.lean
```

New production theorem surfaces:

```lean
exists_section43TimeProductTensor_scalarProbe
section43SchwingerTimeProductMultilinearOfCLM
section43_productSource_pairing_eq_of_schwinger_timeCLM_eq
eq_schwinger_timeShift_single_of_schwinger_timeCLM_eq
```

The key correction is that the Schwinger product-time scalar functional cannot
be built by composing `OS.S` with `ZeroDiagonalSchwartz.ofClassical` on
arbitrary time tests: that fallback is not a linear map without a proved
zero-diagonal membership statement.  The correct next producer is a concrete
time-shell map

```lean
SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k
```

whose values on `section43TimeImagAxisProductKernel` are the shifted Schwinger
shells and whose values on one-sided Laplace product tensors agree across the
two branches.  Once those CLMs are built, the new checked consumer feeds them
through the product-source Fubini and positive-orthant delta lane.

### 2026-05-24: Ordered pullback zero-diagonal support leaf

The first attempted support shortcut was false: strict positivity of the raw
`section43QTime` coordinates does not imply ordered Euclidean support, since
two raw positive times may still coincide or be unordered.  The book-faithful
step is to use the difference-coordinate pullback before applying the ordered
sector zero-diagonal lemma.

This is now checked in production as:

```lean
VanishesToInfiniteOrderOnCoincidence_orderedPullback_section43NPointTimeSpatialTensor
```

and was first tested in:

```text
test/proofideas_section43_time_spatial_zero_diagonal.lean
```

The theorem says that if the finite difference-time factor has topological
support in the strict positive orthant, then

```lean
SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
  (section43DiffCoordRealCLE d n)
  (section43NPointTimeSpatialTensor d n φ χ)
```

is a genuine zero-diagonal Schwartz test.  The OS-II Schwinger-functional
companion now also exposes the raw ordered-pullback time/spatial CLM:

```lean
section43OrderedPullbackTimeSpatialTensorCLM
section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
```

This does **not** yet construct the final full-domain
`SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k`: the new support
lemma applies only to time tests with strict-positive difference-time support.
The remaining producer must therefore use the Section 4.3 quotient/source
argument, or otherwise supply zero-diagonal membership for every input of the
full Schwartz CLM.  That is the real current gap.

### 2026-05-24: Positive-support shifted shells and honest kernel consumers

Scratch-first checks:

```text
test/proofideas_osii_positive_support_kernel_consumer.lean
test/proofideas_osii_positive_shift_zero_diagonal_shell.lean
```

Promoted support in:

```text
OSToWightmanOSIIProductTensorRealEdge.lean
OSToWightmanOSIIProductTensorSchwingerFunctional.lean
```

New production facts:

```lean
VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
section43TimeStrictPositiveRegion_sum_pos
VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
eq_schwinger_timeShift_single_of_section43_productTensor_scalar_eq_on_positive
eq_schwinger_timeShift_single_of_timeProductTensor_multilinear_eq_on_positive
eq_schwinger_timeShift_single_of_schwinger_timeCLM_honest_kernel_eq_on_positive
```

Mathematical content:

1. A strictly positive Euclidean time shift of the right OS tensor factor
   preserves zero-diagonal admissibility when both tensor factors have ordered
   positive-time support.
2. On the Section 4.3 strict positive orthant, the total shift
   `∑ p : Fin m, ξ p` is strictly positive, so every positive-orthant
   imaginary-axis shifted shell is an honest `ZeroDiagonalSchwartz` term, not
   the junk branch of `ZeroDiagonalSchwartz.ofClassical`.
3. The scalar and multilinear product-tensor recovery theorems now require
   imaginary-axis kernel identifications only on
   `section43TimeStrictPositiveRegion m`, exactly matching the support of
   compact positive product sources.
4. The zero-diagonal CLM consumer now has a producer-facing honest-kernel
   form: it is enough to prove equality in `ZeroDiagonalSchwartz` for positive
   imaginary-axis kernels, and the Schwinger scalar identity follows.

This removes another over-strong obligation from the W4/E-to-R producer.  The
remaining gap is sharper: construct the actual OS-II time-shell scalar/CLM
producer and prove the one-sided Laplace product representative equality.  The
positive-support consumers no longer ask for off-support kernel values.
