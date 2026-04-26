# SCV Infrastructure Blueprint

Purpose: this note is the implementation blueprint for the remaining
several-complex-variables infrastructure that other proof lanes depend on.

It should be read together with:
- `docs/theorem2_locality_blueprint.md`,
- `docs/theorem3_os_route_blueprint.md`,
- `docs/general_k_continuation_blueprint.md`,
- `docs/gns_pipeline_blueprint.md`.

## 1. Scope

This blueprint covers the SCV packages that are still axiomatic or sorry-backed:

1. `SCV/VladimirovTillmann.lean`,
2. `SCV/BochnerTubeTheorem.lean`,
3. `SCV/TubeBoundaryValues.lean`,
4. the pure tube-domain / identity-theorem interfaces those packages consume.

It does **not** re-document the already proved:

1. `SCV.edge_of_the_wedge_theorem`,
2. `identity_theorem_SCV`,
3. `identity_theorem_tubeDomain`,
4. `identity_theorem_product`.

The theorem-2 locality route also needs a local distributional
edge-of-the-wedge **envelope** theorem.  This is not a replacement for the
proved continuous `SCV.edge_of_the_wedge_theorem`, and it is not a new axiom.
It is a QFT-free SCV theorem built from the continuous EOW construction plus
the standard Streater-Wightman/Jost distributional regularization argument.
The already-developed real-translation, real-mollification, and compact-test
continuity machinery in `SCV/DistributionalUniqueness.lean` is part of this
route; the missing envelope step is the kernel/translation-covariance recovery
that converts the family of regularized continuous-EOW envelopes into one
holomorphic envelope.

## 2. Current status by file

### 2.1. `VladimirovTillmann.lean`

Still axiomatic:

1. `vladimirov_tillmann`,
2. `distributional_cluster_lifts_to_tube`.

These are major analytical packages, not single missing lemmas.

### 2.2. `TubeBoundaryValues.lean`

Still axiomatic:

1. `tube_boundaryValueData_of_polyGrowth`.

This is the QFT-free boundary-value theorem from polynomial growth on a tube
domain.

### 2.3. `BochnerTubeTheorem.lean`

Still sorry-backed:

1. `bochner_local_extension`,
2. `bochner_tube_extension`.

The good news is that the global gluing theorem
`holomorphic_extension_from_local_family`
is already in place, so the remaining content is precise.

### 2.4. Local distributional EOW envelope

Needed by theorem 2:

```lean
SCV.local_distributional_edge_of_the_wedge_envelope
```

This theorem should live in a pure SCV file and should not mention OS,
Wightman functions, Schwinger functions, `bvt_F`, `extendF`, or locality.  The
theorem-2 blueprint records the exact proposed statement: two holomorphic
functions on open opposite wedge neighborhoods of a real edge have a common
distributional boundary value on compactly supported Schwartz tests over that
edge; then they have a common local holomorphic envelope.  The output theorem
must also include uniqueness on the constructed open set: any holomorphic
function on that same `U` with the same plus and minus trace identities agrees
with the produced envelope.  This uniqueness is proved locally by the
continuous EOW identity theorem and then patched across the local chart cover;
it is part of the construction, not an additional downstream assumption.

The public proof package should be split as fourteen theorem surfaces plus the
final envelope theorem:

```lean
lemma localContinuousEOW_envelope
lemma localRealMollifySide_holomorphicOn
lemma localRealMollify_commonContinuousBoundary
lemma regularizedLocalEOW_family
lemma regularizedEnvelope_linearContinuousInKernel
lemma regularizedEnvelope_translationCovariant
lemma regularizedEnvelope_productKernel
lemma translationCovariantProductKernel_descends
theorem distributionalHolomorphic_regular
lemma regularizedEnvelope_kernelRepresentation
lemma regularizedEnvelope_deltaLimit_agreesOnWedges
lemma chartDistributionalEOW_local_envelope
lemma distributionalEOW_extensions_compatible
lemma localDistributionalEOW_patch_extensions
theorem local_distributional_edge_of_the_wedge_envelope
```

The longer list below gives the internal helper lemmas needed to prove those
surfaces.  Internal helper names are allowed when they carry real content
such as compactness, a change of variables, convolution holomorphy,
kernel extraction, or integration by parts; they should not be exported as
theorem-2 wrappers unless a later Lean file genuinely needs them.

The active Lean route is the **Streater-Wightman distributional EOW route**:

1. choose nested local real boxes and a support radius so all real
   translations used by a compactly supported smoothing kernel stay inside the
   larger box;
2. regularize both wedge-side holomorphic functions by real-direction
   convolution with a fixed compactly supported Schwartz kernel;
3. prove the regularized sides have the continuous common boundary value
   `x ↦ T (translateSchwartz (-x) ψ)`;
4. apply the local continuous EOW theorem to each regularized pair, with a
   domain chosen uniformly from the nested-box/support-radius data;
5. prove the resulting envelope values are continuous linear in the kernel and
   satisfy the real-translation covariance forced by uniqueness;
6. use the Schwartz kernel/nuclear theorem plus translation covariance to
   represent the family as convolution with a single distributional kernel on
   the complex neighborhood;
7. use a compactly supported approximate identity and the standard theorem
   that distributional limits of holomorphic functions are holomorphic to
   recover one holomorphic envelope agreeing with the original wedge functions.

A naive "mollify and pass to the limit" route is not sufficient, because the
continuous-EOW neighborhood may shrink with the kernel if support margins are
not fixed and because a family of regularized envelopes must first be shown to
come from one translation-covariant kernel.  The kernel step is exactly the
mathematical content of Streater-Wightman Theorem 2-16.  The earlier
finite-order primitive draft is not the active route: separately normalized
holomorphic primitives in opposite wedges can differ by kernel terms after
taking boundary values, and the false shortcut
`D_1^M ... D_m^M h = 0 -> h is polynomial` is invalid in several variables.

Local reference check: `references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf`,
Theorem 2-16 (printed pp. 81-83), gives exactly this regularization proof:
smear the two wedge functions by a compactly supported real test function,
apply continuous EOW to the resulting continuous-boundary functions, prove the
regularized extensions form a translation-covariant distributional kernel by
the Schwartz nuclear theorem, and recover the holomorphic extension by a delta
sequence.  Theorem 2-17 is the zero-boundary uniqueness corollary; it remains a
useful consumer but is not a substitute for constructing the full envelope.

Infrastructure audit after `agents_chat.md` #1291:

1. The private `local_eow_extension` in `SCV/TubeDomainExtension.lean` should be
   exposed or refactored for the **continuous** layer.  Its global-tube
   hypotheses mean it cannot be applied directly to OS45 local open sets
   `Ωplus/Ωminus`, but its local Cauchy-polydisc construction, patching, and
   overlap-consistency proof are exactly the code to reuse.
2. `SCV/DistributionalUniqueness.lean` already supplies translation,
   compact-support stability, real-mollification holomorphy, approximate
   identity convergence, and zero-boundary uniqueness tools.  The local
   distributional EOW envelope should reuse these lemmas.  What remains to add
   is the nonzero-envelope half of the Streater-Wightman argument: continuous
   boundary values for each regularization, uniform local continuous-EOW
   domains, linearity/continuity in the smoothing kernel, translation
   covariance, kernel representation, and delta-limit recovery.
3. Every new helper below is either an extraction of existing repo SCV code
   (`local_eow_extension`, `local_extensions_consistent`), a standard
   finite-dimensional chart/compactness lemma, an existing real-mollification
   theorem from `DistributionalUniqueness.lean`, or the standard
   Streater-Wightman/Jost kernel-theorem step used in the classical
   distributional EOW proof.

Source ledger for the internal helper list:

| Helper | Source / justification |
|---|---|
| `localWedge_truncated_maps_compact_subcone` | Direct compact-set use of the local wedge hypothesis. |
| `localEOW_choose_cone_basis` | Existing `open_set_contains_basis` in `SCV/TubeDomainExtension.lean`. |
| `localEOW_chart_real_box` | Finite-dimensional topology: open preimage under a linear equivalence contains a small axis box. |
| `localEOW_chart_positive_polywedge_mem` | Local replacement for the existing `Phi_pos_in_tube` / `Phi_neg_in_tube` lemmas in `TubeDomainExtension.lean`. |
| `localEOW_pullback_boundary_value` | Standard distribution pullback under an affine real-linear equivalence with Jacobian. |
| `localEOW_uniform_slowGrowth_order` | Compactness plus maxima of the two local slow-growth orders. |
| `localEOW_nested_axis_boxes`, `localEOW_support_margin` | Finite-dimensional topology: choose `B0 ⋐ B1 ⋐ E` and kernel-support radius `r` so `B0 + supp ψ ⊆ B1`. |
| `localRealMollifySide_holomorphicOn` | Local version of `differentiableOn_realMollify_tubeDomain`: real-direction convolution of a holomorphic wedge function is holomorphic on the shrunken wedge whenever the support margin keeps all translates inside the original local wedge. |
| `localRealMollify_commonContinuousBoundary` | Streater-Wightman regularization step: the regularized plus/minus sides have the same continuous boundary value `x ↦ T (translateSchwartz (-x) ψ)`.  This reuses `continuous_apply_translateSchwartz_of_isCompactSupport` and compact-support stability. |
| `regularizedLocalEOW_family` | Apply local continuous EOW to every fixed smoothing kernel, using one neighborhood determined by the nested boxes and support radius. |
| `regularizedEnvelope_linearContinuousInKernel` | For each point in the common neighborhood, the value of the regularized envelope is a continuous linear functional of the smoothing kernel.  Use a fixed compactly supported cutoff `χr = 1` on the allowed kernel-support ball so the functional is a genuine `SchwartzMap ->L[ℂ] ℂ`, not an LF-space wrapper. |
| `regularizedEnvelope_translationCovariant` | The regularized envelopes satisfy the translation law forced by real-translation of the kernel and the identity theorem on the regularized wedge pieces. |
| `regularizedEnvelope_kernelRepresentation` | Schwartz kernel/nuclear theorem plus translation covariance: the regularized-envelope family is represented by one distributional kernel depending only on the translated complex point. |
| `regularizedEnvelope_deltaLimit_agreesOnWedges` | Approximate-identity recovery: once kernel recovery has produced a holomorphic `H`, compactly supported approximate identities show `H` agrees with the original plus/minus wedge functions on the shrunken wedge pieces. |
| `localContinuousEOW_envelope` | Refactor/extraction of private `local_eow_extension`, with global tube membership replaced by local wedge membership. |
| `chartDistributionalEOW_local_envelope` | Local distributional EOW envelope on one chart, obtained from the regularized-envelope family and delta-limit recovery. |
| `distributionalEOW_extensions_compatible`, `localDistributionalEOW_patch_extensions` | Existing `local_extensions_consistent` and global patching pattern in `edge_of_the_wedge_theorem`. |

Do not write this as "apply `SCV.edge_of_the_wedge_theorem`" without further
work.  The checked theorem `SCV.edge_of_the_wedge_theorem` is stated for global
tubes `TubeDomain C` and `TubeDomain (-C)`, while the OS45 data are local wedge
neighborhoods inside open sets `Ωplus/Ωminus`.  The local theorem must first
extract a local continuous EOW lemma from the Cauchy-polydisc proof pattern in
`SCV/TubeDomainExtension.lean`:

```lean
theorem local_continuous_edge_of_the_wedge_envelope
    {m : ℕ}
    (Ωplus Ωminus : Set (Fin m -> ℂ))
    (E : Set (Fin m -> ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hE_open : IsOpen E)
    (C : Set (Fin m -> ℝ))
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (hC_ne : C.Nonempty)
    (hC_not_zero : (0 : Fin m -> ℝ) ∉ C)
    (hC_cone : ∀ (t : ℝ), 0 < t -> ∀ y ∈ C, t • y ∈ C)
    (hlocal_wedge :
      ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
        ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (hFplus : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin m -> ℝ) -> ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hplus_bv :
      ∀ x ∈ E,
        Tendsto Fplus (nhdsWithin (realEmbed x) Ωplus) (nhds (bv x)))
    (hminus_bv :
      ∀ x ∈ E,
        Tendsto Fminus (nhdsWithin (realEmbed x) Ωminus) (nhds (bv x))) :
    ∃ (U : Set (Fin m -> ℂ)) (F : (Fin m -> ℂ) -> ℂ),
      IsOpen U ∧
      (∀ x ∈ E, realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ Ωplus, F z = Fplus z) ∧
      (∀ z ∈ U ∩ Ωminus, F z = Fminus z) ∧
      (∀ G : (Fin m -> ℂ) -> ℂ,
        DifferentiableOn ℂ G U ->
        (∀ z ∈ U ∩ Ωplus, G z = Fplus z) ->
        ∀ z ∈ U, G z = F z)
```

Its proof is a localization of the existing `TubeDomainExtension.lean` proof:

1. For `m = 0`, use `hC_ne` and `hC_not_zero` as in the global theorem.
2. For `0 < m`, choose linearly independent `ys : Fin m -> Fin m -> ℝ` in the
   open cone `C` using `open_set_contains_basis`.
3. Define the same affine holomorphic chart
   `Phi x0 ys w = realEmbed x0 + Σ j, w j • ys j`.
4. Replace the global lemmas `Phi_pos_in_tube` / `Phi_neg_in_tube` by local
   compact-subcone lemmas: for each sufficiently small polydisc around `0`,
   all directions of the form `Σ j, a_j • ys j` with `a_j ≥ 0` and not all zero,
   after normalization, lie in the compact simplex image
   `simplexDirectionCompact ys ⊆ C`; `hlocal_wedge` then supplies a radius
   making `Phi x0 ys w ∈ Ωplus` when all `0 < (w j).im`, and
   `Phi x0 ys w ∈ Ωminus` when all `(w j).im < 0`.
5. Reuse the checked Cauchy-polydisc construction and patching pattern from
   `local_eow_extension`, but with these local membership lemmas and the
   two `nhdsWithin (realEmbed x)` boundary hypotheses for `Ωplus` and
   `Ωminus`.

Implementation notes:

1. `localWedge_truncated_maps_compact_subcone` is the uniform
   compact-real-support / compact-direction-set consequence of the local wedge
   hypothesis.  It supplies a radius `r > 0` for all `x ∈ K`, all directions
   `η ∈ Kη`, and all `0 < ε < r`.
2. `localEOW_choose_cone_basis` chooses a real basis
   `ys : Fin m -> Fin m -> ℝ` with every `ys j ∈ C`.  Convexity and the cone
   property imply that every nonzero positive linear combination of the `ys j`
   lies in `C`.  This is the chart used by both local continuous EOW and the
   Streater-Wightman regularization construction.
3. `localEOW_chart_real_box` localizes the real edge.  For each `x0 ∈ E` and
   basis `ys`, pull `E` back by `u ↦ x0 + Σ j, u j • ys j`; because `E` is
   open, choose an axis box `B = Π j (a j, b j)` around `0` whose closure maps
   into `E`.  No global convexity of `E` is needed; all integration is done in
   this local box.
4. `localEOW_chart_positive_polywedge_mem` proves that the chart
   `Phi x0 ys w = realEmbed x0 + Σ j, w j • complexify (ys j)` maps a small
   positive polywedge over `B` into `Ωplus` and the reflected negative
   polywedge into `Ωminus`.  The proof normalizes the imaginary direction
   `Σ j, v j • ys j` with `0 < v j`, places it in the compact simplex image
   inside `C`, and applies `hlocal_wedge`.
5. `localEOW_pullback_boundary_value` transports the distributional boundary
   value to the chart.  If `L : (Fin m -> ℝ) ≃L[ℝ] (Fin m -> ℝ)` sends the
   standard basis to `ys`, then
   `Tchart ψ = T (chartPushTest L x0 ψ)` where `chartPushTest` includes the
   absolute determinant/Jacobian factor.  This is a structured change of
   variables, not ad hoc manipulation of integrals.
6. `localEOW_uniform_slowGrowth_order` combines `hslow_plus` and `hslow_minus`
   on the chosen compact real box and compact simplex of chart directions.
   It returns one order `N0` and one radius `r0` valid for both signs after
   pullback.  These estimates justify Fubini, dominated convergence, and
   continuity of the regularized boundary traces.
7. Choose nested boxes `B0 ⋐ B1 ⋐ Echart` and a support radius `rψ > 0` so
   `u ∈ B0` and `t ∈ closedBall 0 rψ` imply `u + t ∈ B1`.  Shrink the plus and
   minus polywedges over `B0` so every real translate by `t` in the same support
   ball remains in the corresponding plus/minus local wedge over `B1`.
8. For every compactly supported Schwartz kernel `ψ` with
   `tsupport ψ ⊆ closedBall 0 rψ`, define
   `Fplusψ z = ∫ t, FplusChart (z + realEmbed t) * ψ t` and similarly for the
   minus side.  `localRealMollifySide_holomorphicOn` proves these are
   holomorphic on the shrunken polywedges.
9. Define the continuous boundary function
   `bvψ u = Tchart (translateSchwartz (-u) ψ)` on `B0`.
   `localRealMollify_commonContinuousBoundary` proves continuity of `bvψ` and
   the plus/minus boundary convergence.  This is exactly the
   Streater-Wightman `T(f_x)` boundary-value step.
10. Apply `localContinuousEOW_envelope` to `Fplusψ`, `Fminusψ`, and `bvψ`,
    producing a regularized envelope `Gψ` on a fixed local complex
    neighborhood `U0` determined by `B0`, `B1`, and `rψ`, not by the individual
    values of `ψ`.
11. Prove `ψ ↦ Gψ z` is continuous linear for every `z ∈ U0`.  Linearity is
    inherited from convolution and from the explicit Cauchy-polydisc formula
    in the continuous EOW construction; continuity uses a fixed smooth cutoff
    `χr = 1` on the allowed kernel-support ball, the compact support radius,
    and the slow-growth bounds.  This avoids introducing a new LF-space object
    while keeping the statement honest on the kernels used by the approximate
    identity.
12. Prove real-translation covariance:
    translating the kernel is the same as translating the regularized envelope
    in the real directions, on the overlap where both sides are defined.  The
    proof compares the two regularized envelopes on plus or minus wedge pieces
    and applies the ordinary identity theorem.
13. Apply the Schwartz kernel/nuclear theorem to the continuous linear map
    `ψ ↦ Gψ z`, locally uniformly in `z`.  The translation covariance identifies
    the two-variable kernel with one distributional object evaluated at
    translated complex points.
14. Let `ψρ` be a compactly supported approximate identity with
    `tsupport ψρ ⊆ closedBall 0 rψ` and `ψρ -> δ0`.  The regularized envelopes
    `Gψρ` converge distributionally, hence locally uniformly on compact subsets,
    to a holomorphic function `H`.  On the plus/minus wedge pieces,
    `Gψρ` converges to `FplusChart`/`FminusChart` by the existing
    approximate-identity theorem for real mollification.  Therefore `H` is the
    desired chart envelope.
15. `distributionalEOW_extensions_compatible` proves agreement of two local
   chart envelopes on overlaps by the ordinary identity theorem: on every
   nonempty overlap the extensions agree with `Fplus` on a positive wedge
   subset, or with `Fminus` on a negative wedge subset.  The already-proved
   distributional uniqueness theorem can still be used as a fallback on tube
   shaped overlap charts, but it is not the envelope-construction step.
16. `localDistributionalEOW_patch_extensions` follows the existing patching
   pattern in `SCV.edge_of_the_wedge_theorem`: define the extension by local
   representatives and use compatibility to prove well-definedness and
   holomorphy.

This package is substantial SCV mathematics.  Do not replace it by a record of
boundary-limit fields, and do not introduce it as an axiom.

Lean pseudocode for the core reductions:

Regularization notation that must be instantiated before theorem proving:

1. `KernelSupportWithin ψ r` is the checked production predicate
   `tsupport (ψ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 r`.
   It does **not** duplicate compact support as a second field.  Compact
   support is a derived theorem in finite-dimensional real space:

   ```lean
   theorem KernelSupportWithin_hasCompactSupport
       {m : ℕ} {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
       (hψ : KernelSupportWithin ψ r) :
       HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ) := by
     exact IsCompact.of_isClosed_subset
       (isCompact_closedBall 0 r) (isClosed_tsupport _) hψ
   ```

   All regularization lemmas that need compact support must consume this
   theorem explicitly.  Do not change the predicate into a bundled record; the
   current closed-ball support statement is the right local margin hypothesis.
2. `BoxMargin B0 B1 r` means
   `∀ u ∈ B0, ∀ t ∈ Metric.closedBall 0 r, u + t ∈ B1`.
3. `LocalTranslateMargin Dsmall Dlarge r` means
   `∀ z ∈ Dsmall, ∀ t ∈ Metric.closedBall 0 r,
     z + realEmbed t ∈ Dlarge`.
   This name is only a short abbreviation for the displayed support-margin
   fact.  Production proofs should unfold it or use a theorem whose statement
   exposes exactly this closed-ball real-translation condition; it must not be
   treated as an opaque boundary-value predicate.
4. `realMollifyLocal F ψ z` is
   `∫ t : Fin m -> ℝ, F (z + realEmbed t) * ψ t`.
   This is the same convention already used by
   `differentiableOn_realMollify_tubeDomain`.
5. `mollifiedBoundary T ψ u` is
   `T (translateSchwartz (-u) ψ)`.  With the convention
   `translateSchwartz a ψ x = ψ (x + a)`, this is the boundary value of
   `realMollifyLocal F ψ` at the real point `u`.
6. `SmallKernelSpace r` is the test-kernel space used by the kernel theorem:
   in production Lean this should be implemented by a fixed smooth cutoff
   `χr` rather than by introducing a new LF-space wrapper.  Choose
   `χr = 1` on `closedBall 0 r` and `tsupport χr ⊆ closedBall 0 rLarge`.
   Then `ψ ↦ χr • ψ` is a continuous linear map on `SchwartzMap`, and it
   agrees with the identity on all kernels whose support is contained in
   `closedBall 0 r`.  This gives an honest
   `SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ` substrate for the kernel theorem.
7. `CompactSupportedApproxIdentity ψι l` is only a documentation shorthand for
   the concrete data used by the proof: every `ψι i` is a compactly supported
   Schwartz kernel, eventually `tsupport ψι i ⊆ Metric.closedBall 0 r` for the
   fixed radius in the local construction, `∫ t, ψι i t = 1`, and convolution
   against `ψι i` tends to the identity in the Schwartz topology.  Do not
   introduce it as an opaque production structure unless the fields are exactly
   these analytic obligations.

```lean
lemma localWedge_truncated_maps_compact_subcone
    {m : ℕ} {Ωplus Ωminus : Set (Fin m -> ℂ)}
    {E C : Set (Fin m -> ℝ)}
    (hlocal_wedge :
      ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
        ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (φ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hφ_compact : HasCompactSupport (φ : (Fin m -> ℝ) -> ℂ))
    (hφ_supp : tsupport (φ : (Fin m -> ℝ) -> ℂ) ⊆ E)
    (Kη : Set (Fin m -> ℝ)) (hKη_compact : IsCompact Kη) (hKη_sub : Kη ⊆ C) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ tsupport (φ : (Fin m -> ℝ) -> ℂ),
        ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
          (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
          (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus

lemma localEOW_choose_cone_basis
    {m : ℕ}
    (C : Set (Fin m -> ℝ))
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (hC_ne : C.Nonempty)
    (hC_cone : ∀ (t : ℝ), 0 < t -> ∀ y ∈ C, t • y ∈ C) :
    ∃ (ys : Fin m -> Fin m -> ℝ),
      LinearIndependent ℝ ys ∧
      (∀ j, ys j ∈ C) ∧
      (∀ a : Fin m -> ℝ,
        (∀ j, 0 < a j) ->
          (∑ j, a j • ys j) ∈ C)

def localEOWChart
    {m : ℕ}
    (x0 : Fin m -> ℝ)
    (ys : Fin m -> Fin m -> ℝ) :
    (Fin m -> ℂ) -> (Fin m -> ℂ) :=
  fun w a => (x0 a : ℂ) + ∑ j, w j * (ys j a : ℂ)

def localEOWRealChart
    {m : ℕ}
    (x0 : Fin m -> ℝ)
    (ys : Fin m -> Fin m -> ℝ) :
    (Fin m -> ℝ) -> (Fin m -> ℝ) :=
  fun u a => x0 a + ∑ j, u j * ys j a

def IsOpenAxisBox {m : ℕ} (B : Set (Fin m -> ℝ)) : Prop :=
  ∃ a b : Fin m -> ℝ,
    (∀ j, a j < b j) ∧ B = {u | ∀ j, a j < u j ∧ u j < b j}

def PositivePolywedge {m : ℕ} (B : Set (Fin m -> ℝ)) (δ : ℝ) :
    Set (Fin m -> ℂ) :=
  {z | (fun j => (z j).re) ∈ B ∧ ∀ j, 0 < (z j).im ∧ (z j).im < δ}

def NegativePolywedge {m : ℕ} (B : Set (Fin m -> ℝ)) (δ : ℝ) :
    Set (Fin m -> ℂ) :=
  {z | (fun j => (z j).re) ∈ B ∧ ∀ j, -δ < (z j).im ∧ (z j).im < 0}

lemma localEOW_chart_real_box
    {m : ℕ} {E : Set (Fin m -> ℝ)}
    (hE_open : IsOpen E)
    (x0 : Fin m -> ℝ)
    (hx0 : x0 ∈ E)
    (ys : Fin m -> Fin m -> ℝ)
    (hys_li : LinearIndependent ℝ ys) :
    ∃ (a b : Fin m -> ℝ),
      (∀ j, a j < 0 ∧ 0 < b j) ∧
      (∀ u : Fin m -> ℝ,
        (∀ j, a j ≤ u j ∧ u j ≤ b j) ->
          localEOWRealChart x0 ys u ∈ E)

lemma localEOW_nested_axis_boxes
    {m : ℕ} {E : Set (Fin m -> ℝ)}
    (hE_open : IsOpen E)
    (x0 : Fin m -> ℝ)
    (hx0 : x0 ∈ E)
    (ys : Fin m -> Fin m -> ℝ)
    (hys_li : LinearIndependent ℝ ys) :
    ∃ (B0 B1 : Set (Fin m -> ℝ)) (r : ℝ),
      IsOpenAxisBox B0 ∧ IsOpenAxisBox B1 ∧ 0 < r ∧
      x0 ∈ localEOWRealChart x0 ys '' B0 ∧
      (∀ u ∈ B0, ∀ t ∈ Metric.closedBall 0 r, u + t ∈ B1) ∧
      (∀ u ∈ B1, localEOWRealChart x0 ys u ∈ E)

def KernelSupportWithin
    {m : ℕ}
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (r : ℝ) : Prop :=
  HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ) ∧
    tsupport (ψ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 r

def KernelCutoff
    {m : ℕ}
    (χ : (Fin m -> ℝ) -> ℂ)
    (r rLarge : ℝ) : Prop :=
  ContDiff ℝ ⊤ χ ∧
    (∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r, χ t = 1) ∧
    HasCompactSupport χ ∧
    tsupport χ ⊆ Metric.closedBall 0 rLarge

noncomputable def cutoffKernelCLM
    {m : ℕ}
    (χ : (Fin m -> ℝ) -> ℂ)
    (hχ_temp : χ.HasTemperateGrowth) :
    SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ]
      SchwartzMap (Fin m -> ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ χ

def BoxMargin
    {m : ℕ}
    (B0 B1 : Set (Fin m -> ℝ))
    (r : ℝ) : Prop :=
  ∀ u ∈ B0, ∀ t ∈ Metric.closedBall 0 r, u + t ∈ B1

def LocalTranslateMargin
    {m : ℕ}
    (Dsmall Dlarge : Set (Fin m -> ℂ))
    (r : ℝ) : Prop :=
  ∀ z ∈ Dsmall, ∀ t ∈ Metric.closedBall 0 r, z + realEmbed t ∈ Dlarge

noncomputable def realMollifyLocal
    {m : ℕ}
    (F : (Fin m -> ℂ) -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
    (Fin m -> ℂ) -> ℂ :=
  fun z => ∫ t : Fin m -> ℝ, F (z + realEmbed t) * ψ t

noncomputable def mollifiedBoundary
    {m : ℕ}
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
    (Fin m -> ℝ) -> ℂ :=
  fun u => T (translateSchwartz (-u) ψ)

lemma localRealMollifySide_holomorphicOn
    {m : ℕ}
    (Dsmall Dlarge : Set (Fin m -> ℂ))
    (F : (Fin m -> ℂ) -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (r : ℝ)
    (hψ : KernelSupportWithin ψ r)
    (hmargin : LocalTranslateMargin Dsmall Dlarge r)
    (hF_holo : DifferentiableOn ℂ F Dlarge) :
    DifferentiableOn ℂ (realMollifyLocal F ψ) Dsmall

lemma mollifiedBoundary_continuousOn
    {m : ℕ}
    (B : Set (Fin m -> ℝ))
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ)) :
    ContinuousOn (mollifiedBoundary T ψ) B

lemma localRealMollify_commonContinuousBoundary
    {m : ℕ}
    (DplusSmall DminusSmall DplusLarge DminusLarge : Set (Fin m -> ℂ))
    (B C : Set (Fin m -> ℝ))
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (hFplus : DifferentiableOn ℂ Fplus DplusLarge)
    (hFminus : DifferentiableOn ℂ Fminus DminusLarge)
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (r : ℝ)
    (hψ : KernelSupportWithin ψ r)
    (hmargin_plus : LocalTranslateMargin DplusSmall DplusLarge r)
    (hmargin_minus : LocalTranslateMargin DminusSmall DminusLarge r)
    (hslow_plus :
      ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ B ->
        ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
          ∃ (A : ℝ) (N : ℕ) (r0 : ℝ), 0 < A ∧ 0 < r0 ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r0 ->
              ‖Fplus (fun a => (x a : ℂ) +
                (ε : ℂ) * (η a : ℂ) * Complex.I)‖ ≤ A * (ε⁻¹) ^ N)
    (hslow_minus :
      ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ B ->
        ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
          ∃ (A : ℝ) (N : ℕ) (r0 : ℝ), 0 < A ∧ 0 < r0 ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r0 ->
              ‖Fminus (fun a => (x a : ℂ) -
                (ε : ℂ) * (η a : ℂ) * Complex.I)‖ ≤ A * (ε⁻¹) ^ N)
    (hplus_bv :
      ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
        ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
          HasCompactSupport (φ : (Fin m -> ℝ) -> ℂ) ->
          tsupport (φ : (Fin m -> ℝ) -> ℂ) ⊆ B ->
          TendstoUniformlyOn
            (fun ε η =>
              ∫ x : Fin m -> ℝ,
                Fplus (fun a => (x a : ℂ) +
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : Fin m -> ℝ => T φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη)
    (hminus_bv :
      ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
        ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
          HasCompactSupport (φ : (Fin m -> ℝ) -> ℂ) ->
          tsupport (φ : (Fin m -> ℝ) -> ℂ) ⊆ B ->
          TendstoUniformlyOn
            (fun ε η =>
              ∫ x : Fin m -> ℝ,
                Fminus (fun a => (x a : ℂ) -
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : Fin m -> ℝ => T φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη)
    :
    ContinuousOn (mollifiedBoundary T ψ) B ∧
    (∀ u ∈ B,
      Tendsto (realMollifyLocal Fplus ψ)
        (nhdsWithin (realEmbed u) DplusSmall)
        (nhds (mollifiedBoundary T ψ u))) ∧
    (∀ u ∈ B,
      Tendsto (realMollifyLocal Fminus ψ)
        (nhdsWithin (realEmbed u) DminusSmall)
        (nhds (mollifiedBoundary T ψ u)))

lemma regularizedLocalEOW_family
    {m : ℕ}
    (DplusSmall DminusSmall : Set (Fin m -> ℂ))
    (B C : Set (Fin m -> ℝ))
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (r : ℝ) :
    ∃ (U0 : Set (Fin m -> ℂ)),
      IsOpen U0 ∧
      (∀ u ∈ B, realEmbed u ∈ U0) ∧
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        KernelSupportWithin ψ r ->
          ∃ Gψ : (Fin m -> ℂ) -> ℂ,
            DifferentiableOn ℂ Gψ U0 ∧
            (∀ z ∈ U0 ∩ DplusSmall,
              Gψ z = realMollifyLocal Fplus ψ z) ∧
            (∀ z ∈ U0 ∩ DminusSmall,
              Gψ z = realMollifyLocal Fminus ψ z) ∧
            (∀ Hψ : (Fin m -> ℂ) -> ℂ,
              DifferentiableOn ℂ Hψ U0 ->
              (∀ z ∈ U0 ∩ DplusSmall,
                Hψ z = realMollifyLocal Fplus ψ z) ->
              ∀ z ∈ U0, Hψ z = Gψ z)

lemma regularizedEnvelope_linearContinuousInKernel
    {m : ℕ}
    (U0 : Set (Fin m -> ℂ))
    (G : SchwartzMap (Fin m -> ℝ) ℂ ->
      (Fin m -> ℂ) -> ℂ)
    (r rLarge : ℝ)
    (χ : (Fin m -> ℝ) -> ℂ)
    (hχ : KernelCutoff χ r rLarge)
    (hχ_temp : χ.HasTemperateGrowth) :
    ∀ z ∈ U0,
      ∃ Lz : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
        ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
          KernelSupportWithin ψ r ->
            Lz ψ = G (cutoffKernelCLM χ hχ_temp ψ) z

lemma regularizedEnvelope_translationCovariant
    {m : ℕ}
    (U0 : Set (Fin m -> ℂ))
    (G : SchwartzMap (Fin m -> ℝ) ℂ ->
      (Fin m -> ℂ) -> ℂ) :
    -- If both sides are defined and the translated kernel keeps the same
    -- support radius, then this equality follows by comparing on a wedge
    -- piece and applying the identity theorem.
    ∀ (a : Fin m -> ℝ) (ψ : SchwartzMap (Fin m -> ℝ) ℂ) (z : Fin m -> ℂ),
      z ∈ U0 ->
      z - realEmbed a ∈ U0 ->
      G (translateSchwartz a ψ) z = G ψ (z - realEmbed a)

lemma regularizedEnvelope_kernelRepresentation
    {m : ℕ}
    (Ucore : Set (Fin m -> ℂ))
    (U0 : Set (Fin m -> ℂ))
    (G : SchwartzMap (Fin m -> ℝ) ℂ ->
      (Fin m -> ℂ) -> ℂ)
    (r : ℝ)
    (hU_open : IsOpen U0)
    (hcore_margin : LocalTranslateMargin Ucore U0 r)
    (hG_holo :
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        KernelSupportWithin ψ r ->
          DifferentiableOn ℂ (G ψ) U0)
    (hlin :
      ∀ z ∈ U0,
        ∃ Lz : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
          ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
            KernelSupportWithin ψ r ->
              Lz ψ = G ψ z)
    (hcov :
      ∀ (a : Fin m -> ℝ) (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
        (z : Fin m -> ℂ),
        KernelSupportWithin ψ r ->
        KernelSupportWithin (translateSchwartz a ψ) r ->
        z ∈ U0 ->
        z - realEmbed a ∈ U0 ->
        G (translateSchwartz a ψ) z = G ψ (z - realEmbed a)) :
    ∃ H : (Fin m -> ℂ) -> ℂ,
      DifferentiableOn ℂ H U0 ∧
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        KernelSupportWithin ψ r ->
          ∀ z ∈ Ucore,
            G ψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t

lemma regularizedEnvelope_deltaLimit_agreesOnWedges
    {m : ℕ} {ι : Type*} {l : Filter ι}
    (Ucore : Set (Fin m -> ℂ))
    (U0 : Set (Fin m -> ℂ))
    (G : SchwartzMap (Fin m -> ℝ) ℂ ->
      (Fin m -> ℂ) -> ℂ)
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (DplusSmall DminusSmall : Set (Fin m -> ℂ))
    (H : (Fin m -> ℂ) -> ℂ)
    (r : ℝ)
    (hH_holo : DifferentiableOn ℂ H U0)
    (hH_rep :
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        KernelSupportWithin ψ r ->
        ∀ z ∈ Ucore,
          G ψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t)
    (ψι : ι -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hψι_support : ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
    (hG_plus :
      ∀ᶠ i in l, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψι i) z = realMollifyLocal Fplus (ψι i) z)
    (hG_minus :
      ∀ᶠ i in l, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψι i) z = realMollifyLocal Fminus (ψι i) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun i => realMollifyLocal Fplus (ψι i) z) l (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun i => realMollifyLocal Fminus (ψι i) z) l (nhds (Fminus z)))
    (hkernel_limit :
      ∀ z ∈ Ucore,
        Tendsto (fun i => G (ψι i) z) l (nhds (H z)))
    :
    (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
    (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z)

lemma chartDistributionalEOW_local_envelope
    {m : ℕ}
    (Ωplus Ωminus : Set (Fin m -> ℂ))
    (E C : Set (Fin m -> ℝ))
    (x0 : Fin m -> ℝ) (hx0 : x0 ∈ E)
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    -- plus the local wedge, slow-growth, and boundary-value hypotheses
    -- restricted to the chosen chart box
    :
    ∃ (Ux0 : Set (Fin m -> ℂ)) (Hx0 : (Fin m -> ℂ) -> ℂ),
      IsOpen Ux0 ∧
      realEmbed x0 ∈ Ux0 ∧
      DifferentiableOn ℂ Hx0 Ux0 ∧
      (∀ z ∈ Ux0 ∩ Ωplus, Hx0 z = Fplus z) ∧
      (∀ z ∈ Ux0 ∩ Ωminus, Hx0 z = Fminus z)
```

Kernel-recovery implementation substrate:

1. Do **not** consume the QFT-facing axiom
   `Wightman.WightmanAxioms.schwartz_nuclear_extension` in this SCV theorem.
   The local distributional EOW theorem must remain QFT-free.  If the existing
   nuclear-space files are reused, the exported theorem should live in `SCV`
   with no Wightman, OS, field, or vacuum parameters.
2. The production file should introduce a pure theorem package, tentatively in
   `SCV/DistributionalEOWKernel.lean`:

   ```lean
   abbrev ComplexChartSpace (m : ℕ) := Fin m -> ℂ

   def SupportsInOpen
       {E : Type*} [TopologicalSpace E]
       (φ : E -> ℂ) (U : Set E) : Prop :=
     HasCompactSupport φ ∧ tsupport φ ⊆ U

   def complexRealDir {m : ℕ} (j : Fin m) : ComplexChartSpace m :=
     fun k => if k = j then 1 else 0

   def complexImagDir {m : ℕ} (j : Fin m) : ComplexChartSpace m :=
     fun k => if k = j then Complex.I else 0

   noncomputable def directionalDerivSchwartzCLM
       {m : ℕ} (v : ComplexChartSpace m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     -- The Schwartz derivative CLM in the real direction `v`, where
     -- `ComplexChartSpace m` is regarded as a real normed vector space.
     LineDeriv.lineDerivOpCLM ℂ
       (SchwartzMap (ComplexChartSpace m) ℂ) v

   noncomputable def dbarSchwartzCLM
       {m : ℕ} (j : Fin m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     (1 / 2 : ℂ) •
       (directionalDerivSchwartzCLM (complexRealDir j) +
         Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

   def IsDistributionalHolomorphicOn
       {m : ℕ}
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (U : Set (ComplexChartSpace m)) : Prop :=
     ∀ j : Fin m,
       ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
         SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U ->
           T (dbarSchwartzCLM j φ) = 0

   def RepresentsDistributionOnComplexDomain
       {m : ℕ}
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (H : ComplexChartSpace m -> ℂ)
       (U : Set (ComplexChartSpace m)) : Prop :=
     ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
       SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U ->
         T φ = ∫ z : ComplexChartSpace m, H z * φ z

   noncomputable def complexTranslateSchwartz
       {m : ℕ} (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ :=
     -- `(complexTranslateSchwartz a φ) z = φ (z + realEmbed a)`,
     -- implemented by `SchwartzMap.compCLM` for the affine real translation.
     complexTranslateSchwartzCLM a φ

   noncomputable def schwartzTensorProduct₂
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
     -- pointwise `(x,y) ↦ φ x * ψ y`, proved from product-space
     -- Schwartz seminorm estimates in `SCV/DistributionalEOWKernel.lean`.
     schwartzTensorProductRaw φ ψ

   theorem schwartzKernel₂_extension
       {m : ℕ}
       (B : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         (SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)) :
       ∃! K :
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ, K (schwartzTensorProduct₂ φ ψ) = B φ ψ

   lemma kernelCutoff_exists
       {m : ℕ} {r rLarge : ℝ} (hr : 0 < r) (hrLarge : r < rLarge) :
       ∃ χ : (Fin m -> ℝ) -> ℂ,
         KernelCutoff χ r rLarge ∧ χ.HasTemperateGrowth

   lemma regularizedEnvelope_valueCLM_of_cutoff
       -- fixed cutoff, uniqueness of `Gψ`, slow-growth bounds, and explicit
       -- continuous-EOW construction
       :
       ∀ z ∈ U0,
         ∃ Lz : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
           ∀ ψ, KernelSupportWithin ψ r ->
             Lz ψ = G (cutoffKernelCLM χ hχ_temp ψ) z

   lemma regularizedEnvelope_covariance_of_uniqueness
       -- compare the translated-kernel envelope and translated envelope on a
       -- wedge piece, then use continuous-EOW uniqueness
       :
       ∀ a ψ z,
         KernelSupportWithin ψ r ->
         KernelSupportWithin (translateSchwartz a ψ) r ->
         z ∈ U0 -> z - realEmbed a ∈ U0 ->
           G (translateSchwartz a ψ) z = G ψ (z - realEmbed a)

   def ProductKernelRealTranslationCovariantGlobal
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       Prop :=
     ∀ a φ ψ,
       K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
         K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

   def ProductKernelRealTranslationCovariantLocal
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Ucore : Set (ComplexChartSpace m)) (r : ℝ) : Prop :=
     ∀ a φ ψ,
       SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
       SupportsInOpen
         (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ) Ucore ->
       KernelSupportWithin ψ r ->
       KernelSupportWithin (translateSchwartz a ψ) r ->
         K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
           K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

   def realConvolutionShearCLE (m : ℕ) :
       (ComplexChartSpace m × (Fin m -> ℝ)) ≃L[ℝ]
         (ComplexChartSpace m × (Fin m -> ℝ))

   noncomputable def complexRealFiberIntegralRaw
       {m : ℕ}
       {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
       [CompleteSpace V]
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
       (z : ComplexChartSpace m) : V :=
     ∫ t : Fin m -> ℝ, F (z, t)

   noncomputable def complexRealFiberIntegral
       {m : ℕ}
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ

   noncomputable def realConvolutionTest
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ :=
     complexRealFiberIntegral
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (realConvolutionShearCLE m)
         (schwartzTensorProduct₂ φ ψ))

   theorem realConvolutionTest_apply
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       realConvolutionTest φ ψ z =
         ∫ t : Fin m -> ℝ, φ (z - realEmbed t) * ψ t

   theorem translationCovariantProductKernel_descends
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)

   theorem translationCovariantProductKernel_descends_local
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Ucore : Set (ComplexChartSpace m)) (r : ℝ)
       (hcov : ProductKernelRealTranslationCovariantLocal K Ucore r)
       -- plus the fixed-cutoff hypotheses making the localized kernel equal to
       -- a globally covariant cutoff extension on supported product tests
       :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               Hdist (realConvolutionTest φ ψ)

   theorem distributionalHolomorphic_regular
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0) :
       ∃ H : (Fin m -> ℂ) -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         RepresentsDistributionOnComplexDomain Hdist H U0

   theorem regularizedEnvelope_kernelRecovery
       (Ucore U0 : Set (ComplexChartSpace m))
       (G : SchwartzMap (Fin m -> ℝ) ℂ -> (ComplexChartSpace m -> ℂ))
       (r : ℝ)
       (hU0_open : IsOpen U0)
       (hcore_margin : LocalTranslateMargin Ucore U0 r)
       (hG_holo :
         ∀ ψ, KernelSupportWithin ψ r ->
           DifferentiableOn ℂ (G ψ) U0)
       (hlin :
         ∀ z ∈ U0,
           ∃ Lz : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
             ∀ ψ, KernelSupportWithin ψ r -> Lz ψ = G ψ z)
       (hcov :
         ∀ a ψ z,
           KernelSupportWithin ψ r ->
           KernelSupportWithin (translateSchwartz a ψ) r ->
           z ∈ U0 -> z - realEmbed a ∈ U0 ->
             G (translateSchwartz a ψ) z = G ψ (z - realEmbed a)) :
       ∃ H : (Fin m -> ℂ) -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         ∀ ψ, KernelSupportWithin ψ r ->
           ∀ z ∈ Ucore,
             G ψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t
   ```

   The derivative line is not pseudocode: the existing repo already uses
   `LineDeriv.lineDerivOpCLM` for Schwartz directional derivatives in
   `SCV/TubeBoundaryValueExistence.lean`.  The names
   `complexTranslateSchwartzCLM`, `schwartzTensorProduct₂`,
   `realConvolutionShearCLE`, `complexRealFiberIntegral`, and
   `realConvolutionTest` designate QFT-free construction lemmas on Schwartz
   space; they must be proved directly from `SchwartzMap.compCLM`, product-space
   tensor estimates, finite-dimensional fiber-integration estimates, and
   continuous-linear-equivalence pullback before the kernel-recovery theorem is
   attempted.
   Repo audit: there is already a generic-looking external tensor API
   `SchwartzMap.tensorProduct` with `SchwartzMap.tensorProduct_apply`, but it
   currently lives in `OSReconstruction/Wightman/SchwartzTensorProduct.lean`.
   The pure SCV file must not import that Wightman module.  The theorem-2 SCV
   file has therefore reproved the needed product-space Schwartz estimates
   locally and exposed only `schwartzTensorProduct₂`.
   For theorem 2, do not first broaden the public theorem surface to arbitrary
   finite-dimensional spaces.  The required public declaration is exactly the
   mixed chart product `ComplexChartSpace m × (Fin m -> ℝ)`.  Implement it by
   reproducing the split-variable seminorm proof locally in SCV: define a
   private projection-based product helper
   `schwartzTensorProductRaw φ ψ : SchwartzMap (E₁ × E₂) ℂ`, prove rapid decay
   from the Leibniz estimate
   `norm_iteratedFDeriv_mul_le`, the projection bounds
   `ContinuousLinearMap.norm_fst_le` and
   `ContinuousLinearMap.norm_snd_le`, and the pointwise seminorm bounds
   `SchwartzMap.le_seminorm`, then expose only
   `schwartzTensorProduct₂` for
   `E₁ = ComplexChartSpace m`, `E₂ = Fin m -> ℝ`.  This is now checked in
   `SCV/DistributionalEOWKernel.lean`, including the apply theorem
   `(schwartzTensorProduct₂ φ ψ) (z,t) = φ z * ψ t`.
   The real-direction shear is also checked there, with apply theorems for the
   forward and inverse maps.  The raw generic fiber integral
   `complexRealFiberIntegralRaw` is checked as a definition with its apply
   theorem, and the fixed-fiber Bochner integrability lemma
   `integrable_complexRealFiber` is checked.  The base-direction derivative
   field `baseFDerivSchwartz` and its apply theorem are also checked.  The
   zeroth-order weighted decay estimate
   `exists_norm_pow_mul_complexRealFiberIntegralRaw_le` is checked, as is the
   uniform integrable-bound lemma
   `exists_integrable_bound_baseFDerivSchwartz`.  The
   derivative-under-the-integral theorem
   `hasFDerivAt_complexRealFiberIntegralRaw` is checked, as are
   `fderiv_complexRealFiberIntegralRaw_eq`,
   `continuous_complexRealFiberIntegralRaw`,
   `contDiff_nat_complexRealFiberIntegralRaw`, and
   `contDiff_complexRealFiberIntegralRaw`.  The next implementation target is
   no longer the convolution-test construction: the higher-order decay
   induction, `complexRealFiberIntegral`, `realConvolutionTest`, and the exact
   apply theorem
   `realConvolutionTest φ ψ z = ∫ t, φ (z - realEmbed t) * ψ t`
   are checked, as are the first fiber-descent primitives
   `complexRealFiberTranslateSchwartzCLM`,
   `complexRealFiberIntegral_fiberTranslate`,
   `complexRealFiberIntegral_schwartzTensorProduct₂`,
   `translateSchwartz_translateSchwartz`,
   `complexTranslateSchwartz_complexTranslateSchwartz`,
   `shearedProductKernelFunctional`, and
   `IsComplexRealFiberTranslationInvariant`, plus the sheared tensor identity
   `complexRealFiberTranslate_shearedTensor_eq`.  The mixed fiber quotient and
   normalized-cutoff factorization are now checked in
   `DistributionalEOWKernelTransport.lean` and
   `DistributionalEOWKernelFactorization.lean`.  The next implementation target
   is therefore the mixed product-tensor density/kernel-extension theorem; only
   after that can product-test covariance be promoted to the sheared
   product-kernel invariance theorem and the global translation-covariant
   descent layer.

   The `realConvolutionTest` construction must be implemented by the following
   exact Lean route, not by an informal convolution placeholder.

   1. Define the real-direction shear as a real continuous linear equivalence:
      ```lean
      def realConvolutionShearCLE (m : ℕ) :
          (ComplexChartSpace m × (Fin m -> ℝ)) ≃L[ℝ]
            (ComplexChartSpace m × (Fin m -> ℝ))
      ```
      with pointwise equations
      ```lean
      realConvolutionShearCLE m (z, t) = (z - realEmbed t, t)
      (realConvolutionShearCLE m).symm (w, t) = (w + realEmbed t, t)
      ```
      The proof is elementary `ext`/`simp`: addition, subtraction, and real
      scalar multiplication commute with `realEmbed`.  This step is checked in
      `SCV/DistributionalEOWKernel.lean`.

   2. Define the raw fiber integral
      ```lean
      noncomputable def complexRealFiberIntegralRaw
          {m : ℕ}
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) : V :=
        ∫ t : Fin m -> ℝ, F (z, t)
      ```
      The raw definition and its apply theorem are checked in
      `SCV/DistributionalEOWKernel.lean`; the remaining work is the analytic
      package proving that this raw function is Schwartz in the `V = ℂ` case.
      The generic codomain is necessary: the first derivative of a scalar-valued
      Schwartz map is valued in a continuous-linear-map space, and the induction
      for smoothness/decay integrates those derivative fields fiberwise.

   3. Prove pointwise integrability of every fiber:
      ```lean
      lemma integrable_complexRealFiber
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) :
          Integrable (fun t : Fin m -> ℝ => F (z, t))
      ```
      This lemma is checked.  Its proof applies mathlib's
      `integrable_of_le_of_pow_mul_le` to
      `f t := F (z,t)` with the temperate-growth measure `volume` on
      `Fin m -> ℝ`.  The two required pointwise bounds are:
      ```lean
      ‖F (z,t)‖ ≤ SchwartzMap.seminorm ℝ 0 0 F
      ‖t‖ ^ volume.integrablePower * ‖F (z,t)‖ ≤
        SchwartzMap.seminorm ℝ volume.integrablePower 0 F
      ```
      The second bound uses `‖t‖ ≤ ‖(z,t)‖` for the product norm and
      `SchwartzMap.le_seminorm`.  This is the first place where the theorem-2
      docs must not hide a gap: the majorant is the standard temperate-measure
      radial tail supplied by mathlib, not a compact-support shortcut.

   4. Prove differentiation under the fiber integral:
      ```lean
      def baseFDerivSchwartz
          {m : ℕ}
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V) :
          SchwartzMap
            (ComplexChartSpace m × (Fin m -> ℝ))
            (ComplexChartSpace m ->L[ℝ] V) :=
        (SchwartzMap.postcompCLM
          ((ContinuousLinearMap.inl ℝ
            (ComplexChartSpace m) (Fin m -> ℝ)).precomp V))
          (SchwartzMap.fderivCLM ℝ
            (ComplexChartSpace m × (Fin m -> ℝ)) V F)

      theorem baseFDerivSchwartz_apply
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
          baseFDerivSchwartz F (z,t) =
            (fderiv ℝ
              (F :
                (ComplexChartSpace m × (Fin m -> ℝ)) -> V)
              (z,t)).comp
              (ContinuousLinearMap.inl ℝ
                (ComplexChartSpace m) (Fin m -> ℝ))

      lemma exists_integrable_bound_baseFDerivSchwartz
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V) :
          ∃ bound : (Fin m -> ℝ) -> ℝ,
            Integrable bound ∧
            ∀ z t, ‖baseFDerivSchwartz F (z,t)‖ ≤ bound t

      lemma hasFDerivAt_complexRealFiberIntegralRaw
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) :
          HasFDerivAt (complexRealFiberIntegralRaw F)
            (complexRealFiberIntegralRaw (baseFDerivSchwartz F) z)
            z
      ```
      The definition and apply theorem for `baseFDerivSchwartz` are checked.
      The uniform bound `exists_integrable_bound_baseFDerivSchwartz` and the
      derivative theorem `hasFDerivAt_complexRealFiberIntegralRaw` are also
      checked.

      The product-inclusion CLM is exactly
      `ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m -> ℝ)`, and
      `.precomp V` is the continuous linear map
      `(ComplexChartSpace m × (Fin m -> ℝ) ->L[ℝ] V) ->L[ℝ]
       (ComplexChartSpace m ->L[ℝ] V)`.

      The dominated-convergence call should instantiate
      `hasFDerivAt_integral_of_dominated_of_fderiv_le` with
      ```lean
      α  := Fin m -> ℝ
      H  := ComplexChartSpace m
      E  := V
      s  := Set.univ
      F  := fun z' t => F (z', t)
      F' := fun z' t => baseFDerivSchwartz F (z', t)
      ```
      The term `hF_int` is exactly `integrable_complexRealFiber F z`;
      `hF'_meas` follows from `integrable_complexRealFiber
      (baseFDerivSchwartz F) z`; `h_bound` and `bound_integrable` are supplied
      by `exists_integrable_bound_baseFDerivSchwartz`; and `h_diff` is the
      chain rule for the map `z' ↦ F (z',t)` through
      `ContinuousLinearMap.inl`.  This is the direct product-space analogue of
      `SliceIntegral.hasFDerivAt_sliceIntegralRaw`, but with the head/tail CLM
      replaced by `ContinuousLinearMap.inl`.

   5. Bootstrap to smoothness and decay:
      ```lean
      theorem fderiv_complexRealFiberIntegralRaw_eq
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V) :
          fderiv ℝ (complexRealFiberIntegralRaw F) =
            complexRealFiberIntegralRaw (baseFDerivSchwartz F)

      theorem contDiff_complexRealFiberIntegralRaw :
          ContDiff ℝ ⊤ (complexRealFiberIntegralRaw F)

      theorem exists_norm_pow_mul_complexRealFiberIntegralRaw_le
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (k : ℕ) :
          ∃ C, ∀ z,
            ‖z‖ ^ k * ‖complexRealFiberIntegralRaw F z‖ ≤ C

      theorem decay_complexRealFiberIntegralRaw :
          ∀ k n, ∃ C, ∀ z,
            ‖z‖ ^ k *
              ‖iteratedFDeriv ℝ n
                (complexRealFiberIntegralRaw F) z‖ ≤ C
      ```
      The `fderiv` equality and smoothness theorems are checked.  The `fderiv`
      equality is `hasFDerivAt_complexRealFiberIntegralRaw F z` plus
      extensionality of `fderiv`.  Smoothness follows by the same successor step as
      `SliceIntegral.contDiff_nat_sliceIntegralRaw`: apply
      `contDiff_succ_iff_hasFDerivAt`, use the derivative theorem at every
      point, and recurse on `baseFDerivSchwartz F`, whose codomain is again a
      complete real normed space.

      Zeroth-order decay is not a new theorem: apply
      `integral_pow_mul_le_of_le_of_pow_mul_le` to the fiber function
      `t ↦ (‖z‖ ^ k : ℝ) • F (z,t)`.  The required two bounds are
      `‖z‖^k * ‖F(z,t)‖ ≤ seminorm k 0 F` and
      `‖t‖^volume.integrablePower * (‖z‖^k * ‖F(z,t)‖) ≤
       seminorm (k + volume.integrablePower) 0 F`, both from
      `‖z‖ ≤ ‖(z,t)‖`, `‖t‖ ≤ ‖(z,t)‖`, and
      `SchwartzMap.le_seminorm`.  This theorem is checked as
      `exists_norm_pow_mul_complexRealFiberIntegralRaw_le`.

      Higher-order decay is the induction used in
      `SliceIntegral.decay_sliceIntegralRaw`: for `n+1`, rewrite
      `iteratedFDeriv ℝ (n+1)` as `iteratedFDeriv ℝ n` of the `fderiv`,
      replace the `fderiv` by
      `complexRealFiberIntegralRaw (baseFDerivSchwartz F)` using
      `fderiv_complexRealFiberIntegralRaw_eq`, and apply the induction
      hypothesis to `baseFDerivSchwartz F`.

   6. Package the Schwartz map:
      ```lean
      noncomputable def complexRealFiberIntegral
          {m : ℕ}
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
          SchwartzMap (ComplexChartSpace m) ℂ where
        toFun := complexRealFiberIntegralRaw F
        smooth' := contDiff_complexRealFiberIntegralRaw F
        decay' := decay_complexRealFiberIntegralRaw F
      ```

   7. Define `realConvolutionTest` by pulling the tensor product through the
      shear and then integrating out the real fiber:
      ```lean
      noncomputable def realConvolutionTest
          {m : ℕ}
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap (ComplexChartSpace m) ℂ :=
        complexRealFiberIntegral
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realConvolutionShearCLE m))
            (schwartzTensorProduct₂ φ ψ))
      ```
      This definition and its apply theorem are checked in
      `SCV/DistributionalEOWKernel.lean`; the checked apply theorem reduces by
      simp to `∫ t, φ (z - realEmbed t) * ψ t`.  This fixes the sign convention
      used later in `ProductKernelRealTranslationCovariantGlobal` and its local
      cutoff corollary.

   8. Prove the exact translation identity consumed by the descent layer:
      ```lean
      theorem realConvolutionTest_complexTranslate_eq_translateSchwartz
          (a : Fin m -> ℝ)
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
          realConvolutionTest (complexTranslateSchwartz a φ) ψ =
            realConvolutionTest φ (translateSchwartz a ψ)
      ```
      The proof is the Haar/Lebesgue change of variables
      `t ↦ t + a` in the real fiber:
      rewrite the left integral by
      `integral_add_right_eq_self a`, then simplify
      `realEmbed (t + a) = realEmbed t + realEmbed a`.  This identity is not a
      wrapper: it is the sign-sensitive algebraic bridge that makes the
      covariance hypothesis
      `K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
       K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))`
      compatible with the quotient map
      `(φ, ψ) ↦ realConvolutionTest φ ψ`.
3. The proof transcript for `regularizedEnvelope_kernelRecovery` is fixed:
   build the cutoff CLM; prove value CLMs by continuous-EOW uniqueness; prove
   translation covariance by identity theorem/uniqueness; apply the pure
   two-space Schwartz-kernel theorem `schwartzKernel₂_extension`; descend the
   translation-covariant product kernel by
   `translationCovariantProductKernel_descends`; use distributional
   Cauchy-Riemann regularity to get a holomorphic function; then apply the
   approximate identity theorem already present in
   `SCV/DistributionalUniqueness.lean`.

Detailed kernel-recovery proof transcript:

1. For compactly supported complex-chart tests `φ` with
   `tsupport φ ⊆ Ucore` and real kernels `ψ`, define the bilinear pairing
   ```lean
   regularizedEnvelopeBilinear φ ψ :=
     ∫ z : ComplexChartSpace m, G (cutoffKernelCLM χ hχ_temp ψ) z * φ z
   ```
   The support condition on `φ` keeps the integral inside `Ucore`.
2. Prove `regularizedEnvelopeBilinear` is separately continuous:
   continuity in `ψ` uses `regularizedEnvelope_valueCLM_of_cutoff` plus
   integration against the compactly supported `φ`; continuity in `φ` uses
   holomorphy/continuity of `G (χr • ψ)` on compact subsets of `Ucore`.
3. Promote the separately continuous bilinear map to the product-kernel
   distribution:
   ```lean
   lemma regularizedEnvelope_productKernel
       :
       ∃ K :
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
             K (schwartzTensorProduct₂ φ ψ) =
               regularizedEnvelopeBilinear φ ψ
   ```
   Do not use the existing homogeneous `SchwartzMap.productTensor ![φ, ψ]`
   here: that API tensors functions on repeated copies of one space.  The EOW
   kernel is on `ComplexChartSpace m × (Fin m -> ℝ)`, so the implementation
   needs the two-space tensor product `schwartzTensorProduct₂`.
4. Prove product-kernel translation covariance.  The covariance identity for
   `G` gives, after changing variables in the compactly supported `φ`
   integral,
   ```lean
   K((complexTranslateSchwartz a φ)(z), ψ(t)) =
     K(φ(z), (translateSchwartz a ψ)(t))
   ```
   with the exact signs matching `translateSchwartz a ψ x = ψ (x + a)`.
5. Descend the product kernel to a diagonal complex distribution:
   ```lean
   def ProductKernelRealTranslationCovariantGlobal
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       Prop :=
     ∀ a φ ψ,
       K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
         K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

   theorem translationCovariantProductKernel_descends
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```
   Here `realConvolutionTest φ ψ` is the complex-chart Schwartz test
   `z ↦ ∫ t, φ (z - realEmbed t) * ψ t`.  This is the precise Lean object
   replacing the informal phrase "the kernel depends only on `z + t`."

   The local/support-restricted theorem used by the regularized envelope should
   be a corollary of this global descent applied after the fixed cutoff
   `χr = 1` on the allowed kernel-support ball.  Do not use the older
   support-restricted predicate as the direct input for a global `Hdist`;
   that hides a density gap.  The implementation should first prove the global
   pure-SCV descent theorem, then add the local envelope corollary with
   `SupportsInOpen` and `KernelSupportWithin` hypotheses.

Exact product-kernel/descent subpackage:

1. The product-kernel theorem is a mixed two-space Schwartz kernel theorem,
   not the QFT-facing Wightman axiom:
   ```lean
   theorem schwartzKernel₂_extension
       {m : ℕ}
       (B : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         (SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)) :
       ∃! K :
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ, K (schwartzTensorProduct₂ φ ψ) = B φ ψ
   ```
   The proof obligations are:
   - product tensors are dense in the mixed product Schwartz space;
   - the separately continuous bilinear map `B` gives a continuous functional
     on the completed projective tensor product;
   - nuclearity of the two Schwartz spaces identifies the completed projective
     tensor product with the concrete mixed product Schwartz space;
   - uniqueness is exactly agreement on `schwartzTensorProduct₂` product tests.
   This is the pure-SCV analogue of the existing Wightman
   `schwartz_nuclear_extension` axiom, but it must not import that axiom.

2. Convert product covariance into fiber-translation invariance by shearing:
   ```lean
   noncomputable def complexRealFiberTranslateSchwartzCLM
       {m : ℕ} (a : Fin m -> ℝ) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
     SchwartzMap.compSubConstCLM ℂ ((0 : ComplexChartSpace m), -a)

   theorem complexRealFiberTranslateSchwartzCLM_apply
       (a : Fin m -> ℝ)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       complexRealFiberTranslateSchwartzCLM a F (z,t) = F (z, t + a)

   theorem complexRealFiberIntegral_fiberTranslate
       (a : Fin m -> ℝ)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       complexRealFiberIntegral (complexRealFiberTranslateSchwartzCLM a F) =
         complexRealFiberIntegral F

   theorem complexRealFiberIntegral_schwartzTensorProduct₂
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       complexRealFiberIntegral (schwartzTensorProduct₂ φ ψ) =
         (∫ t : Fin m -> ℝ, ψ t) • φ

   theorem translateSchwartz_translateSchwartz
       (a b : Fin m -> ℝ) (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       translateSchwartz a (translateSchwartz b ψ) =
         translateSchwartz (a + b) ψ

   theorem complexTranslateSchwartz_complexTranslateSchwartz
       (a b : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexTranslateSchwartz a (complexTranslateSchwartz b φ) =
         complexTranslateSchwartz (a + b) φ

   noncomputable def shearedProductKernelFunctional
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ :=
     K.comp
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (realConvolutionShearCLE m).symm)

   def IsComplexRealFiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       Prop :=
     ∀ a, T.comp (complexRealFiberTranslateSchwartzCLM a) = T

   theorem shearedProductKernel_fiberInvariant_of_productCovariant
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       IsComplexRealFiberTranslationInvariant
         (shearedProductKernelFunctional K)

   theorem complexRealFiberTranslate_shearedTensor_eq
       (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       complexRealFiberTranslateSchwartzCLM a
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ φ ψ)) =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂
             (complexTranslateSchwartz (-a) φ)
             (translateSchwartz a ψ))
   ```
   The proof first checks the equality on tensors
   `(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
    (schwartzTensorProduct₂ φ ψ)`, where the already checked identity
   `realConvolutionTest_complexTranslate_eq_translateSchwartz` fixes the sign.
   Then uniqueness/density from `schwartzKernel₂_extension` promotes the
   tensor equality to CLM equality on the full mixed Schwartz space.

   The tensor-level covariance consequence is a separate checked theorem and
   should be implemented before the density theorem:

   ```lean
   theorem translateSchwartz_zero
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       translateSchwartz (0 : Fin m -> ℝ) ψ = ψ

   theorem shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       shearedProductKernelFunctional K
         (complexRealFiberTranslateSchwartzCLM a
           ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
               (realConvolutionShearCLE m))
             (schwartzTensorProduct₂ φ ψ))) =
       shearedProductKernelFunctional K
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ φ ψ))
   ```

   Lean proof transcript:

   ```lean
   rw [complexRealFiberTranslate_shearedTensor_eq]
   simp [shearedProductKernelFunctional, ContinuousLinearMap.comp_apply]
   have h := hcov (-a) φ (translateSchwartz a ψ)
   simpa [translateSchwartz_translateSchwartz] using h
   ```

   This theorem is not a substitute for
   `shearedProductKernel_fiberInvariant_of_productCovariant`; it proves exactly
   the sign-sensitive covariance calculation on the product-tensor generators.
   The remaining step is density/uniqueness: if two continuous functionals on
   the mixed product Schwartz space agree on the span of these sheared product
   tensors, then they agree everywhere.  That is precisely where
   `schwartzKernel₂_extension` or the equivalent dense-span theorem is needed.

   The dense-span promotion layer should be implemented as an honest
   conditional theorem before the full nuclear/kernel theorem is proved:

   ```lean
   def shearedProductTensorSet (m : ℕ) :
       Set (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     {F | ∃ φ ψ,
       F =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ φ ψ)}

   def shearedProductTensorSpan (m : ℕ) :
       Submodule ℂ
         (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     Submodule.span ℂ (shearedProductTensorSet m)

   def ShearedProductTensorDense (m : ℕ) : Prop :=
     Dense ((shearedProductTensorSpan m : Set
       (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ))

   theorem shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense
       (hdense : ShearedProductTensorDense m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       IsComplexRealFiberTranslationInvariant
         (shearedProductKernelFunctional K)
   ```

   Proof transcript:

   ```lean
   intro a
   let L₁ :=
     (shearedProductKernelFunctional K).comp
       (complexRealFiberTranslateSchwartzCLM a)
   let L₂ := shearedProductKernelFunctional K

   have hspan : ∀ F ∈ shearedProductTensorSpan m, L₁ F = L₂ F := by
     intro F hF
     refine Submodule.span_induction ?gen ?zero ?add ?smul hF
     · intro G hG
       rcases hG with ⟨φ, ψ, rfl⟩
       exact
         shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant
           K hcov a φ ψ
     · simp [L₁, L₂]
     · intro u v _ _ hu hv
       simpa [L₁, L₂] using congrArg₂ (fun x y => x + y) hu hv
     · intro c u _ hu
       simpa [L₁, L₂] using congrArg (fun x => c • x) hu

   exact continuousLinearMap_eq_of_eq_on_dense L₁ L₂ hdense hspan
   ```

   Here `continuousLinearMap_eq_of_eq_on_dense` is the standard closed-equalizer
   argument: `{F | L₁ F = L₂ F}` is closed because both maps are continuous, it
   contains the dense sheared product-tensor span, hence it is all of the mixed
   Schwartz space.  This theorem shrinks the remaining analytic blocker to the
   single dense-span theorem `ShearedProductTensorDense m`.

   With the checked normalized fiber factorization, the corresponding
   conditional product-kernel descent is also 100% Lean-ready:

   ```lean
   theorem translationCovariantProductKernel_descends_of_shearedProductTensorDense
       (hdense : ShearedProductTensorDense m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη : ∫ t : Fin m -> ℝ, η t = 1) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```

   Proof transcript:

   ```lean
   let T := shearedProductKernelFunctional K
   let Hdist := complexRealFiberTranslationDescentCLM T η
   have hT : IsComplexRealFiberTranslationInvariant T :=
     shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense
       hdense K hcov

   refine ⟨Hdist, ?_⟩
   intro φ ψ
   let F :=
     (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m))
       (schwartzTensorProduct₂ φ ψ)
   have hfac :=
     map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant
       T hT η hη F
   simpa [T, Hdist, F, realConvolutionTest, shearedProductKernelFunctional,
     ContinuousLinearMap.comp_apply] using hfac
   ```

   This is not the final unqualified
   `translationCovariantProductKernel_descends`: it retains the dense-span
   hypothesis explicitly.  The unqualified theorem follows only after proving
   `ShearedProductTensorDense m`, equivalently the mixed two-space
   `schwartzKernel₂_extension`/product-density theorem.

   The conditional promotion/descent package is now checked in
   `SCV/DistributionalEOWProductKernel.lean`.  The remaining unproved theorem
   at this layer is exactly `ShearedProductTensorDense m` (or the stronger
   `schwartzKernel₂_extension` from which it follows).

   The checked coordinate-transport reduction is the pure shear part of that
   blocker.  It does **not** prove the Schwartz nuclear/product theorem; it
   proves that the sheared dense-span hypothesis follows from the standard
   unsheared product-tensor dense-span theorem by applying the checked shear
   continuous linear equivalence:

   ```lean
   def productTensorSet (m : ℕ) :
       Set (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     {F | ∃ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
         (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
       F = schwartzTensorProduct₂ φ ψ}

   def productTensorSpan (m : ℕ) :
       Submodule ℂ
         (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     Submodule.span ℂ (productTensorSet m)

   def ProductTensorDense (m : ℕ) : Prop :=
     Dense ((productTensorSpan m : Set
       (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)))
   ```

   The image comparison is exact:

   ```lean
   theorem shearedProductTensorSet_eq_image_productTensorSet :
       shearedProductTensorSet m =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (realConvolutionShearCLE m)) '' productTensorSet m

   theorem shearedProductTensorSpan_eq_productTensorSpan_map :
       shearedProductTensorSpan m =
         (productTensorSpan m).map
           ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m) :
               SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
                 SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ).toLinearMap)
   ```

   Lean proof transcript:

   ```lean
   -- set image
   ext F
   constructor
   · rintro ⟨φ, ψ, rfl⟩
     exact ⟨schwartzTensorProduct₂ φ ψ, ⟨φ, ψ, rfl⟩, rfl⟩
   · rintro ⟨G, ⟨φ, ψ, rfl⟩, rfl⟩
     exact ⟨φ, ψ, rfl⟩

   -- span image
   rw [shearedProductTensorSpan, productTensorSpan,
     shearedProductTensorSet_eq_image_productTensorSet,
     Submodule.map_span]
   rfl
   ```

   The density transport theorem is:

   ```lean
   theorem shearedProductTensorDense_of_productTensorDense
       (hdense : ProductTensorDense m) :
       ShearedProductTensorDense m
   ```

   Proof transcript:

   ```lean
   change Dense ((productTensorSpan m : Set
     (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ))) at hdense
   change Dense ((shearedProductTensorSpan m : Set
     (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)))
   rw [Submodule.dense_iff_topologicalClosure_eq_top] at hdense ⊢
   let shear : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m)
   have hsurj : Function.Surjective shear := by
     intro F
     refine ⟨(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m).symm) F, ?_⟩
     change shear ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m).symm) F) = F
     exact compCLMOfContinuousLinearEquiv_symm_left_inv
       (e := realConvolutionShearCLE m) F
   have hmap_dense :
       (((productTensorSpan m).map shear.toLinearMap).topologicalClosure) = ⊤ := by
     exact hsurj.denseRange.topologicalClosure_map_submodule
       (f := shear) hdense
   rw [shearedProductTensorSpan_eq_productTensorSpan_map]
   exact hmap_dense
   ```

   The corresponding consumer-facing corollary can now expose the standard
   unsheared density blocker directly:

   ```lean
   theorem translationCovariantProductKernel_descends_of_productTensorDense
       (hdense : ProductTensorDense m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη : ∫ t : Fin m -> ℝ, η t = 1) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```

   This is a strict reduction of the live blocker: after this checked transport
   step, the remaining mathematical theorem is the standard QFT-free statement
   `ProductTensorDense m`, equivalent to the mixed two-space Schwartz
   kernel/product-density theorem.  No Wightman import or existing Wightman
   nuclear axiom is used in this SCV layer.

   The remaining product-density theorem is now Lean-planned through the
   pure GaussianField product-Hermite density theorem, not through the Wightman
   nuclear axiom.  The route is:

   1. add a pure-SCV complex Schwartz decomposition file, with no Wightman
      imports:

      ```lean
      def SCV.schwartzRealPartCLM :
          SchwartzMap D ℂ ->L[ℝ] SchwartzMap D ℝ

      def SCV.schwartzImagPartCLM :
          SchwartzMap D ℂ ->L[ℝ] SchwartzMap D ℝ

      def SCV.schwartzOfRealCLM :
          SchwartzMap D ℝ ->L[ℝ] SchwartzMap D ℂ

      def SCV.complexSchwartzDecomposeCLE :
          SchwartzMap D ℂ ≃L[ℝ]
            (SchwartzMap D ℝ × SchwartzMap D ℝ)
      ```

      Proof transcript: copy the real/imaginary estimates from the local
      Wightman `ComplexSchwartz.lean` source pattern, but place them in
      `OSReconstruction/SCV/ComplexSchwartz.lean` importing only Mathlib/SCV
      prerequisites.  `realPartCLM` and `imagPartCLM` use
      `SchwartzMap.mkCLM` and
      `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`; `ofRealCLM` uses
      `Complex.ofRealLI.norm_iteratedFDeriv_comp_left`.  The equivalence is
      `ContinuousLinearEquiv.equivOfInverse` with pointwise proof
      `Complex.re_add_im`.

   2. flatten the mixed chart in the existing fiber-first order:

      ```lean
      def flatMixedCLM (m : ℕ) :
          SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ]
            SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mixedChartFiberFirstCLE m)

      def flattenMixedFunctional (m : ℕ)
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
          SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ] ℂ :=
        L.comp (flatMixedCLM m)
      ```

      Here `mixedChartFiberFirstCLE m (z,t) = Fin.append t
      (complexChartRealFlattenCLE m z)`, already checked as
      `mixedChartFiberFirstCLE_apply_finAppend`.  This exact order matters:
      the first `m` real coordinates are the real fiber and the last `m*2`
      real coordinates are the real/imaginary complex-chart coordinates.

   3. expose the generic external product and prove the pointwise bridge from
      flat two-block products to mixed `schwartzTensorProduct₂` tests:

      ```lean
      def schwartzExternalProduct
          {E₁ E₂ : Type*}
          [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
          [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
          (φ : SchwartzMap E₁ ℂ) (ψ : SchwartzMap E₂ ℂ) :
          SchwartzMap (E₁ × E₂) ℂ

      def twoBlockProductSchwartz {m n : ℕ}
          (B : SchwartzMap (Fin m -> ℝ) ℂ)
          (A : SchwartzMap (Fin n -> ℝ) ℂ) :
          SchwartzMap (Fin (m + n) -> ℝ) ℂ :=
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finAppendCLE m n).symm)
          (schwartzExternalProduct B A)

      theorem flatTwoBlockProduct_eq_mixedProduct
          {m : ℕ}
          (A : SchwartzMap (Fin (m * 2) -> ℝ) ℂ)
          (B : SchwartzMap (Fin m -> ℝ) ℂ) :
          (flatMixedCLM m)
            (twoBlockProductSchwartz (m := m) (n := m * 2) B A) =
          schwartzTensorProduct₂
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (complexChartRealFlattenCLE m)) A)
            B
      ```

      `SCV.schwartzExternalProduct` is the checked local product estimate for
      `(x,y) ↦ φ x * ψ y`, and `twoBlockProductSchwartz B A` pulls it back to
      the flat append domain.  The bridge proof is pointwise:

      ```lean
      ext p
      rcases p with ⟨z,t⟩
      simp [flatMixedCLM, twoBlockProductSchwartz,
        schwartzTensorProduct₂_apply,
        mixedChartFiberFirstCLE_apply_finAppend,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      ring
      ```

      This slice is now implemented in
      `OSReconstruction/SCV/SchwartzExternalProduct.lean` and
      `OSReconstruction/SCV/ProductDensity.lean`.

   4. consume GaussianField's checked one-dimensional product-Hermite theorem
      on the flat real domain.  For `0 < m`, set `N := m + m * 2` and apply

      ```lean
      GaussianField.productHermite_schwartz_dense
        (D := ℝ) N (by omega)
      ```

      to any real continuous linear functional on
      `SchwartzMap (Fin N -> ℝ) ℝ`.  The hypothesis required by that theorem is
      vanishing on functions of the form
      `fun x => ∏ i : Fin N, DyninMityaginSpace.basis (ks i) (x i)`.
      To get that hypothesis from vanishing on mixed two-block product tests,
      split the one-dimensional Hermite product into the fiber block and the
      complex-chart block:

      ```lean
      have hsplit :
          fullHermiteProduct ks =
            twoBlockProductSchwartz
              (fiberHermiteProduct (fun i : Fin m => ks (Fin.castAdd (m*2) i)))
              (chartHermiteProduct
                (fun j : Fin (m*2) => ks (Fin.natAdd m j))) := by
        ext x
        rw [Fin.prod_univ_add]
        simp [twoBlockProductSchwartz, fiberHermiteProduct,
          chartHermiteProduct]
        ring
      ```

      `fiberHermiteProduct` and `chartHermiteProduct` are built by
      `GaussianField.schwartzProductTensor_schwartz (D := ℝ)` for the
      positive dimensions `m` and `m*2`; for `m = 0`, use the zero-dimensional
      base case below instead of this product-Hermite split.

   5. prove complex flat functional uniqueness from the real product-Hermite
      theorem:

      ```lean
      theorem flatComplexCLM_zero_of_zero_on_twoBlockProducts
          {m : ℕ} (hm : 0 < m)
          (Lflat : SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ] ℂ)
          (hL : ∀ A B,
            Lflat (twoBlockProductSchwartz (m := m) (n := m * 2) B A) = 0) :
          Lflat = 0
      ```

      Proof transcript:

      ```lean
      let Lre : SchwartzMap (Fin (m + m*2) -> ℝ) ℝ ->L[ℝ] ℝ :=
        Complex.reCLM.comp
          ((Lflat.restrictScalars ℝ).comp SCV.schwartzOfRealCLM)
      let Lim : SchwartzMap (Fin (m + m*2) -> ℝ) ℝ ->L[ℝ] ℝ :=
        Complex.imCLM.comp
          ((Lflat.restrictScalars ℝ).comp SCV.schwartzOfRealCLM)
      have hre : Lre = 0 := by
        apply GaussianField.productHermite_schwartz_dense
        intro ks F hF
        -- split F into fiber/chart Hermite products and use hL
      have him : Lim = 0 := by
        apply GaussianField.productHermite_schwartz_dense
        intro ks F hF
        -- same split
      ext F
      let R := (SCV.complexSchwartzDecomposeCLE F).1
      let I := (SCV.complexSchwartzDecomposeCLE F).2
      have hdecomp :
          F = SCV.schwartzOfRealCLM R +
            (Complex.I : ℂ) • SCV.schwartzOfRealCLM I := by
        exact (SCV.complexSchwartzDecomposeCLE.symm_apply_apply F).symm
      have hR : Lflat (SCV.schwartzOfRealCLM R) = 0 := by
        apply Complex.ext
        · change Lre R = 0
          rw [hre]
          rfl
        · change Lim R = 0
          rw [him]
          rfl
      have hI : Lflat (SCV.schwartzOfRealCLM I) = 0 := by
        apply Complex.ext
        · change Lre I = 0
          rw [hre]
          rfl
        · change Lim I = 0
          rw [him]
          rfl
      rw [hdecomp, map_add, map_smul, hR, hI]
      simp
      ```

      The only nontrivial local lemma in this transcript is the `hsplit`
      block-product identity from step 4.

   6. pull the flat uniqueness back to the mixed chart:

      ```lean
      theorem mixedProductCLM_zero_of_zero_on_productTensor
          {m : ℕ} (hm : 0 < m)
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
          (hL : ∀ φ ψ, L (schwartzTensorProduct₂ φ ψ) = 0) :
          L = 0 := by
        have hflat :
            flattenMixedFunctional m L = 0 :=
          flatComplexCLM_zero_of_zero_on_twoBlockProducts hm
            (flattenMixedFunctional m L) (by
              intro A B
              rw [flatTwoBlockProduct_eq_mixedProduct]
              exact hL _ _)
        ext F
        have hinv :
            (flatMixedCLM m)
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (mixedChartFiberFirstCLE m).symm) F) = F :=
          compCLMOfContinuousLinearEquiv_symm_left_inv
            (e := mixedChartFiberFirstCLE m) F
        simpa [flattenMixedFunctional, hinv] using
          congrArg (fun T => T
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (mixedChartFiberFirstCLE m).symm) F)) hflat
      ```

   7. convert CLM uniqueness into topological density with the same
      Hahn-Banach argument already checked in
      `Wightman/Reconstruction/DenseCLM.lean`, but with the new pure-SCV
      uniqueness theorem:

      ```lean
      theorem ProductTensorDense_of_pos {m : ℕ} (hm : 0 < m) :
          ProductTensorDense m := by
        rw [ProductTensorDense,
          Submodule.dense_iff_topologicalClosure_eq_top]
        by_contra hM
        let M := productTensorSpan m
        obtain ⟨x, hx⟩ : ∃ x, x ∉ M.topologicalClosure := by
          -- same `Submodule.eq_top_iff'` contradiction as DenseCLM
        have hconv :
            Convex ℝ (M.topologicalClosure :
              Set (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)) := by
          simpa using (M.topologicalClosure.restrictScalars ℝ).convex
        obtain ⟨f, u, hleft, hright⟩ :=
          RCLike.geometric_hahn_banach_closed_point
            (𝕜 := ℂ) (E := SchwartzMap
              (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
            (x := x) (s := (M.topologicalClosure : Set _))
            hconv M.isClosed_topologicalClosure hx
        -- scaling by real scalars and then by `Complex.I` proves
        -- `f` vanishes on `M.topologicalClosure`, hence on `M`.
        have hf_prod : ∀ φ ψ,
            f (schwartzTensorProduct₂ φ ψ) = 0 := by
          intro φ ψ
          exact hfS _ (Submodule.subset_span ⟨φ, ψ, rfl⟩)
        have hf_zero : f = 0 :=
          mixedProductCLM_zero_of_zero_on_productTensor hm f hf_prod
        -- contradict strict separation of x from M.topologicalClosure
      ```

   8. handle `m = 0` separately.  The domain
      `ComplexChartSpace 0 × (Fin 0 -> ℝ)` is a singleton finite-dimensional
      real normed space.  The proof should use evaluation at the unique point
      and the constant-one product tensor:

      ```lean
      theorem ProductTensorDense_zero : ProductTensorDense 0 := by
        -- show every Schwartz function on the singleton is a scalar multiple
        -- of `schwartzTensorProduct₂ 1 1`, hence lies in `productTensorSpan 0`

      theorem ProductTensorDense_all (m : ℕ) : ProductTensorDense m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact ProductTensorDense_zero
        · exact ProductTensorDense_of_pos hm
      ```

      This base case must be proved directly and should not be hidden behind
      GaussianField's positive-dimensional product theorem, whose hypotheses
      require `1 ≤ n`.

      This product-density route is now implemented in
      `OSReconstruction/SCV/ProductDensity.lean`.  The checked declarations are:

      ```lean
      def SCV.realHermiteBasis
      def SCV.singletonConstantSchwartz
      def SCV.flatMixedCLM
      def SCV.flattenMixedFunctional
      def SCV.twoBlockProductSchwartz
      theorem SCV.schwartzOfRealCLM_eq_twoBlockProduct_of_forall_append
      theorem SCV.exists_hermite_twoBlockFactors
      theorem SCV.flatTwoBlockProduct_eq_mixedProduct
      theorem SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts
      theorem SCV.mixedProductCLM_zero_of_zero_on_productTensor
      theorem SCV.ProductTensorDense_of_pos
      theorem SCV.ProductTensorDense_zero
      theorem SCV.ProductTensorDense_all
      theorem SCV.translationCovariantProductKernel_descends
      ```

      The proof uses `GaussianField.productHermite_schwartz_dense` only after
      building the exact Hermite split bridge from full flat products to the
      two mixed blocks, and it imports no Wightman nuclear theorem.

   Lean proof details for the checked first slice of this step:

   - `complexRealFiberTranslateSchwartzCLM` should not reprove a custom affine
     temperate-growth lemma.  Mathlib already supplies
     `SchwartzMap.compSubConstCLM`, so the fiber translation is the pullback by
     subtracting the constant `(0,-a)` in the product space:
     `F (p - (0,-a)) = F (z,t+a)`.
   - The apply theorem is one `simp` after unfolding the definition.
   - `complexRealFiberIntegral_fiberTranslate` is exactly invariance of
     Lebesgue/Haar measure under addition:
     ```lean
     ext z
     simp [complexRealFiberIntegral_apply]
     simpa using
       (MeasureTheory.integral_add_right_eq_self
         (μ := (volume : Measure (Fin m -> ℝ)))
         (fun t : Fin m -> ℝ => F (z,t)) a)
     ```
   - `complexRealFiberIntegral_schwartzTensorProduct₂` is the normalized-tensor
     computation used later to define the descent map with a fixed real cutoff:
     ```lean
     ext z
     simp [complexRealFiberIntegral_apply]
     calc
       ∫ t : Fin m -> ℝ, φ z * ψ t =
           φ z * ∫ t : Fin m -> ℝ, ψ t := by
         simpa [smul_eq_mul] using
           (integral_const_mul
             (μ := (volume : Measure (Fin m -> ℝ)))
             (r := φ z) (f := fun t : Fin m -> ℝ => ψ t))
       _ = (∫ t : Fin m -> ℝ, ψ t) * φ z := by ring
     ```

   The next tensor-level identity before the density promotion is:

   ```lean
   ext p
   rcases p with ⟨z, t⟩
   have hz : z - realEmbed (a + t) =
       z - realEmbed t + realEmbed (-a) := by
     ext i
     simp [realEmbed, sub_eq_add_neg, add_comm, add_left_comm]
   simp [hz, add_comm]
   ```

   This proves `complexRealFiberTranslate_shearedTensor_eq`.  It is the exact
   sign bridge used when applying `ProductKernelRealTranslationCovariantGlobal`
   with `-a` and then simplifying
   `translateSchwartz (-a) (translateSchwartz a ψ)` by
   `translateSchwartz_translateSchwartz`.

3. Prove the fiber-factorization theorem:
   ```lean
   noncomputable def schwartzTensorProduct₂CLMRight
       {m : ℕ} (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ

   theorem schwartzTensorProduct₂CLMRight_apply
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       schwartzTensorProduct₂CLMRight η φ (z,t) = φ z * η t

   theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (F G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
       T F = T G

   noncomputable def complexRealFiberTranslationDescentCLM
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ :=
     T.comp (schwartzTensorProduct₂CLMRight η)

   theorem map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη : ∫ t : Fin m -> ℝ, η t = 1)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       T F =
         complexRealFiberTranslationDescentCLM T η
           (complexRealFiberIntegral F)
   ```

   After `agents_chat.md` #1328, the hard quotient theorem
   `map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant` is
   checked in production.  Therefore the immediate Lean target is now the
   normalized-cutoff factorization above, not the full product-kernel descent.
   This is a genuine mathematical consumer of the quotient theorem: it
   constructs the descended continuous functional explicitly by embedding a
   complex-chart test `φ` as the product test `(z,t) ↦ φ z * η t` and uses
   `∫ η = 1` to identify its fiber integral with `φ`.

   The exact implementation route is:

   ```lean
   theorem schwartzTensorProduct₂_add_left
       (φ φ' : SchwartzMap (ComplexChartSpace m) ℂ)
       (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       schwartzTensorProduct₂ (φ + φ') η =
         schwartzTensorProduct₂ φ η + schwartzTensorProduct₂ φ' η

   theorem schwartzTensorProduct₂_smul_left
       (c : ℂ) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       schwartzTensorProduct₂ (c • φ) η =
         c • schwartzTensorProduct₂ φ η

   theorem schwartzTensorProduct₂CLMRight_eq
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       schwartzTensorProduct₂CLMRight η φ =
         schwartzTensorProduct₂ φ η
   ```

   The continuity proof for `schwartzTensorProduct₂CLMRight` is the product
   Schwartz seminorm estimate specialized to a fixed right factor.  For every
   output seminorm `(p,l)`, use

   ```lean
   s =
     (Finset.range (l + 1)).image (fun i => (p,i)) ∪
     (Finset.range (l + 1)).image (fun i => (0,i))

   C =
     (2 : ℝ) ^ p *
       ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
         (SchwartzMap.seminorm ℂ 0 (l - i) η +
          SchwartzMap.seminorm ℂ p (l - i) η)
   ```

   and prove

   ```lean
   ‖x‖ ^ p *
     ‖iteratedFDeriv ℝ l (fun y => φ y.1 * η y.2) x‖
     ≤ C * (s.sup
       (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ)) φ.
   ```

   The derivative estimate is exactly the already checked product-rule
   estimate used in `schwartzTensorProductRaw`: split
   `‖x‖ ≤ ‖x.1‖ + ‖x.2‖`, use
   `(a+b)^p ≤ 2^p(a^p+b^p)`, bound the pullback derivatives through
   `ContinuousLinearMap.fst` and `ContinuousLinearMap.snd`, then absorb the
   variable `φ` seminorms into the finite sup over `s`.  The fixed `η`
   seminorms are part of `C`, so this gives a true continuous linear map, not
   a new assumption.

   The factorization proof then has no remaining mathematical gap:

   ```lean
   let G := schwartzTensorProduct₂ (complexRealFiberIntegral F) η
   have hFG :
       complexRealFiberIntegral F = complexRealFiberIntegral G := by
     rw [G, complexRealFiberIntegral_schwartzTensorProduct₂, hη, one_smul]

   have hquot :
       T F = T G :=
     map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       T hT F G hFG

   calc
     T F = T G := hquot
     _ =
       complexRealFiberTranslationDescentCLM T η
         (complexRealFiberIntegral F) := by
       simp [complexRealFiberTranslationDescentCLM,
         schwartzTensorProduct₂CLMRight_eq, G]
   ```

   This package is now checked in
   `SCV/DistributionalEOWKernelFactorization.lean`, including the fixed-right
   tensor CLM, the explicit descended CLM, and
   `map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant`.

   What this does *not* yet prove: it does not derive
   `IsComplexRealFiberTranslationInvariant (shearedProductKernelFunctional K)`
   from `ProductKernelRealTranslationCovariantGlobal K` on all mixed tests.
   The existing covariance predicate is an equality on product tensors; to
   promote it to all of `SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ`
   still requires the mixed product-tensor density/kernel-extension theorem
   `schwartzKernel₂_extension` or an equivalent uniqueness principle.  That
   density theorem is the next mathematical blocker after the normalized
   factorization is checked.

   This is the mixed chart analogue of the already checked
   `HeadBlockTranslationInvariant` factorization theorem.  The proof cannot be
   a wrapper around the Wightman file because the domain is
   `ComplexChartSpace m × (Fin m -> ℝ)`, not a pure `Fin n -> ℝ` space.
   The mathematical proof is the same:
   - fiber-translation invariance kills every real-fiber directional derivative;
   - a Schwartz function with zero real-fiber integral is a finite sum of
     real-fiber directional derivatives, using the same zero-mean/antiderivative
     construction as `SliceIntegral.lean` iterated over the `Fin m -> ℝ`
     fiber;
   - therefore `T` depends only on `complexRealFiberIntegral F`;
   - a normalized real-fiber cutoff `η` gives an explicit descended CLM by
     tensoring the base test with `η`.

   Lean-ready extraction plan for this factorization:

   The proof should be moved into a pure SCV coordinate package rather than
   imported from `Wightman/Reconstruction/HeadBlockTranslationInvariant.lean`.
   The Wightman file is a source pattern, not a dependency, because importing it
   into SCV would reverse the project layering and would also pull the
   Wightman tensor-product package into the theorem-2 SCV layer.

   The exact SCV transport objects should be the following.  The complex
   coordinates are flattened as `Fin (m * 2)`, not `Fin (2 * m)`, because the
   existing Mathlib equivalence `finProdFinEquiv : Fin m × Fin 2 ≃ Fin
   (m * 2)` is the definitional order that makes the apply lemmas `rfl`/`simp`.
   Do not insert a commuted `2 * m` target unless a separate cast equivalence is
   mathematically needed downstream.

   ```lean
   def headBlockShift (m n : ℕ) (a : Fin m -> ℝ) : Fin (m + n) -> ℝ

   theorem headBlockShift_apply_head
       (a : Fin m -> ℝ) (i : Fin m) :
       headBlockShift m n a (Fin.castAdd n i) = a i

   theorem headBlockShift_apply_tail
       (a : Fin m -> ℝ) (i : Fin n) :
       headBlockShift m n a (Fin.natAdd m i) = 0

   private def realBlockUncurryLinearEquiv (n d : ℕ) (R : Type*)
       [CommSemiring R] :
       (Fin n -> Fin d -> R) ≃ₗ[R] (Fin n × Fin d -> R)

   private def realBlockFlattenLinearEquiv (n d : ℕ) (R : Type*)
       [CommSemiring R] :
       (Fin n -> Fin d -> R) ≃ₗ[R] (Fin (n * d) -> R)

   def realBlockFlattenCLE (n d : ℕ) :
       (Fin n -> Fin d -> ℝ) ≃L[ℝ] (Fin (n * d) -> ℝ)

   theorem realBlockFlattenCLE_apply
       (f : Fin n -> Fin d -> ℝ) (k : Fin (n * d)) :
       realBlockFlattenCLE n d f k =
         f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

   theorem realBlockFlattenCLE_symm_apply
       (w : Fin (n * d) -> ℝ) (i : Fin n) (j : Fin d) :
       (realBlockFlattenCLE n d).symm w i j =
         w (finProdFinEquiv (i, j))

   noncomputable def complexToFinTwoCLE : ℂ ≃L[ℝ] (Fin 2 -> ℝ)

   theorem complexToFinTwoCLE_apply_zero (z : ℂ) :
       complexToFinTwoCLE z 0 = z.re

   theorem complexToFinTwoCLE_apply_one (z : ℂ) :
       complexToFinTwoCLE z 1 = z.im

   noncomputable def complexChartRealBlockCLE (m : ℕ) :
       ComplexChartSpace m ≃L[ℝ] (Fin m -> Fin 2 -> ℝ)

   noncomputable def complexChartRealFlattenCLE (m : ℕ) :
       ComplexChartSpace m ≃L[ℝ] (Fin (m * 2) -> ℝ)

   theorem complexChartRealFlattenCLE_apply_re
       (z : ComplexChartSpace m) (i : Fin m) :
       complexChartRealFlattenCLE m z (finProdFinEquiv (i, (0 : Fin 2))) =
         (z i).re

   theorem complexChartRealFlattenCLE_apply_im
       (z : ComplexChartSpace m) (i : Fin m) :
       complexChartRealFlattenCLE m z (finProdFinEquiv (i, (1 : Fin 2))) =
         (z i).im

   private def finAppendLinearEquiv (m n : ℕ) :
       ((Fin m -> ℝ) × (Fin n -> ℝ)) ≃ₗ[ℝ] (Fin (m + n) -> ℝ)

   noncomputable def finAppendCLE (m n : ℕ) :
       ((Fin m -> ℝ) × (Fin n -> ℝ)) ≃L[ℝ] (Fin (m + n) -> ℝ)

   theorem finAppendCLE_apply_head
       (p : (Fin m -> ℝ) × (Fin n -> ℝ)) (i : Fin m) :
       finAppendCLE m n p (Fin.castAdd n i) = p.1 i

   theorem finAppendCLE_apply_tail
       (p : (Fin m -> ℝ) × (Fin n -> ℝ)) (i : Fin n) :
       finAppendCLE m n p (Fin.natAdd m i) = p.2 i

   noncomputable def mixedChartFiberFirstCLE (m : ℕ) :
       (ComplexChartSpace m × (Fin m -> ℝ)) ≃L[ℝ]
         (Fin (m + m * 2) -> ℝ)

   theorem mixedChartFiberFirstCLE_apply_head
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) (i : Fin m) :
       mixedChartFiberFirstCLE m (z,t) (Fin.castAdd (m * 2) i) = t i

   theorem mixedChartFiberFirstCLE_apply_tail_re
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) (i : Fin m) :
       mixedChartFiberFirstCLE m (z,t)
         (Fin.natAdd m (finProdFinEquiv (i, (0 : Fin 2)))) = (z i).re

   theorem mixedChartFiberFirstCLE_apply_tail_im
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) (i : Fin m) :
       mixedChartFiberFirstCLE m (z,t)
         (Fin.natAdd m (finProdFinEquiv (i, (1 : Fin 2)))) = (z i).im

   theorem mixedChartFiberFirstCLE_symm_headBlockShift
       (a : Fin m -> ℝ) :
       (mixedChartFiberFirstCLE m).symm (headBlockShift m (m * 2) a) =
         (0, a)
   ```

   `mixedChartFiberFirstCLE` must put the real fiber in the **head block** and
   the real/imaginary coordinates of the complex chart in the tail block.  With
   this ordering, `complexRealFiberTranslateSchwartzCLM a` transports exactly
   to head-block translation by `a`:

   ```lean
   theorem mixedChartFiberFirstCLE_translate
       (a : Fin m -> ℝ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (mixedChartFiberFirstCLE m).symm).comp
         (complexRealFiberTranslateSchwartzCLM a) =
       (SCV.translateSchwartzCLM
          (headBlockShift m (m * 2) a)).comp
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mixedChartFiberFirstCLE m).symm)
   ```

   The verified proof transcript is:
   - prove `mixedChartFiberFirstCLE_symm_headBlockShift`, reducing the head
     shift under the inverse chart to `(0, a)` in
     `ComplexChartSpace m × (Fin m -> ℝ)`;
   - for a real-coordinate point `x`, set
     `y := (mixedChartFiberFirstCLE m).symm x`;
   - use linearity of `(mixedChartFiberFirstCLE m).symm` to rewrite
     `(mixedChartFiberFirstCLE m).symm (x + headBlockShift m (m * 2) a)` as
     `y + (0, a)`;
   - case-split `y = (z,t)` and reduce both sides by `simp` to
     `F (z, t + a)`.

   Here `headBlockShift` is the pure-SCV extraction of the existing
   `zeroTailBlockShift` idea: the first `m` coordinates are `a`, and the final
   `n` coordinates are zero.  Extract this definition and its apply lemmas into
   the SCV package; do not import the Wightman file that currently contains the
   source-pattern version.

   The transported fiber integral must also be an exact theorem, not an
   informal identification:

   ```lean
   -- in namespace SCV, after extracting the QFT-free block-integration
   -- machinery out of the Wightman namespace
   theorem complexRealFiberIntegral_eq_transport_integrateHeadBlock
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       complexRealFiberIntegral F =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (complexChartRealFlattenCLE m))
           (integrateHeadBlock (m := m) (n := m * 2)
             ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
               (mixedChartFiberFirstCLE m).symm) F))
   ```

   The proof is Fubini-free: both sides are the same single integral over the
   real fiber after expanding `mixedChartFiberFirstCLE`; the finite-dimensional
   linear equivalence only reorders the non-integrated real coordinates.
   The outer chart transport uses `complexChartRealFlattenCLE m`, not its
   inverse: `compCLMOfContinuousLinearEquiv ℂ (complexChartRealFlattenCLE m)`
   has type
   `SchwartzMap (Fin (m * 2) -> ℝ) ℂ ->L[ℂ]
    SchwartzMap (ComplexChartSpace m) ℂ`.

   Because `DistributionalEOWKernel.lean` is now above 1000 lines and is
   sorry-free, Stage 3.1+ implementation should not continue growing that file.
   The next implementation file should be a pure-SCV companion:

   ```lean
   -- OSReconstruction/SCV/HeadBlockIntegral.lean
   import OSReconstruction.SCV.DistributionalEOWKernel

   namespace SCV

   def realFiberIntegralRaw
       (F : SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ)) V)
       (u : Fin n -> ℝ) : V :=
     ∫ t : Fin m -> ℝ, F (u, t)

   def realFiberBaseFDerivSchwartz
       (F : SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ)) V) :
       SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ))
         ((Fin n -> ℝ) ->L[ℝ] V)

   def realFiberIntegral
       (F : SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ)) ℂ) :
       SchwartzMap (Fin n -> ℝ) ℂ

   def headTailAppendCLE (m n : ℕ) :
       ((Fin n -> ℝ) × (Fin m -> ℝ)) ≃L[ℝ] (Fin (m + n) -> ℝ)

   theorem headTailAppendCLE_apply
       (u : Fin n -> ℝ) (t : Fin m -> ℝ) :
       headTailAppendCLE m n (u, t) = Fin.append t u

   noncomputable def integrateHeadBlock :
       SchwartzMap (Fin (m + n) -> ℝ) ℂ ->
       SchwartzMap (Fin n -> ℝ) ℂ

   theorem integrateHeadBlock_apply_finAppend
       (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ) (u : Fin n -> ℝ) :
       integrateHeadBlock (m := m) (n := n) F u =
         ∫ t : Fin m -> ℝ, F (Fin.append t u)

   end SCV
   ```

   The checked implementation uses the direct finite-dimensional real fiber
   integral rather than the older recursive `sliceIntegral` source pattern.
   This is mathematically the same head-block integral, but the theorem needed
   by the mixed-chart transport is Fubini-free:
   `integrateHeadBlock F u` is definitionally the integral of `F` over
   `Fin.append t u` after the continuous-linear equivalence
   `headTailAppendCLE m n`.

   `HeadBlockIntegral.lean` is extracted by adapting the QFT-free Schwartz
   estimates already checked for `complexRealFiberIntegral` in
   `SCV/DistributionalEOWKernel.lean`: fixed-fiber integrability, dominated
   differentiation under the fiber integral, smoothness, and higher derivative
   Schwartz decay.  It imports only SCV/Mathlib infrastructure.  The Wightman
   `SliceIntegral.lean` and `BlockIntegral.lean` files remain historical source
   patterns and are not imported.

   Minimal dependency ledger for `integrateHeadBlock_apply_finAppend`:

   | Lemma | Source pattern | Role |
   |---|---|---|
   | `integrable_realFiber` | adapted from `integrable_complexRealFiber` | fixed-base Bochner integrability over `Fin m -> ℝ` |
   | `realFiberBaseFDerivSchwartz` | adapted from `baseFDerivSchwartz` | base-variable derivative field for dominated differentiation |
   | `hasFDerivAt_realFiberIntegralRaw` | adapted from `hasFDerivAt_complexRealFiberIntegralRaw` | differentiating under the finite real fiber integral |
   | `decay_realFiberIntegralRaw` | adapted from `decay_complexRealFiberIntegralRaw` | Schwartz decay of all base derivatives |
   | `headTailAppendCLE_apply` | `finAppendCLE` | coordinate identity `(u,t) ↦ Fin.append t u` |
   | `integrateHeadBlock_apply_finAppend` | direct definition | public apply theorem consumed by mixed-chart transport |

   Lean proof transcript for `integrateHeadBlock_apply_finAppend`:

   ```lean
   theorem integrateHeadBlock_apply_finAppend
       (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (u : Fin n -> ℝ) :
       integrateHeadBlock (m := m) (n := n) F u =
         ∫ t : Fin m -> ℝ, F (Fin.append t u)
     simp [integrateHeadBlock,
       SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
       headTailAppendCLE_apply]
   ```

   After `integrateHeadBlock_apply_finAppend`, the transported mixed fiber
   integral proof is mechanical.  Add the following chart lemma in the file that
   imports both `HeadBlockIntegral.lean` and `DistributionalEOWKernel.lean`:

   ```lean
   -- OSReconstruction/SCV/DistributionalEOWKernelTransport.lean
   import OSReconstruction.SCV.HeadBlockIntegral
   import OSReconstruction.SCV.DistributionalEOWKernel

   namespace SCV

   theorem mixedChartFiberFirstCLE_apply_finAppend
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       mixedChartFiberFirstCLE m (z, t) =
         Fin.append t (complexChartRealFlattenCLE m z)

   theorem mixedChartFiberFirstCLE_symm_finAppend
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       (mixedChartFiberFirstCLE m).symm
         (Fin.append t (complexChartRealFlattenCLE m z)) = (z, t)

   theorem complexRealFiberIntegral_eq_transport_integrateHeadBlock
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       complexRealFiberIntegral F =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (complexChartRealFlattenCLE m))
           (integrateHeadBlock (m := m) (n := m * 2)
             ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
               (mixedChartFiberFirstCLE m).symm) F))
   ```

   Proof transcript for the final theorem:

   ```lean
   ext z
   rw [complexRealFiberIntegral_apply]
   simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
   rw [integrateHeadBlock_apply_finAppend]
   apply integral_congr_ae
   filter_upwards with t
   rw [mixedChartFiberFirstCLE_symm_finAppend]
   ```

   If the exact simp theorem for `compCLMOfContinuousLinearEquiv` has a
   different generated name, first prove and use local apply lemmas for
   `complexChartRealFlattenCLE` and `mixedChartFiberFirstCLE` composition; do
   not change the theorem statement or the chart direction.

   After these transport lemmas, prove the pure theorem behind
   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant` in SCV
   as a real-coordinate theorem.  The production target is the recursive
   quotient descent used by the checked Wightman source pattern: first prove
   the one-coordinate quotient through `sliceIntegral` using the
   `headFiberAntideriv` theorem, then induct over the head block.  The
   zero-fiber-integral Poincare decomposition is useful intuition, but it
   should not be introduced as a separate public theorem unless a later proof
   consumes it directly.

   ```lean
   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G
   ```

   Proof transcript for this decomposition:

   1. `m = 0`: use `integrateHeadBlock_apply_finAppend` and
      `Measure.volume_pi_eq_dirac` / `integral_dirac` to reduce `hF` to
      `F = 0`; the empty sum is zero.
   2. `m = k + 1`: expose the first head coordinate by an explicit continuous
      linear equivalence
      `(Fin n -> ℝ) × (Fin (k + 1) -> ℝ) ≃L[ℝ]
       ((Fin n -> ℝ) × (Fin k -> ℝ)) × ℝ`, not by importing the Wightman
      reindexing file.
   3. Let
      `g(s,u) = ∫ x : ℝ, F (Fin.append (Fin.cons x s) u)`.  This is a checked
      instance of `realFiberIntegral` with base
      `(Fin k -> ℝ) × (Fin n -> ℝ)`.
   4. Pick one fixed normalized one-dimensional Schwartz bump `φ` and define
      `F₀(x,s,u) = F(x,s,u) - φ x * g(s,u)`.  Then
      `∫ x, F₀(x,s,u) = 0` for every `(s,u)`.
   5. Apply the one-coordinate fiberwise antiderivative theorem to `F₀`,
      obtaining `H₀` with `∂_{firstHead} H₀ = F₀`.
   6. The remaining term `φ x * g(s,u)` has zero integral over the remaining
      `k` head coordinates because `integrateHeadBlock F = 0`.  Apply the
      induction hypothesis to `g`, then prepend each primitive with `φ`.
   7. Reassemble the sum of derivatives and transport it back through the
      head-tail append equivalence.

   The direct quotient map now has the basic checked algebra needed by this
   induction:

   ```lean
   theorem integrateHeadBlock_add
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       integrateHeadBlock (m := m) (n := n) (F + G) =
         integrateHeadBlock (m := m) (n := n) F +
           integrateHeadBlock (m := m) (n := n) G

   theorem integrateHeadBlock_sub
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       integrateHeadBlock (m := m) (n := n) (F - G) =
         integrateHeadBlock (m := m) (n := n) F -
           integrateHeadBlock (m := m) (n := n) G
   ```

   The one-coordinate antiderivative theorem is the large analytic extraction
   still needed here.  Do not start with a general Banach-space parameter `E`;
   the first production theorem should be the finite-dimensional real product
   statement below, which is exactly what the induction consumes:

   ```lean
   noncomputable def headFiberAntiderivRaw {n : ℕ}
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
       (Fin (n + 1) -> ℝ) -> ℂ :=
     fun v => ∫ t in Set.Iic (v 0), F (Fin.cons t (Fin.tail v))

   noncomputable def headFiberAntideriv {n : ℕ}
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hF : ∀ y : Fin n -> ℝ, ∫ x : ℝ, F (Fin.cons x y) = 0) :
       SchwartzMap (Fin (n + 1) -> ℝ) ℂ

   theorem lineDeriv_headFiberAntideriv {n : ℕ}
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hF : ∀ y : Fin n -> ℝ, ∫ x : ℝ, F (Fin.cons x y) = 0) :
       LineDeriv.lineDerivOp
         ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ)
         (headFiberAntideriv F hF) = F

   theorem exists_headFiberAntideriv_of_integral_eq_zero
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hF : ∀ y : Fin n -> ℝ, ∫ x : ℝ, F (Fin.cons x y) = 0) :
       ∃ H : SchwartzMap (Fin (n + 1) -> ℝ) ℂ,
         LineDeriv.lineDerivOp
           ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ) H = F
   ```

   Proof transcript for this extraction:

   1. Extract the QFT-free definitions underlying
      `Wightman/Reconstruction/SliceIntegral.lean` into a new SCV companion
      file, with names `SCV.headFiberAntiderivRaw` and
      `SCV.headFiberAntideriv`.  The true dependency range is not only lines
      1713-2639: the proof also consumes the earlier slice-integral,
      `iicZeroSlice`, and `intervalPiece` derivative machinery.
   2. Also extract the elementary coordinate maps used by that proof:
      `tailInsertCLM`, `tailInsertCLM_apply`, `tailInsertCLM_opNorm_le`,
      `SCV.tailCLM`, and the `Fin.cons`/`Fin.tail` coordinate identities.  These
      are finite-dimensional real-coordinate lemmas, not Wightman objects.
   3. Keep the two analytic representations explicit:
      `headFiberAntiderivRaw F v = ∫ t in Set.Iic (v 0), ...`, and under
      `hF`,
      `headFiberAntiderivRaw F v = -(∫ t in Set.Ioi (v 0), ...)`.
   4. Prove the head-direction FTC lemma first:
      `lineDeriv ℝ (headFiberAntiderivRaw F) v (Pi.single 0 1) = F v`.
   5. Prove smoothness by the interval/Iic decomposition and parameterized
      FTC, then prove Schwartz decay by the negative/positive half-line split.
      The decay induction must retain the tail-derivative formula
      `fderiv headFiberAntiderivRaw = head term + tail antiderivatives`.
   6. Wrap the raw map as a `SchwartzMap` only after smoothness and decay are
      checked; no `sorry` or arbitrary choice is allowed in the definition.
   7. The existential theorem is then a one-line `refine ⟨headFiberAntideriv F
      hF, ?_⟩; ext v; simpa [SchwartzMap.lineDerivOp_apply] using
      lineDeriv_headFiberAntideriv F hF v`.

   Do not import `Wightman/Reconstruction/SliceIntegral.lean` into SCV.  The
   source file is a proof pattern only; the production dependency must be
   QFT-free.

   First extract the small pure product-coordinate substrate from
   `Wightman/SchwartzTensorProduct.lean` into
   `SCV/SchwartzPrependField.lean`; do not import the Wightman file into SCV.
   This file is genuine Schwartz infrastructure, not a wrapper.  The
   declarations must live under `namespace SCV`, not as global `tailCLM` or
   `SchwartzMap.prependField`, because the old Wightman source already defines
   those global names.  The Stage 3.5 consumer only needs the finite-dimensional
   real-coordinate case:

   ```lean
   import OSReconstruction.SCV.DistributionalEOWKernel

   namespace SCV

   noncomputable def tailCLM (n : ℕ) :
       (Fin (n + 1) -> ℝ) ->L[ℝ] (Fin n -> ℝ)
   @[simp] theorem tailCLM_apply
   theorem tailCLM_opNorm_le
   theorem norm_le_head_add_tail

   def prependField
       (f : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ) :
       SchwartzMap (Fin (n + 1) -> ℝ) ℂ
   @[simp] theorem prependField_apply
   theorem prependField_add_right
   theorem prependField_sub_right
   theorem prependField_smul_right
   theorem prependField_seminorm_le
   theorem prependField_isBounded_right
   theorem prependField_continuous_right
   def prependFieldCLMRight
   @[simp] theorem prependFieldCLMRight_apply

   end SCV
   ```

   The proof should not port the full old tensor-product continuity package.
   Prove fixed-head continuity directly from the Schwartz seminorm estimate:

   ```lean
   theorem prependField_seminorm_le {n : ℕ}
       (f : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ)
       (p l : ℕ) :
       SchwartzMap.seminorm ℝ p l (SCV.prependField f g) ≤
         (2 : ℝ) ^ p * ∑ i in Finset.range (l + 1), (l.choose i : ℝ) *
           (SchwartzMap.seminorm ℝ p i f *
              SchwartzMap.seminorm ℝ 0 (l - i) g +
            SchwartzMap.seminorm ℝ 0 i f *
              SchwartzMap.seminorm ℝ p (l - i) g)
   ```

   For each target seminorm `(p,l)`, take the finite source index set
   `{(0,l-i), (p,l-i) | i ∈ range (l+1)}` and the real constant
   `(2 : ℝ)^p * ∑ i, choose(l,i) *
     (seminorm p i f + seminorm 0 i f)`.  Since each source seminorm is bounded
   by the finite supremum over that set, `WithSeminorms.continuous_of_isBounded`
   gives `SCV.prependField_continuous_right`.  This is the exact fixed-head
   CLM needed by the descent proof.  The left and joint continuity lemmas from
   the old source should stay unported unless a named later proof consumes them.

   Lean proof transcript for `SCV/SchwartzPrependField.lean`:

   1. Define `SCV.tailCLM n` as the projection `x ↦ fun i => x i.succ`, prove
      `tailCLM_apply` by `rfl`, and prove `tailCLM_opNorm_le` from the pi
      norm projection bound.  Prove `norm_le_head_add_tail` by `Fin.cases` on
      the coordinate index.
   2. Define `SCV.prependField f g` by
      `toFun x = f (x 0) * g (fun i => x i.succ)`.  Smoothness is
      `ContDiff.mul` after composing `f.smooth'` with the head projection and
      `g.smooth'` with `SCV.tailCLM n`.
   3. Prove the `decay'` field directly from the old source estimate:
      compose iterated derivatives through the head and tail CLMs, apply
      `norm_iteratedFDeriv_mul_le`, use
      `norm_le_head_add_tail` and `(a+b)^p ≤ 2^p(a^p+b^p)`, and finish with
      the Schwartz decay constants for `f` and `g`.
   4. Prove the algebra lemmas by `ext x; simp [SCV.prependField, mul_add,
      mul_sub, mul_left_comm]`.
   5. Prove `prependField_seminorm_le` by repeating the decay estimate with
      `SchwartzMap.le_seminorm ℝ` in place of chosen decay constants.  This
      theorem is the non-wrapper mathematical input for continuity.
   6. Prove `prependField_isBounded_right f` for the real restricted linear
      map `g ↦ SCV.prependField f g` using `Seminorm.IsBounded.of_real`.  For
      target `(p,l)`, use
      `s = image (fun i => (0,l-i)) range ∪ image (fun i => (p,l-i)) range`
      and the constant described above; each source seminorm is controlled by
      `Finset.le_sup` at the corresponding image member.
   7. Prove `prependField_continuous_right f` by applying
      `WithSeminorms.continuous_of_isBounded` to
      `schwartz_withSeminorms ℝ (Fin n -> ℝ) ℂ` and
      `schwartz_withSeminorms ℝ (Fin (n+1) -> ℝ) ℂ`.
   8. Define `SCV.prependFieldCLMRight f` as the complex continuous linear map
      whose `toLinearMap` is `g ↦ SCV.prependField f g`, with complex add/smul
      laws from step 4 and continuity from step 7.

   Lean-ready extraction order for `SCV/HeadFiberAntideriv.lean`:

   ```lean
   import OSReconstruction.SCV.SchwartzPrependField
   import OSReconstruction.SCV.HeadBlockIntegral
   import Mathlib.Analysis.Calculus.ParametricIntegral
   import Mathlib.Analysis.Asymptotics.Lemmas
   import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
   import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
   import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
   import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
   import Mathlib.MeasureTheory.Integral.IntegralEqImproper
   import Mathlib.MeasureTheory.Integral.Prod
   ```

   The declarations should be ported in this order, and each batch should be
   checked by `lake env lean` on the exact touched file.  Current status:
	   batches 1-7 below are now checked across the pure-SCV files.  To
	   keep the frontier below the harness file-size threshold, the remaining
	   antiderivative extraction was split into coherent companion files:

   1. `SCV/HeadFiberAntideriv.lean` — checked slice-integral substrate,
      including `iicZeroSlice` and its derivative/`ContDiff` package.
   2. `SCV/HeadFiberAntiderivInterval.lean` — checked `intervalPiece`,
      `headFiberAntiderivRaw`, and the head-direction FTC.
	   3. `SCV/HeadFiberAntiderivDecay.lean` — checked zero-slice preservation,
	      decay induction, and final Schwartz packaging.

   The split is organizational only: each file contains genuine analytic
   content and no forwarding wrapper layer.

   1. Coordinate insertion and one-dimensional slice integral:

      ```lean
      noncomputable def tailInsertCLM (n : ℕ) :
          (Fin n -> ℝ) ->L[ℝ] (Fin (n + 1) -> ℝ)

      @[simp] theorem tailInsertCLM_apply ...
      theorem tailInsertCLM_opNorm_le ...

      def sliceIntegralRaw {n : ℕ}
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V)
          (y : Fin n -> ℝ) : V :=
        ∫ x : ℝ, F (Fin.cons x y)

      @[simp] theorem sliceIntegralRaw_prependField
          (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ)
          (y : Fin n -> ℝ) :
          sliceIntegralRaw (SCV.prependField φ g) y =
            (∫ x : ℝ, φ x) * g y

      theorem integral_sliceIntegralRaw
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V) :
          ∫ y : Fin n -> ℝ, sliceIntegralRaw F y =
            ∫ z : Fin (n + 1) -> ℝ, F z

      theorem exists_one_add_norm_pow_mul_sliceIntegralRaw_le
          {n k : ℕ} {V : Type*} [NormedAddCommGroup V]
          [NormedSpace ℝ V] [CompleteSpace V] :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ (F : SchwartzMap (Fin (n + 1) -> ℝ) V)
              (y : Fin n -> ℝ),
              (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖ ≤
                C * ((Finset.Iic (k + 2, 0)).sup
                  (schwartzSeminormFamily ℝ (Fin (n + 1) -> ℝ) V)) F

      theorem norm_sliceSection_le_inv_one_add_sq
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (y : Fin n -> ℝ) (x : ℝ) :
          ‖F (Fin.cons x y)‖ ≤
            ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) -> ℝ) ℂ)) F) *
              (1 + x ^ 2)⁻¹

      theorem integrable_sliceSection
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) (y : Fin n -> ℝ) :
          Integrable (fun x : ℝ => F (Fin.cons x y))

      theorem decay_sliceIntegralRaw
          (k m : ℕ)
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V) :
          ∃ C : ℝ, ∀ y : Fin n -> ℝ,
            ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F) y‖ ≤ C

      noncomputable def sliceIntegral
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V) :
          SchwartzMap (Fin n -> ℝ) V

      @[simp] theorem sliceIntegral_apply
      theorem integral_sliceIntegral

      -- Complex-valued algebra needed by descent:
      theorem sliceIntegral_add
          (F G : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          sliceIntegral (F + G) = sliceIntegral F + sliceIntegral G
      theorem sliceIntegral_sub
          (F G : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          sliceIntegral (F - G) = sliceIntegral F - sliceIntegral G
      theorem sliceIntegral_smul
          (c : ℂ) (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          sliceIntegral (c • F) = c • sliceIntegral F
      theorem sliceIntegral_prependField
          (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ) :
          sliceIntegral (SCV.prependField φ g) =
            (∫ x : ℝ, φ x) • g
      theorem sliceIntegral_prependField_eq_self
          (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ)
          (hφ : ∫ x : ℝ, φ x = 1) :
          sliceIntegral (SCV.prependField φ g) = g

      theorem sliceIntegral_translateSchwartz_head
      ```

      Proof transcript for this batch:

      1. `tailInsertCLM` is the linear map `y ↦ Fin.cons 0 y`; prove its
         operator norm bound by the pi-norm supremum.
      2. `sliceIntegralRaw_prependField` is
         `MeasureTheory.integral_mul_const` after unfolding
         `SCV.prependField_apply`.
      3. `integral_sliceIntegralRaw` uses
         `MeasurableEquiv.piFinSuccAbove` at coordinate `0`,
         `volume_preserving_piFinSuccAbove`, integrability of Schwartz maps,
         `integral_prod_symm`, and the measure-preserving integral-change
         theorem.
      4. `exists_one_add_norm_pow_mul_sliceIntegralRaw_le` is the first
         genuine estimate: with
         `S = (Finset.Iic (k+2,0)).sup schwartzSeminormFamily F`, prove
         `(1+‖y‖)^k * ‖F (Fin.cons x y)‖ ≤
          (2^(k+2) * S) * (1+x^2)⁻¹`, integrate against
         `integrable_inv_one_add_sq`, and take
         `C = 2^(k+2) * ∫ x, (1+x^2)⁻¹`.
      5. `norm_sliceSection_le_inv_one_add_sq` is the `k=0` pointwise majorant
         from the same seminorm estimate.  `integrable_sliceSection` follows
         by `Integrable.mono'`.
      6. `decay_sliceIntegralRaw` is by induction on the iterated derivative
         order: the base case uses the estimate in step 4; the successor step
         uses `fderiv_sliceIntegralRaw_eq`, composition by
         `ContinuousLinearMap.compL ... (SCV.tailInsertCLM n)`, and the
         induction hypothesis for `SchwartzMap.fderivCLM`.
      7. Package `sliceIntegral` only after `contDiff_sliceIntegralRaw` and
         `decay_sliceIntegralRaw` are proved.  The add/sub/smul and
         prepend-field theorems are then pointwise integral algebra; they are
         not a substitute for the decay proof.

      `sliceIntegral` is not an optional convenience wrapper: it is the
      quotient map used by the one-coordinate descent theorem and the recursive
      head-block descent induction.

   2. Derivatives of the raw slice integral:

      ```lean
      theorem hasFDerivAt_sliceSection
      theorem norm_fderiv_fullSlice_le_inv_one_add_sq
      theorem norm_fderiv_sliceSection_le_inv_one_add_sq
      theorem hasFDerivAt_sliceIntegralRaw
      theorem fderiv_sliceIntegralRaw_eq
      theorem continuous_fderiv_sliceIntegralRaw
      theorem contDiff_nat_sliceIntegralRaw
      theorem contDiff_sliceIntegralRaw
      ```

      These are needed only for the zero-slice preservation lemma below.  The
      proof is dominated differentiation under the integral with derivative
      field
      `(fun x => (fderiv ℝ F (Fin.cons x y)).comp (tailInsertCLM n))`.

   3. Fixed lower half-line slice:

      ```lean
      def iicZeroSlice {n : ℕ}
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) (y : Fin n -> ℝ) : ℂ :=
        ∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)

      theorem hasFDerivAt_iicZeroSlice
      theorem fderiv_iicZeroSlice_eq
      theorem contDiff_nat_iicZeroSlice
      theorem contDiff_iicZeroSlice
      ```

      This is the restricted-measure version of the slice-integral derivative
      theorem.  It supplies the tail-smooth fixed-boundary term in
      `headFiberAntiderivRaw_eq_interval_add_iic`.

   4. Variable finite interval piece:

      ```lean
      def intervalPiece {n : ℕ}
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (v : Fin (n + 1) -> ℝ) : ℂ :=
        ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t (Fin.tail v))

      theorem hasDerivAt_intervalPiece_head
      theorem hasFDerivAt_intervalPiece_tailFixed
      theorem intervalPiece_split_at
      theorem hasFDerivAt_intervalPiece_tailFixed_prod
      theorem hasFDerivAt_intervalPiece_headFixed_prod
      def intervalPieceShortTailError
      theorem intervalPiece_prod_split
      theorem norm_intervalPieceShortTailError_le
      theorem hasFDerivAt_intervalPieceShortTailError
      noncomputable def headTailCLM
      theorem hasFDerivAt_intervalPiece_prod
      theorem hasFDerivAt_intervalPiece
      theorem contDiff_intervalPiece
      ```

      The only hard point here is the product differentiability proof:
      split simultaneous head/tail variation into a head-fixed piece plus a
      short tail-error integral and use the uniform derivative bound from the
      old source proof.

   5. Raw antiderivative, FTC, and split formulas:

      ```lean
      def headFiberAntiderivRaw
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          (Fin (n + 1) -> ℝ) -> ℂ :=
        fun v => ∫ t in Set.Iic (v 0), F (Fin.cons t (Fin.tail v))

      theorem headFiberAntiderivRaw_eq_interval_add_iic
      theorem lineDeriv_headFiberAntiderivRaw
      theorem headFiberAntiderivRaw_eq_neg_ioi
      ```

      `lineDeriv_headFiberAntiderivRaw` is the one-dimensional FTC:
      fix the tail `y = Fin.tail v`, set `G s = F (Fin.cons s y)`, use
      `hasDerivAt_integral_Iic`, and identify
      `Fin.tail (v + t • Pi.single 0 1) = y`.

   6. Tail-derivative recursion and decay:

      ```lean
      theorem zeroSlice_lineDerivOp_tailInsert
      theorem fderiv_iicZeroSlice_comp_tail_tailInsert_eq
      theorem fderiv_intervalPiece_tailInsert_eq
      theorem head_tail_decomposition_sliceIntegral
      theorem fderiv_iicZeroSlice_comp_tail_apply
      theorem contDiff_headFiberAntiderivRaw
      theorem fderiv_headFiberAntiderivRaw_apply
      theorem exists_norm_pow_mul_headFiberAntiderivRaw_le
      theorem headFiberAntiderivRaw_add
      theorem headFiberAntiderivRaw_smul
      theorem headFiberAntiderivRaw_finset_sum
      theorem fderiv_headFiberAntiderivRaw_eq_sum
      theorem decay_headFiberAntiderivRaw
      ```

      The zero-slice preservation theorem is:

      ```lean
      theorem zeroSlice_lineDerivOp_tailInsert
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0)
          (w : Fin n -> ℝ) :
          ∀ y : Fin n -> ℝ,
            ∫ t : ℝ,
              (LineDeriv.lineDerivOp (tailInsertCLM n w) F)
                (Fin.cons t y) = 0
      ```

      Its proof is not optional: rewrite `sliceIntegralRaw F = 0`, take the
      line derivative in the tail direction, rewrite the derivative of
      `sliceIntegralRaw` by differentiating under the integral, and conclude
      the new slice integral is zero.

      The decay proof is by induction on the iterated-derivative order `p`.
      At `p = 0`, split into cases `0 <= v 0` and `v 0 <= 0`, using the
      `Set.Ioi` representation in the first case and the original `Set.Iic`
      representation in the second.  In the successor step, use
      `fderiv_headFiberAntiderivRaw_eq_sum` and the induction hypotheses for
      the tail derivatives supplied by `zeroSlice_lineDerivOp_tailInsert`.

      The compact-support theorem
      `hasCompactSupport_fiberwiseAntiderivRaw` from the old source is not
      consumed by the Stage 3.5 descent proof and should not be ported unless a
      later named proof step needs it.

   7. Schwartz packaging:

      ```lean
      noncomputable def headFiberAntideriv
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0) :
          SchwartzMap (Fin (n + 1) -> ℝ) ℂ :=
        SchwartzMap.mk (headFiberAntiderivRaw F)
          (contDiff_headFiberAntiderivRaw F)
          (decay_headFiberAntiderivRaw F hzero)

      theorem lineDeriv_headFiberAntideriv
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0)
          (v : Fin (n + 1) -> ℝ) :
          lineDeriv ℝ (headFiberAntideriv F hzero) v
            (Pi.single 0 1) = F v

      theorem lineDerivOp_headFiberAntideriv
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0) :
          LineDeriv.lineDerivOp
            ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ)
            (headFiberAntideriv F hzero) = F
      ```

	      The last theorem is an `ext v` wrapper over the pointwise line-derivative
	      theorem and is the exact consumer surface for head-translation descent.

	   Lean-ready transcript for `SCV/HeadFiberAntiderivDecay.lean`:

	   ```lean
	   import OSReconstruction.SCV.HeadFiberAntiderivInterval

	   noncomputable section

	   open scoped SchwartzMap Topology
	   open MeasureTheory SchwartzMap LineDeriv

	   namespace SCV
	   ```

	   This file is a direct QFT-free extraction of the checked source block
	   `Wightman/Reconstruction/SliceIntegral.lean`, lines 1945-2639, with
	   `fiberwiseAntiderivRaw` renamed to `headFiberAntiderivRaw` and the
	   collision-free `SCV.tailCLM` used in place of the old global `tailCLM`.
	   Do not port lines 1808-1940
	   (`hasCompactSupport_fiberwiseAntiderivRaw`): compact support of the raw
	   primitive is not consumed by the Stage 3.5 quotient descent and would only
	   enlarge the frontier.

	   1. Zero-slice preservation:

	      ```lean
	      theorem zeroSlice_lineDerivOp_tailInsert {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0)
	          (w : Fin n -> ℝ) :
	          ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ,
	              (∂_{tailInsertCLM n w} F) (Fin.cons t y) = 0
	      ```

	      Proof:
	      define `hzeroFun : sliceIntegralRaw F = 0` by extensionality and
	      `hzero`.  The line derivative of the zero function is zero.  Rewrite
	      `lineDeriv ℝ (sliceIntegralRaw F) y w` using
	      `hasFDerivAt_sliceIntegralRaw`, move evaluation through
	      `ContinuousLinearMap.integral_apply`, and simplify with
	      `SchwartzMap.lineDerivOp_apply_eq_fderiv` and `tailInsertCLM_apply`.
	      The integrability input is exactly the differentiated-slice majorant
	      `norm_fderiv_sliceSection_le_inv_one_add_sq`.

	   2. Tail-derivative identities for the raw primitive:

	      ```lean
	      theorem fderiv_iicZeroSlice_comp_tail_tailInsert_eq
	      theorem fderiv_intervalPiece_tailInsert_eq
	      theorem head_tail_decomposition_sliceIntegral
	      theorem fderiv_iicZeroSlice_comp_tail_apply
	      theorem contDiff_headFiberAntiderivRaw
	      theorem fderiv_headFiberAntiderivRaw_apply
	      theorem headFiberAntiderivRaw_eq_neg_ioi
	      ```

	      Proof:
	      `fderiv_iicZeroSlice_comp_tail_tailInsert_eq` is the chain rule for
	      `iicZeroSlice F ∘ SCV.tailCLM n`, plus restricted-measure dominated
	      differentiation under the `Set.Iic 0` integral.  The dominating
	      function is again
	      `C * (1 + t^2)⁻¹`, with
	      `C = 4 * ((Finset.Iic (2,1)).sup schwartzSeminormFamily) F`.
	      `fderiv_intervalPiece_tailInsert_eq` evaluates the derivative formula
	      from `hasFDerivAt_intervalPiece` on the pure tail vector
	      `tailInsertCLM n w`; the head projection term vanishes and
	      `ContinuousLinearMap.intervalIntegral_apply` turns the remaining CLM
	      integral into the interval piece of the tail derivative.
	      `head_tail_decomposition_sliceIntegral` is the coordinate identity
	      `y = y 0 • Pi.single 0 1 + tailInsertCLM n (tailCLM n y)`.
	      `fderiv_iicZeroSlice_comp_tail_apply` reduces an arbitrary direction
	      to its tail component using the chain-rule derivative above.
	      Smoothness is the sum of `contDiff_intervalPiece F` and
	      `(contDiff_iicZeroSlice F).comp (tailCLM n).contDiff`.
	      The derivative formula for `headFiberAntiderivRaw` rewrites the raw
	      primitive as `intervalPiece + iicZeroSlice ∘ Fin.tail`; the head term
	      comes from `intervalPiece`, and the tail terms combine back into
	      `headFiberAntiderivRaw` for the line derivative
	      `∂_{tailInsertCLM n (tailCLM n y)} F`.  The `Set.Ioi` representation is
	      the complement split
	      `∫_{Iic a} f = ∫ f - ∫_{Ioi a} f` plus `hzero`.

	   3. Zeroth-order decay:

	      ```lean
	      theorem exists_norm_pow_mul_headFiberAntiderivRaw_le {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0)
	          (k : ℕ) :
	          ∃ C : ℝ, ∀ v : Fin (n + 1) -> ℝ,
	            ‖v‖ ^ k * ‖headFiberAntiderivRaw F v‖ ≤ C
	      ```

	      Proof:
	      set
	      `S = ((Finset.Iic (k+2,0)).sup schwartzSeminormFamily) F`,
	      `M = 2^(k+2) * S`, and
	      `C = ∫ t, M * (1 + t^2)⁻¹`.  For
	      `zfun t = Fin.cons t (Fin.tail v)`, prove the pointwise estimate
	      `‖zfun t‖^k * ‖F (zfun t)‖ ≤ M * (1+t^2)⁻¹` from the Schwartz seminorm.
	      If `0 <= v 0`, rewrite the primitive by the `Set.Ioi` formula and use
	      `v`'s coordinates bounded by `zfun t` on `t ∈ Ioi (v 0)`.  If
	      `v 0 <= 0`, use the defining `Set.Iic` formula and the analogous
	      coordinate bound on `t ∈ Iic (v 0)`.  Both cases finish by
	      `setIntegral_mono_on` and `setIntegral_le_integral` against
	      `integrable_inv_one_add_sq`.

	   4. Linearity and derivative-basis decomposition:

	      ```lean
	      theorem headFiberAntiderivRaw_add
	      theorem headFiberAntiderivRaw_smul
	      theorem headFiberAntiderivRaw_finset_sum
	      theorem fderiv_headFiberAntiderivRaw_eq_sum
	      ```

	      Proof:
	      additivity and scalar-linearity are integral algebra over `Set.Iic`.
	      The finite-sum lemma is induction over `Finset`.  For the derivative
	      sum, expand `tailCLM n h` in the standard basis of `Fin n`, map that
	      decomposition through `tailInsertCLM n`, use linearity of
	      `SchwartzMap.lineDerivOp`, then apply finite-sum linearity of the raw
	      antiderivative to the tail part in
	      `fderiv_headFiberAntiderivRaw_apply`.

	   5. Full Schwartz decay and packaging:

	      ```lean
	      theorem decay_headFiberAntiderivRaw {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0)
	          (k p : ℕ) :
	          ∃ C : ℝ, ∀ v : Fin (n + 1) -> ℝ,
	            ‖v‖ ^ k *
	              ‖iteratedFDeriv ℝ p (headFiberAntiderivRaw F) v‖ ≤ C

	      noncomputable def headFiberAntideriv {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0) :
	          SchwartzMap (Fin (n + 1) -> ℝ) ℂ

	      theorem lineDeriv_headFiberAntideriv
	      theorem lineDerivOp_headFiberAntideriv
	      theorem exists_headFiberAntideriv_of_integral_eq_zero
	      ```

	      Proof:
	      induct on derivative order `p`.  The base case is
	      `exists_norm_pow_mul_headFiberAntiderivRaw_le`.  In the successor,
	      use `fderiv_headFiberAntiderivRaw_eq_sum` to write the derivative as
	      one head coefficient term plus finitely many tail-antiderivative terms.
	      The head coefficient uses `F.decay' k p`; the tail terms use the
	      induction hypothesis applied to
	      `∂_{tailInsertCLM n (Pi.single i 1)} F`, whose zero-slice hypothesis is
	      supplied by `zeroSlice_lineDerivOp_tailInsert`.  Push iterated
	      derivatives through the continuous linear maps with
	      `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`, sum the bounds, and
	      take
	      `C_total = ‖L₀‖ * C_head + ∑ i, ‖Lᵢ i‖ * C_tail i`.
	      Package the raw map by `SchwartzMap.mk` only after
	      `contDiff_headFiberAntiderivRaw` and `decay_headFiberAntiderivRaw`.
	      The pointwise line-derivative theorem is inherited from the checked raw
	      FTC lemma, and the `LineDeriv.lineDerivOp` theorem is an extensional
	      restatement for the descent consumer.

	   After `SCV/HeadFiberAntiderivDecay.lean`, the next file should be
	   `SCV/HeadBlockDescent.lean`.  It ports the QFT-free proof pattern from
	   `Wightman/Reconstruction/HeadTranslationInvariant.lean` and
	   `Wightman/Reconstruction/HeadBlockTranslationInvariant.lean`, but with
	   `SCV.headBlockShift`, `SCV.integrateHeadBlock`, and the new
   `SCV.sliceIntegral` package.  The production proof should use this
   recursive quotient descent rather than introducing an unconsumed explicit
   decomposition theorem.

	   Current checked status:

	   `SCV/HeadBlockDescent.lean` now checks the one-coordinate descent layer:
	   `IsHeadTranslationInvariantSchwartzCLM`,
	   `map_lineDeriv_eq_zero_of_headTranslationInvariant`,
	   `map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant`,
	   `map_eq_of_sliceIntegral_eq_of_headTranslationInvariant`,
	   `normedUnitBumpSchwartz`, `integral_normedUnitBumpSchwartz`,
	   `headTranslationDescentCLM`, and
	   `map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant`.
	   This is genuine descent content: it uses the checked
	   `headFiberAntideriv` package, not a wrapper around the old Wightman files.

	   The general block descent has one additional SCV-specific bridge compared
	   with the old source.  The old Wightman `integrateHeadBlock` was a
	   recursive definition, so the induction step reduced by
	   `simp [integrateHeadBlock]`.  The SCV `integrateHeadBlock` in
	   `SCV/HeadBlockIntegral.lean` is instead the direct finite-dimensional
	   block integral through `realFiberIntegral`.  The recursive induction now
	   proves the direct/recursive Fubini bridge explicitly; the bridge is not
	   hidden behind the induction theorem.

	   The same file now checks the general head-block descent layer:
	   `castFinCLE_apply`, `headBlockShift_zero`,
	   `finAppend_zero_castFinCLE`,
	   `reindexSchwartzFin_translate_headBlockShift_succ`,
	   `reindexSchwartzFin_symm_translate_headBlockShift`,
	   `prependField_translate_headBlockShift`,
	   `headTranslationDescentCLM_headBlockInvariant`,
	   `integrateHeadBlock_sliceIntegral_reindex`, and
	   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV`.

	   Implemented declaration order for `SCV/HeadBlockDescent.lean`:

   ```lean
	   import OSReconstruction.SCV.HeadFiberAntiderivDecay
	   import OSReconstruction.SCV.DistributionalEOWKernelTransport
	   import Mathlib.Analysis.Calculus.BumpFunction.Normed

   def IsHeadTranslationInvariantSchwartzCLM
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ) : Prop :=
     ∀ a : ℝ, T.comp (translateSchwartzCLM (Fin.cons a 0)) = T

   theorem map_lineDeriv_eq_zero_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
       T (LineDeriv.lineDerivOp
         ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ) F) = 0

   theorem map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hzero : sliceIntegral F = 0) :
       T F = 0

   theorem map_eq_of_sliceIntegral_eq_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (F G : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hFG : sliceIntegral F = sliceIntegral G) :
       T F = T G
   ```

   The one-coordinate proof is now mechanically specified:

   1. `map_lineDeriv_eq_zero_of_headTranslationInvariant` is the already
      checked difference-quotient argument specialized to the vector
      `Pi.single 0 1`.
   2. `map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant` turns
      `sliceIntegral F = 0` into the pointwise zero-slice hypothesis for
      `headFiberAntideriv`, rewrites
      `LineDeriv.lineDerivOp (Pi.single 0 1) (headFiberAntideriv F hzero') = F`,
      and applies the previous derivative-annihilation theorem.
   3. `map_eq_of_sliceIntegral_eq_of_headTranslationInvariant` applies the
      zero theorem to `F - G`; the only algebra needed is
      `sliceIntegral_sub`, which is proved by the same integral-sub template
      as `integrateHeadBlock_sub`.

   Then add the descended tail functional:

   ```lean
   noncomputable def normedUnitBumpSchwartz : SchwartzMap ℝ ℂ
   theorem integral_normedUnitBumpSchwartz :
       ∫ x : ℝ, normedUnitBumpSchwartz x = 1

   noncomputable def headTranslationDescentCLM
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (φ : SchwartzMap ℝ ℂ) :
       SchwartzMap (Fin n -> ℝ) ℂ ->L[ℂ] ℂ :=
     T.comp (SCV.prependFieldCLMRight φ)

   theorem map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (φ : SchwartzMap ℝ ℂ)
       (hφ : ∫ x : ℝ, φ x = 1)
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
       T F = headTranslationDescentCLM T φ (sliceIntegral F)
   ```

	   Direct/recursive bridge:

	   ```lean
	   abbrev castFinCLE (h : a = b) : (Fin a -> ℝ) ≃L[ℝ] (Fin b -> ℝ)
	   abbrev reindexSchwartzFin (h : a = b) :
	       SchwartzMap (Fin a -> ℝ) ℂ ->L[ℂ] SchwartzMap (Fin b -> ℝ) ℂ
	   @[simp] theorem reindexSchwartzFin_apply
	   @[simp] theorem castFinCLE_symm_apply

	   theorem integrateHeadBlock_sliceIntegral_reindex {m n : ℕ}
	       (F : SchwartzMap (Fin ((m + 1) + n) -> ℝ) ℂ) :
	       integrateHeadBlock (m := m) (n := n)
	         (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) =
	       integrateHeadBlock (m := m + 1) (n := n) F
	   ```

	   Proof transcript for `integrateHeadBlock_sliceIntegral_reindex`:

	   1. Work pointwise in `u : Fin n -> ℝ`.
	   2. The target reduces to
	      `∫ s : Fin m -> ℝ, ∫ x : ℝ,
	         F (Fin.append (Fin.cons x s) u)
	       =
	       ∫ t : Fin (m+1) -> ℝ, F (Fin.append t u)`.
	   3. Prove the fixed-tail head section as a Schwartz map without importing
	      `Wightman/Reconstruction/SchwartzPartialEval.lean`.  Extract the
	      QFT-free `partialEval₂` proof into a pure SCV file:

	      ```lean
	      theorem iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl
	          (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (l : ℕ) (x : E₁) :
	          iteratedFDeriv ℝ l (fun x' => f (x', y)) x =
	            (iteratedFDeriv ℝ l (⇑f) (x, y)).compContinuousLinearMap
	              (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)

	      theorem norm_iteratedFDeriv_partialEval_le
	          (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (l : ℕ) (x : E₁) :
	          ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ ≤
	            ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖

	      def schwartzPartialEval₂
	          (f : SchwartzMap (E₁ × E₂) F) (y : E₂) :
	          SchwartzMap E₁ F

	      @[simp] theorem schwartzPartialEval₂_apply :
	          schwartzPartialEval₂ f y x = f (x, y)
	      ```

	      The decay proof is the standard product-space estimate:
	      choose `C` from `f.decay' k l`, bound the partial-evaluation
	      derivative by the full product derivative via `inl`, and use
	      `‖x‖ ≤ ‖(x,y)‖`.  This is the exact QFT-free mathematical content of
	      the old `partialEval₂` source, with no reconstruction imports.

	      Then define the fixed-tail section by partially evaluating the
	      product-coordinate pullback through `finAppendCLE`:

	      ```lean
	      def fixedTailHeadSection
	          (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
	          (u : Fin n -> ℝ) :
	          SchwartzMap (Fin m -> ℝ) ℂ :=
	        schwartzPartialEval₂
	          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
	            (finAppendCLE m n)) F) u

	      @[simp] theorem fixedTailHeadSection_apply :
	          fixedTailHeadSection F u t = F (Fin.append t u)
	      ```

	      The apply lemma is just
	      `change F (finAppendCLE m n (t,u)) = F (Fin.append t u); congr 1`,
	      using the definitional/product-coordinate behavior already checked for
	      `finAppendCLE`.
	   4. Apply the checked theorem `integral_sliceIntegralRaw` to
	      `fixedTailHeadSection F u`.  Its left side is the nested
	      `∫ s, ∫ x, ...`; its right side is the direct `m+1` head integral.
	   5. Finish by `reindexSchwartzFin_apply`, `sliceIntegral_apply`,
	      `sliceIntegralRaw`, `integrateHeadBlock_apply_finAppend`, and the
	      coordinate identity
	      `(castFinCLE (Nat.succ_add m n)).symm (Fin.cons x (Fin.append s u))
	       = Fin.append (Fin.cons x s) u`.
	      The identity is Lean-ready by `ext i`, `Fin.addCases` on
	      `i : Fin ((m + 1) + n)`, then `Fin.cases` on the head part.  The three
	      index casts needed in the branches are:

	      ```lean
	      (finCongr (Nat.succ_add m n)) (Fin.castAdd n (0 : Fin (m + 1))) = 0
	      (finCongr (Nat.succ_add m n)) (Fin.castAdd n k.succ) =
	        (Fin.castAdd n k).succ
	      (finCongr (Nat.succ_add m n)) (Fin.natAdd (m + 1) j) =
	        (Fin.natAdd m j).succ
	      ```

	      Each is proved by `apply Fin.ext; simp` (`omega` only for the final
	      tail branch).  With these, rewrite `castFinCLE_symm_apply` and close
	      by `simp [Fin.append]`.

	   Finally port the recursive head-block theorem.  The helper lemmas are
	   exactly the reindexing and prepend-field transport lemmas from
	   `HeadBlockTranslationInvariant.lean`, rewritten from the old
	   `zeroTailBlockShift` convention to `headBlockShift`:

   ```lean
   abbrev castFinCLE (h : a = b) : (Fin a -> ℝ) ≃L[ℝ] (Fin b -> ℝ)
   def reindexSchwartzFin (h : a = b)
       (F : SchwartzMap (Fin a -> ℝ) ℂ) :
       SchwartzMap (Fin b -> ℝ) ℂ
   @[simp] theorem castFinCLE_apply
   @[simp] theorem reindexSchwartzFin_apply
   @[simp] theorem castFinCLE_symm_apply

   @[simp] theorem headBlockShift_zero
   private theorem integral_fin_zero
   @[simp] theorem finAppend_zero_castFinCLE
   theorem reindexSchwartzFin_translate_headBlockShift_succ
   theorem reindexSchwartzFin_symm_translate_headBlockShift
   theorem prependField_translate_headBlockShift
   theorem headTranslationDescentCLM_headBlockInvariant
   theorem integrateHeadBlock_sliceIntegral_reindex

   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       {m n : ℕ}
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G
   ```

   Proof transcript for the recursive theorem:

   1. Induct on `m`.
   2. For `m = 0`, evaluate `hFG` at the cast of each tail coordinate and use
      `integrateHeadBlock_apply_finAppend` to prove `F = G`.  Because the SCV
      block integral is direct rather than recursive, this base case must
      explicitly use the zero-dimensional volume identity
      `(volume : Measure (Fin 0 -> ℝ)) = Measure.dirac default`, via
      `Measure.volume_pi_eq_dirac`, and the coordinate identity
      `Fin.append default (castFinCLE (Nat.zero_add n) x) = x`.  The coordinate
      identity is proved by `Fin.addCases`: the head branch is `Fin.elim0`, and
      the tail branch uses `Fin.append_right` plus
      `castFinCLE_apply` and
      `(finCongr (Nat.zero_add n)).symm j = Fin.natAdd 0 j`.
   3. For `m + 1`, reindex `F` and `G` by `Nat.succ_add m n` so the active
      head coordinate is first.
   4. Define `T' = T.comp (reindexSchwartzFin (Nat.succ_add m n).symm)`.
      Prove `T'` is one-coordinate head-translation invariant by rewriting the
      reindexed translate with
      `reindexSchwartzFin_symm_translate_headBlockShift` and applying `hT`.
      In the special vector `Fin.cons a 0`, write the zero tail as
      `fun _ : Fin m => 0`, then use `headBlockShift_zero` to rewrite
      `Fin.cons a (headBlockShift m n 0)` back to `Fin.cons a 0`.
   5. Use
      `map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant`
      to replace `T' F'` and `T' G'` by the descended functional evaluated on
      `sliceIntegral F'` and `sliceIntegral G'`.
   6. Prove the descended functional is invariant under the remaining `m`
      head translations using `prependField_translate_headBlockShift` and
      `hT`.
   7. Convert `hFG` into equality of the remaining block integrals of the two
      slices by the calculation
      `integrateHeadBlock (sliceIntegral F') =
       integrateHeadBlock (m := m + 1) F =
       integrateHeadBlock (m := m + 1) G =
       integrateHeadBlock (sliceIntegral G')`,
      using `integrateHeadBlock_sliceIntegral_reindex` in the first and last
      steps; apply the induction hypothesis.
   8. Reindex back by the inverse `castFinCLE` identities.

   After this theorem checked, the already verified transport proof from
   `test/proofideas_fiber_translation_descent.lean` was moved into production.
   `SCV/DistributionalEOWKernelTransport.lean` now checks:
   `liftToFlatChart_apply_liftMixedToFlat`,
   `liftToFlatChart_headBlockTranslationInvariant`,
   `integrateHeadBlock_liftMixedToFlat_eq_of_complexRealFiberIntegral_eq`, and:

   ```lean
   theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (F G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
       T F = T G
   ```

   The checked derivative-annihilation theorem plus the recursive descent
   theorem give these consumer corollaries.  Add the zero corollary only if a
   downstream proof consumes it directly; the equality theorem above is the
   main Stage 3.5 surface:

   ```lean
   theorem map_lineDeriv_headBlockShift_eq_zero
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (i : Fin m)
       (H : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       T (LineDeriv.lineDerivOp
         (headBlockShift m n (Pi.single i (1 : ℝ))) H) = 0

   theorem map_eq_zero_of_integrateHeadBlock_eq_zero_of_headBlockTranslationInvariant
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hF : integrateHeadBlock (m := m) (n := n) F = 0) :
       T F = 0

   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G
   ```

   The derivative-annihilation lemma is now checked in
   `SCV/HeadBlockIntegral.lean`:

   ```lean
   def IsHeadBlockTranslationInvariantSchwartzCLM
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ) : Prop :=
     ∀ a : Fin m -> ℝ,
       T.comp (translateSchwartzCLM (headBlockShift m n a)) = T

   theorem map_lineDeriv_headBlockShift_eq_zero
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (i : Fin m)
       (H : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       T (LineDeriv.lineDerivOp
         (headBlockShift m n (Pi.single i (1 : ℝ))) H) = 0
   ```

   Its proof uses the checked difference-quotient theorem for
   `translateSchwartz`, now extracted to pure SCV from the QFT-free part of
   `Wightman/Reconstruction/TranslationInvariantSchwartz.lean`.  The checked
   SCV surface in `SCV/TranslationDifferentiation.lean` is:

   ```lean
   theorem exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le
       (f : SchwartzMap (Fin m -> ℝ) ℂ)
       (v : Fin m -> ℝ) (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ t : ℝ, t ≠ 0 -> |t| ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (t⁻¹ • (translateSchwartz (t • v) f - f) -
               LineDeriv.lineDerivOp v f) ≤ C * |t|

   theorem tendsto_diffQuotient_translateSchwartz_zero
       (f : SchwartzMap (Fin m -> ℝ) ℂ)
       (v : Fin m -> ℝ) :
       Filter.Tendsto
         (fun t : ℝ => t⁻¹ • (translateSchwartz (t • v) f - f))
         (nhdsWithin (0 : ℝ) ({0}ᶜ))
         (𝓝 (LineDeriv.lineDerivOp v f))
   ```

   The proof is the QFT-free content of
   `Wightman/Reconstruction/TranslationInvariantSchwartz.lean` lines
   1045-2660.  It was extracted without Wightman imports and without a
   file-level `set_option maxHeartbeats`.  The one long quantitative theorem
   uses a local `set_option maxHeartbeats 1200000 in`, matching the cost of
   the old source proof while keeping the override scoped to the theorem.

   Scratch support status after `agents_chat.md` #1312/#1313, now partly
   superseded by production:

   1. `test/proofideas_fiber_translation_descent.lean` checks with exactly one
      deliberate `sorry`, namely the pure real head-block descent theorem
      `map_eq_of_integrateHeadBlock_eq_of_isHeadBlockTranslationInvariantSCV`.
      Its proved content is the mixed-chart transport corollary from pure
      head-block descent to `complexRealFiberIntegral` descent.  That transport
      corollary is now in production, using
      `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV`
      instead of the scratch `sorry`; the remaining useful scratch material is
      only the elementary tensor-product linearity lemmas for
      `schwartzTensorProduct₂`.
   2. `test/proofideas_head_block_helpers.lean` checks with zero `sorry`s and
      zero warnings.  The file declares 19 theorem helpers, not the 15 stated
      in #1313: `integrateHeadBlock_smul`, `headBlockShift_zero`,
      `headBlockShift_add`, `translateSchwartz_zero`,
      `translateSchwartzCLM_zero`, the four
      `complexRealFiberIntegral_*` linearity lemmas, the six
      `realConvolutionTest_*` linearity lemmas, the three
      `complexRealFiberTranslateSchwartzCLM` / tensor-translate identities,
      and `isHeadBlockTranslationInvariantSCV_of_m_zero`.

   These helpers may be ported only when they are the next named proof step in
   the antiderivative/descent proof.  They are an algebra inventory, not a
   replacement for the genuine finite-dimensional antiderivative theorem.

   The checked quotient-map invariance now available in
   `SCV/HeadBlockIntegral.lean` is:

   ```lean
   theorem integrateHeadBlock_translate_head
       (a : Fin m -> ℝ) (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       integrateHeadBlock (m := m) (n := n)
         (translateSchwartzCLM (headBlockShift m n a) F) =
       integrateHeadBlock (m := m) (n := n) F
   ```

   The mixed factorization theorem then follows by transporting `T`, `F`, and
   `G` through `mixedChartFiberFirstCLE`, applying the SCV head-block theorem,
   and transporting the equality of `integrateHeadBlock` back through
   `complexRealFiberIntegral_eq_transport_integrateHeadBlock`.

   The proof must not stop at this sentence.  The exact mixed theorem package
   is:

   ```lean
   def IsHeadBlockTranslationInvariantSchwartzCLM
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ) : Prop :=
     ∀ a : Fin m -> ℝ,
       T.comp (translateSchwartzCLM (headBlockShift m n a)) = T

   theorem compCLMOfContinuousLinearEquiv_injective
       (e : E ≃L[ℝ] F) :
       Function.Injective
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e :
           SchwartzMap F ℂ ->L[ℂ] SchwartzMap E ℂ)

   theorem compCLMOfContinuousLinearEquiv_symm_left_inv
       (e : E ≃L[ℝ] F) (f : SchwartzMap E ℂ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f) = f

   theorem compCLMOfContinuousLinearEquiv_symm_right_inv
       (e : E ≃L[ℝ] F) (f : SchwartzMap F ℂ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) f) = f

   theorem mixedChartFiberFirstCLE_translate_inv
       (a : Fin m -> ℝ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (mixedChartFiberFirstCLE m)).comp
         (translateSchwartzCLM (headBlockShift m (m * 2) a)) =
       (complexRealFiberTranslateSchwartzCLM a).comp
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (mixedChartFiberFirstCLE m))

   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G

   theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (F G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
       T F = T G
   ```

   Lean proof transcript for `mixedChartFiberFirstCLE_translate_inv`:

   ```lean
   ext H p
   rcases p with ⟨z, t⟩
   -- LHS evaluates `H` at
   --   `mixedChartFiberFirstCLE m (z,t) + headBlockShift m (m*2) a`.
   -- RHS evaluates `H` at
   --   `mixedChartFiberFirstCLE m (z,t+a)`.
   -- Prove the coordinate equality by extensionality:
   have hcoord :
       mixedChartFiberFirstCLE m (z, t) + headBlockShift m (m * 2) a =
         mixedChartFiberFirstCLE m (z, t + a) := by
     ext k
     -- split `k` into head/tail cases and use
     -- `mixedChartFiberFirstCLE_apply_head`,
     -- `mixedChartFiberFirstCLE_apply_tail_re/im`, and
     -- `headBlockShift_apply_head/tail`.
   simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hcoord]
   ```

   Lean proof transcript for the mixed factorization theorem:

   ```lean
   let pullFlat :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (mixedChartFiberFirstCLE m).symm
   let pushMixed :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (mixedChartFiberFirstCLE m)
   let Tflat : SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ] ℂ :=
     T.comp pushMixed
   let Fflat := pullFlat F
   let Gflat := pullFlat G

   have hTflat :
       IsHeadBlockTranslationInvariantSchwartzCLM
         (m := m) (n := m * 2) Tflat := by
     intro a
     ext H
     -- use `mixedChartFiberFirstCLE_translate_inv a`
     -- and `hT a`.

   have hInt :
       integrateHeadBlock (m := m) (n := m * 2) Fflat =
         integrateHeadBlock (m := m) (n := m * 2) Gflat := by
     apply compCLMOfContinuousLinearEquiv_injective
       (complexChartRealFlattenCLE m)
     -- rewrite both sides by
     -- `complexRealFiberIntegral_eq_transport_integrateHeadBlock`
     -- and use `hFG`.

   have hflat :
       Tflat Fflat = Tflat Gflat :=
     map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       Tflat hTflat Fflat Gflat hInt

   -- identify `pushMixed Fflat = F` and `pushMixed Gflat = G` by the
   -- left-inverse theorem for `compCLMOfContinuousLinearEquiv`.
   simpa [Tflat, Fflat, Gflat, pullFlat, pushMixed,
     compCLMOfContinuousLinearEquiv_symm_left_inv] using hflat
   ```

   The proof of
   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV` is a
   direct extraction of the existing QFT-free induction in
   `Wightman/Reconstruction/HeadBlockTranslationInvariant.lean`, but with these
   replacements:

   | Existing source object | SCV extraction |
   |---|---|
   | `zeroTailBlockShift` | `headBlockShift` |
   | `OSReconstruction.integrateHeadBlock` | `SCV.integrateHeadBlock` |
   | `OSReconstruction.sliceIntegral` | `SCV.sliceIntegral` |
   | `headTranslationDescentCLM` | `SCV.headTranslationDescentCLM` |
   | Wightman namespace imports | pure SCV imports only |

   The one-coordinate descent step also requires extracting these QFT-free
   lemmas from `HeadTranslationInvariant.lean`,
   `SliceIntegral.lean`, and `TranslationInvariantSchwartz.lean`:

   ```lean
   def IsHeadTranslationInvariantSchwartzCLM
   theorem tendsto_diffQuotient_translateSchwartz_zero
   theorem map_lineDeriv_eq_zero_of_headTranslationInvariant
   theorem fiberwiseAntideriv
   theorem lineDeriv_fiberwiseAntideriv
   theorem map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant
   theorem map_eq_of_sliceIntegral_eq_of_headTranslationInvariant
   def headTranslationDescentCLM
   theorem map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
   ```

   Each of these is pure Schwartz analysis.  None may mention Wightman
   functions, Schwinger functions, OS positivity, Hilbert spaces, or boundary
   values.

4. Finish global descent:
   ```lean
   theorem translationCovariantProductKernel_descends
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```
   Let `T := shearedProductKernelFunctional K`.  Apply the fiber-factorization
   theorem to `T`; then for product tensors use
   `complexRealFiberIntegral` of the sheared tensor product, which is exactly
   `realConvolutionTest φ ψ`.  This proves the Streater-Wightman statement
   that the kernel depends only on the translated complex point.
6. Prove `Hdist` is distributionally holomorphic by a three-lemma
   integration-by-parts package, not by a one-line appeal to holomorphy.

   The Lean-facing statements are:

   The support-preservation precursor lives in a small companion file
   `SCV/DistributionalEOWSupport.lean`, because
   `SCV/DistributionalEOWKernel.lean` is already a checked, stable support
   file.  Its declarations and proof transcript are:

   ```lean
   theorem directionalDerivSchwartzCLM_tsupport_subset
       {m : ℕ} (v : ComplexChartSpace m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport
         ((directionalDerivSchwartzCLM v φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ) := by
     simpa [directionalDerivSchwartzCLM] using
       (SchwartzMap.tsupport_lineDerivOp_subset (m := v) (f := φ))

   theorem directionalDerivSchwartzCLM_supportsInOpen
       {m : ℕ} {U : Set (ComplexChartSpace m)}
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (v : ComplexChartSpace m) :
       SupportsInOpen
         ((directionalDerivSchwartzCLM v φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) U := by
     constructor
     · exact hφ.1.mono'
         ((subset_tsupport _).trans
           (directionalDerivSchwartzCLM_tsupport_subset v φ))
     · exact
         (directionalDerivSchwartzCLM_tsupport_subset v φ).trans hφ.2

   theorem dbarSchwartzCLM_tsupport_subset
       {m : ℕ} (j : Fin m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport
         ((dbarSchwartzCLM j φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ)

   theorem SupportsInOpen.dbar
       {m : ℕ} {U : Set (ComplexChartSpace m)}
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       SupportsInOpen
         ((dbarSchwartzCLM j φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) U
   ```

   The `dbarSchwartzCLM_tsupport_subset` proof expands `dbarSchwartzCLM j φ`
   into the sum of two scalar multiples of real directional derivatives, uses
   `tsupport_add` and `tsupport_smul_subset_right`, and then applies
   `SchwartzMap.tsupport_lineDerivOp_subset` to the real and imaginary
   coordinate directions.  This is genuine infrastructure for the integration
   by parts package: it proves that applying `dbarSchwartzCLM` to a test
   supported in `U0` is still an admissible compactly supported test in `U0`.

   The next checked `∂bar` precursor is the Schwartz-Schwartz integration by
   parts package in `SCV/DistributionalEOWDbar.lean`.  It intentionally proves
   only the global Schwartz identity; the later local holomorphic factor still
   needs a cutoff/localization theorem before it can be applied to a merely
   holomorphic `G ψ`.

   ```lean
   theorem integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left
       {m : ℕ}
       (f g : SchwartzMap (ComplexChartSpace m) ℂ)
       (v : ComplexChartSpace m) :
       (∫ z : ComplexChartSpace m,
           f z * (directionalDerivSchwartzCLM v g) z) =
         -∫ z : ComplexChartSpace m,
           (directionalDerivSchwartzCLM v f) z * g z

   theorem integral_mul_dbarSchwartzCLM_right_eq_neg_left
       {m : ℕ}
       (f g : SchwartzMap (ComplexChartSpace m) ℂ)
       (j : Fin m) :
       (∫ z : ComplexChartSpace m,
           f z * (dbarSchwartzCLM j g) z) =
         -∫ z : ComplexChartSpace m,
           (dbarSchwartzCLM j f) z * g z

   theorem integral_mul_dbarSchwartzCLM_right_eq_zero_of_dbar_eq_zero
       {m : ℕ}
       (f g : SchwartzMap (ComplexChartSpace m) ℂ)
       (j : Fin m)
       (hf : dbarSchwartzCLM j f = 0) :
       (∫ z : ComplexChartSpace m,
           f z * (dbarSchwartzCLM j g) z) = 0
   ```

   Proof transcript: the directional theorem is exactly
   `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` after unfolding
   `directionalDerivSchwartzCLM`.  The `∂bar` theorem applies the integral
   continuous linear map to the Schwartz pairing `f * g`, expands
   `dbarSchwartzCLM` as
   `(1/2) * (∂_real + I * ∂_imag)`, rewrites the two directional terms by the
   directional integration-by-parts theorem, and closes by ring
   normalization.  The zero corollary rewrites the left factor's
   `dbarSchwartzCLM` to zero.

   The next checked algebraic localization slice is:

   ```lean
   theorem integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
       {m : ℕ}
       (F : ComplexChartSpace m -> ℂ)
       (G φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (j : Fin m)
       (hFG :
         ∀ z ∈ tsupport
             ((dbarSchwartzCLM j φ :
               SchwartzMap (ComplexChartSpace m) ℂ) :
               ComplexChartSpace m -> ℂ),
           F z = G z)
       (hG_dbar_zero :
         ∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
           (dbarSchwartzCLM j G) z = 0) :
       (∫ z : ComplexChartSpace m, F z * (dbarSchwartzCLM j φ) z) = 0
   ```

   Proof transcript: first replace `F` by `G` under the integral.  This is
   valid because `F = G` on `tsupport (dbarSchwartzCLM j φ)` and
   `dbarSchwartzCLM j φ` is pointwise zero off that topological support.  Then
   apply `integral_mul_dbarSchwartzCLM_right_eq_neg_left G φ j`.  The resulting
   integral is zero because `dbarSchwartzCLM j G = 0` on `tsupport φ`, while
   `φ` is pointwise zero off its topological support.  This lemma is the exact
   algebraic endpoint of the cutoff construction; it does not assert the
   cutoff exists.

   The cutoff/localization bridge is now checked in
   `OSReconstruction/SCV/DistributionalEOWRepresentative.lean`:

   ```lean
   theorem exists_local_dbarClosed_schwartz_representative
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
         (∀ z ∈ tsupport
             ((dbarSchwartzCLM j φ :
               SchwartzMap (ComplexChartSpace m) ℂ) :
               ComplexChartSpace m -> ℂ),
             F z = G z) ∧
         (∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
             (dbarSchwartzCLM j G) z = 0)
   ```

   The representative theorem is implemented through smaller theorem
   surfaces.  The compact cutoff theorem is checked in
   `OSReconstruction/SCV/DistributionalEOWCutoff.lean`:

   ```lean
   theorem exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U) :
       ∃ χ : ComplexChartSpace m -> ℝ,
         ContDiff ℝ (⊤ : ℕ∞) χ ∧
         HasCompactSupport χ ∧
         tsupport χ ⊆ U ∧
         Set.range χ ⊆ Set.Icc 0 1 ∧
         ∃ V : Set (ComplexChartSpace m),
           IsOpen V ∧
           tsupport (φ : ComplexChartSpace m -> ℂ) ⊆ V ∧
           V ⊆ U ∧
           Set.EqOn χ (fun _ => 1) V
   ```

   The zero-extension/smooth-to-Schwartz theorem is also checked:

   ```lean
   theorem exists_local_schwartz_representative_eq_on_open
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U) :
       ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
         ∃ V : Set (ComplexChartSpace m),
           IsOpen V ∧
           tsupport (φ : ComplexChartSpace m -> ℂ) ⊆ V ∧
           V ⊆ U ∧
           Set.EqOn (G : ComplexChartSpace m -> ℂ) F V
   ```

   The local Cauchy-Riemann theorem is checked as
   `dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic`: if a Schwartz
   representative agrees with a holomorphic function on an open set `V ⊆ U`,
   then its `dbarSchwartzCLM j` value is zero on `V`.  It unfolds
   `dbarSchwartzCLM`, rewrites line derivatives as real Fréchet derivatives,
   uses eventual equality on `V`, and applies complex-linearity of
   `fderiv ℂ F z` after restricting scalars to `ℝ`.

   Lean-level construction plan for the cutoff and representative:

   1. From `hφ`, obtain compactness of `K = tsupport φ` and `K ⊆ U`.
      Since `dbarSchwartzCLM_tsupport_subset` is checked, the smaller support
      `tsupport (dbarSchwartzCLM j φ)` is also contained in `K`.
   2. The cutoff construction is now checked: build a cutoff equal to one on
      an open neighborhood of `K` using nested
      thickenings, not by applying the pointwise bump theorem directly to
      `K`.  Use `IsCompact.exists_cthickening_subset_open` to choose a closed
      thickening of `K` inside `U`, and
      finite-dimensional properness to keep that thickening compact.  Choose
      radii `0 < r₁ < r₂` such that `cthickening r₂ K` is compact and
      contained in `U`; set
      `V₁ = thickening r₁ K` and `V₂ = thickening r₂ K`.  Then
      `K ⊆ V₁`, `closure V₁ ⊆ V₂`, and
      `closure V₂ ⊆ cthickening r₂ K ⊆ U`.
   3. The checked cutoff theorem applies the smooth support theorem
      `exists_contMDiff_support_eq_eq_one_iff` to the open set `V₂` and the
      closed set `closure V₁`.  Convert the resulting manifold-smooth real
      function to a Euclidean `ContDiff ℝ ∞` function.  This yields
      `χ : ComplexChartSpace m -> ℝ` with range in `[0,1]`,
      `χ = 1` on `closure V₁`, `Function.support χ = V₂`, and hence
      `HasCompactSupport χ` plus `tsupport χ ⊆ U`.
   4. The representative theorem defines the compactly supported smooth
      function `H z = (χ z : ℂ) * F z`.  The support containment
      `tsupport χ ⊆ U` makes this independent of arbitrary values of `F` off
      `U`: outside `U`, `χ` is locally zero.  On a neighborhood of `K`,
      `H = F` because `χ = 1`.
   5. `H` is a Schwartz function by the compact-support smooth-to-
      Schwartz conversion already used in `SCV.DistributionalUniqueness`:
      compact support comes from `tsupport χ`, and smoothness comes from
      `ContDiffOn` multiplication with
      `(hF_holo.analyticOnNhd_of_finiteDimensional hU_open)
        .contDiffOn_of_completeSpace`
      on `U`, restricted from `ℂ` to `ℝ`, and zero smoothness on
      `(tsupport χ)ᶜ`.  The open cover
      `U ∪ (tsupport χ)ᶜ = univ` follows from `tsupport χ ⊆ U`.
   6. Let `G` be that Schwartz representative.  Agreement on
      `tsupport (dbarSchwartzCLM j φ)` follows from Step 1 and `χ = 1` on
      the neighborhood `V₁` of `K`.  The identity
      `(dbarSchwartzCLM j G) z = 0` on `K` follows because `G = F` on the
      same open neighborhood of `K`; after unfolding `dbarSchwartzCLM` and
      `SchwartzMap.lineDerivOp_apply_eq_fderiv`, holomorphicity of `F` gives
      the coordinate Cauchy-Riemann equation in direction `j`.

   The full local theorem is now checked and follows immediately from the
   checked algebraic localization lemma:

   ```lean
   theorem integral_holomorphic_mul_dbarSchwartz_eq_zero
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       (∫ z : ComplexChartSpace m, F z * (dbarSchwartzCLM j φ) z) = 0
   ```

   Pseudocode:

   ```lean
   obtain ⟨G, hFG, hG_dbar_zero⟩ :=
     exists_local_dbarClosed_schwartz_representative
       U hU_open F hF_holo φ hφ j
   exact
     integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
       F G φ j hFG hG_dbar_zero
   ```

   The product-kernel consumer is now checked in the same file.  It rewrites
   the kernel by the checked product-kernel representation on the supported
   test `dbarSchwartzCLM j φ`, then applies the local holomorphic integral
   theorem to the scalar kernel `G ψ`.

   ```lean
   theorem regularizedEnvelope_productKernel_dbar_eq_zero
       {m : ℕ} {r : ℝ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
       (U0 : Set (ComplexChartSpace m))
       (hU0_open : IsOpen U0)
       (hG_holo :
         ∀ ψ, KernelSupportWithin ψ r -> DifferentiableOn ℂ (G ψ) U0)
       (hK_rep :
         ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, G ψ z * φ z)
       (j : Fin m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ : KernelSupportWithin ψ r) :
       K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0

   theorem translationCovariantKernel_distributionalHolomorphic
       {m : ℕ} {r : ℝ} {ι : Type*} {l : Filter ι} [NeBot l]
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (ψι : ι -> SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_support :
         ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
       (hψ_approx :
         ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto
             (fun i => realConvolutionTest θ (ψι i))
             l
             (nhds θ))
       (hdesc :
         ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ))
       (hK_dbar_zero :
         ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0) :
       IsDistributionalHolomorphicOn Hdist U0
   ```

   Lean proof of the first theorem:

   ```lean
   rw [hK_rep (dbarSchwartzCLM j φ) ψ (hφ.dbar j) hψ]
   exact
     integral_holomorphic_mul_dbarSchwartz_eq_zero
       U0 hU0_open (G ψ) (hG_holo ψ hψ) φ hφ j
   ```

   The distributional-holomorphicity theorem above is now checked under the
   displayed concrete approximate-identity hypotheses.  Thus the next unchecked
   declaration in this layer is no longer the product-kernel `∂bar` consumer or
   the continuity passage theorem; it is the genuine approximate-identity
   construction that supplies `hψ_support` and `hψ_approx`.

   Lean proof transcript for the checked continuity-passage theorem:

   ```lean
   intro j φ hφ
   let θ : SchwartzMap (ComplexChartSpace m) ℂ := dbarSchwartzCLM j φ
   have hlim :
       Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
         l (nhds (Hdist θ)) :=
     (Hdist.continuous.tendsto θ).comp (hψ_approx θ)
   have hzero_eventually :
       ∀ᶠ i in l, Hdist (realConvolutionTest θ (ψι i)) = 0 := by
     filter_upwards [hψ_support] with i hi
     have hK0 := hK_dbar_zero j φ (ψι i) hφ hi
     have hdesc_i := hdesc θ (ψι i)
     rw [← hdesc_i]
     exact hK0
   have heq :
       (fun i => Hdist (realConvolutionTest θ (ψι i))) =ᶠ[l]
         fun _ => (0 : ℂ) :=
     hzero_eventually
   have hlim0 :
       Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
         l (nhds (0 : ℂ)) :=
     tendsto_const_nhds.congr' heq.symm
   exact tendsto_nhds_unique hlim hlim0
   ```

   The remaining analytic theorem below this surface is the genuine
   approximate-identity construction: for every fixed positive support radius
   `r`, construct `ψι` with eventual `KernelSupportWithin (ψι i) r` and prove
   `hψ_approx` for all complex-chart Schwartz tests.

   The next proof-doc/Lean target must be the following concrete theorem, not
   a bundled approximation structure:

   ```lean
   theorem exists_realConvolutionTest_approxIdentity
       {m : ℕ} {r : ℝ} (hr : 0 < r) :
       ∃ ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1) ∧
         (∀ n,
           KernelSupportWithin (ψn n)
             (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
         (∀ n, KernelSupportWithin (ψn n) r) ∧
         (∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto
             (fun n => realConvolutionTest θ (ψn n))
             atTop
             (nhds θ))
   ```

   The proof must be split into two honest pieces:

   ```lean
   theorem exists_normalized_schwartz_bump_kernelSupportWithin
       {m : ℕ} (ε : ℝ) (hε : 0 < ε) :
       ∃ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ t, 0 ≤ (ψ t).re) ∧
         (∀ t, (ψ t).im = 0) ∧
         (∫ t : Fin m -> ℝ, ψ t = 1) ∧
         KernelSupportWithin ψ ε
   ```

   This theorem is now checked in
   `SCV/DistributionalEOWApproxIdentity.lean`.  It is the centered
   finite-dimensional version of the Wightman source theorem
   `exists_approx_identity_schwartz`, but ported into pure SCV rather than
   imported.  The proof uses `ContDiffBump (0 : Fin m -> ℝ)` with radii
   `ε / 4` and `ε / 2`, converts the real bump to a complex-valued compact
   supported smooth function, and normalizes by the nonzero integral supplied
   by `ContDiffBump.integral_pos`.  The support proof is simpler than the
   positive-time Wightman source: after normalizing,
   `tsupport_smul_subset_right` and the bump support theorem give containment
   in `closedBall 0 (ε / 2)`, hence in `closedBall 0 ε`.

   The sequence-selection wrapper with explicit fields is also checked:

   ```lean
   theorem exists_shrinking_normalized_schwartz_bump_sequence
       {m : ℕ} {r : ℝ} (hr : 0 < r) :
       ∃ ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ n t, 0 ≤ (ψn n t).re) ∧
         (∀ n t, (ψn n t).im = 0) ∧
         (∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1) ∧
         (∀ n,
           KernelSupportWithin (ψn n)
             (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
         (∀ n, KernelSupportWithin (ψn n) r)
   ```

   It chooses the preceding bump at radius
   `min (r / 2) (1 / (n + 1 : ℝ))`.  This is still genuine content, not the
   difficult convergence theorem: it supplies normalized compact kernels with
   shrinking support and the fixed-radius support hypothesis needed by
   `translationCovariantKernel_distributionalHolomorphic`.

   ```lean
   theorem tendsto_realConvolutionTest_of_shrinking_normalized_support
       {m : ℕ}
       (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
       (hψ_real : ∀ n t, (ψn n t).im = 0)
       (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
       (hψ_support :
         ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
       ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
         Tendsto
           (fun n => realConvolutionTest θ (ψn n))
           atTop
           (nhds θ)
   ```

   The convergence proof should use the Schwartz seminorm topology directly.
   The implementation belongs in the approximate-identity companion, not in
   `SCV/DistributionalEOWKernel.lean`.  The first line of the proof is the
   standard `WithSeminorms` reduction:

   ```lean
   rw [(schwartz_withSeminorms ℂ (ComplexChartSpace m) ℂ).tendsto_nhds_atTop _ _]
   intro ⟨k, l⟩ ε hε
   ```

   and the goal is to prove, eventually in `n`,

   ```lean
   SchwartzMap.seminorm ℂ k l
     (realConvolutionTest θ (ψn n) - θ) < ε
   ```

   The proof is Lean-ready only after the following local theorem slots are
   present.  The first four are elementary and should be checked before the
   convergence theorem itself.

   ```lean
   theorem integral_norm_eq_one_of_real_nonneg_normalized
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_nonneg : ∀ t : Fin m -> ℝ, 0 ≤ (ψ t).re)
       (hψ_real : ∀ t : Fin m -> ℝ, (ψ t).im = 0)
       (hψ_norm : ∫ t : Fin m -> ℝ, ψ t = 1) :
       ∫ t : Fin m -> ℝ, ‖ψ t‖ = 1
   ```

   Proof transcript: prove pointwise
   `‖ψ t‖ = (ψ t).re` by `Complex.ext`, `Complex.norm_real`, and
   `Real.norm_eq_abs`; then use
   `integral_congr_ae`, `integral_re ψ.integrable`, and `hψ_norm`.

   ```lean
   theorem norm_realEmbed_le (t : Fin m -> ℝ) :
       ‖realEmbed t‖ ≤ ‖t‖
   ```

   Proof transcript: rewrite by `pi_norm_le_iff_of_nonneg`; each coordinate is
   `Complex.norm_real (t i)` and is bounded by `norm_le_pi_norm t i`.

   ```lean
   theorem continuous_realEmbed :
       Continuous (realEmbed : (Fin m -> ℝ) -> ComplexChartSpace m)
   ```

   Proof transcript: use `continuous_pi`; each coordinate is
   `Complex.continuous_ofReal.comp (continuous_apply i)`.

   ```lean
   theorem kernel_eq_zero_of_not_mem_closedBall
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) {r : ℝ} {t : Fin m -> ℝ}
       (hψ : KernelSupportWithin ψ r)
       (ht : t ∉ Metric.closedBall (0 : Fin m -> ℝ) r) :
       ψ t = 0
   ```

   Proof transcript: apply `image_eq_zero_of_notMem_tsupport`; membership in
   `tsupport ψ` would contradict `ht` through `hψ`.

   ```lean
   theorem iteratedFDeriv_sub_realEmbed_right
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (t : Fin m -> ℝ) (l : ℕ) (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (fun z : ComplexChartSpace m => θ (z - realEmbed t)) z =
         iteratedFDeriv ℝ l
           (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t)
   ```

   Proof transcript: `simpa [sub_eq_add_neg]` using
   `iteratedFDeriv_comp_add_right` with translation vector `-(realEmbed t)`.

   ```lean
   theorem integrable_smul_iteratedFDeriv_translate
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (l : ℕ) (z : ComplexChartSpace m) :
       Integrable (fun t : Fin m -> ℝ =>
         (ψ t) • iteratedFDeriv ℝ l
           (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t))
   ```

   Proof transcript: set `C = SchwartzMap.seminorm ℂ 0 l θ`; dominate the
   norm by `C * ‖ψ t‖` using
   `SchwartzMap.norm_iteratedFDeriv_le_seminorm`; integrability is
   `ψ.integrable.norm.const_mul C`.  Measurability comes from
   `continuous_realEmbed`, continuity of
   `θ.smooth l |>.continuous_iteratedFDeriv`, and continuity of scalar
   multiplication.

   The base case of derivative-through-convolution is already an independent
   theorem:

   ```lean
   theorem iteratedFDeriv_zero_realConvolutionTest_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ 0
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z =
         ∫ t : Fin m -> ℝ,
           (ψ t) • iteratedFDeriv ℝ 0
             (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t)
   ```

   Proof transcript: extensionality on the `Fin 0` multilinear map, rewrite by
   `iteratedFDeriv_zero_apply`, move application through the integral by
   `ContinuousMultilinearMap.integral_apply`, using
   `integrable_smul_iteratedFDeriv_translate θ ψ 0 z`, and finish by
   `realConvolutionTest_apply`.

   The derivative-through-convolution theorem is the first nontrivial
   analytic bridge beyond that base case.  Its exact target is:

   ```lean
   theorem iteratedFDeriv_realConvolutionTest_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (l : ℕ) (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z =
         ∫ t : Fin m -> ℝ,
           (ψ t) •
           iteratedFDeriv ℝ l
               (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t)
   ```

   Before the all-orders theorem, the first derivative must be checked as its
   own concrete package.  The required real-linear embedding is not an
   abstract route assumption; it is the coordinate map already used by the
   shear:

   ```lean
   private def realEmbedCLMApprox :
       (Fin m -> ℝ) ->L[ℝ] ComplexChartSpace m :=
     ContinuousLinearMap.pi fun i =>
       Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

   @[simp] private theorem realEmbedCLMApprox_apply
       (t : Fin m -> ℝ) :
       realEmbedCLMApprox t = realEmbed t
   ```

   Proof transcript: extensionality in `i`, then
   `simp [realEmbedCLMApprox, realEmbed]`.  Keeping this helper private in the
   approximate-identity file is acceptable: it exposes no new mathematical
   theorem surface and only gives Lean the continuous-linear structure needed
   to compute the derivative of the shear.

   The pointwise base derivative of the sheared tensor product is:

   ```lean
   theorem fderiv_shearedTensor_base_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z v : ComplexChartSpace m) (t : Fin m -> ℝ) :
       fderiv ℝ
         (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
           θ (p.1 - realEmbed p.2) * ψ p.2)
         (z, t)
         ((ContinuousLinearMap.inl ℝ
           (ComplexChartSpace m) (Fin m -> ℝ)) v)
       =
       (ψ t) •
         fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
           (z - realEmbed t) v
   ```

   Lean proof transcript.  Set
   ```
   fstCLM := ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m -> ℝ)
   sndCLM := ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m -> ℝ)
   L := fstCLM - realEmbedCLMApprox.comp sndCLM
   A p := θ (p.1 - realEmbed p.2)
   B p := ψ p.2
   ```
   Prove `hL_apply : L p = p.1 - realEmbed p.2` by `simp`.  Rewrite
   `A = fun p => θ (L p)`, then get
   ```
   hA_deriv :
     HasFDerivAt A ((fderiv ℝ θ (z - realEmbed t)).comp L) (z,t)
   ```
   from `θ.differentiableAt.hasFDerivAt.comp`.
   Similarly,
   ```
   hB_deriv :
     HasFDerivAt B ((fderiv ℝ ψ t).comp sndCLM) (z,t)
   ```
   from `ψ.differentiableAt.hasFDerivAt.comp`.  Apply
   `hA_deriv.mul hB_deriv`, rewrite the original function as
   `fun p => A p * B p`, use `.fderiv`, and evaluate on `inl v`.  The
   `B`-derivative term vanishes because `sndCLM (inl v) = 0`; the shear term
   is `v` because `realEmbed 0 = 0`.  The final simplification is:
   ```lean
   have hreal_zero : realEmbed (0 : Fin m -> ℝ) = 0 := by
     ext i
     simp [realEmbed]
   simp [A, B, L, fstCLM, sndCLM, hreal_zero, smul_eq_mul, mul_comm]
   ```

   The corresponding checked bridge into the existing fiber-integral
   infrastructure is:

   ```lean
   theorem baseFDeriv_realConvolution_kernel_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z v : ComplexChartSpace m) (t : Fin m -> ℝ) :
       baseFDerivSchwartz
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ θ ψ)) (z, t) v =
       (ψ t) •
         fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
           (z - realEmbed t) v
   ```

   Proof transcript: rewrite `baseFDerivSchwartz_apply`, then `change` the
   differentiated function to
   `fun p => θ (p.1 - realEmbed p.2) * ψ p.2`; finish by
   `fderiv_shearedTensor_base_apply`.

   The first derivative of the convolution test is then:

   ```lean
   theorem fderiv_realConvolutionTest_apply_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z v : ComplexChartSpace m) :
       fderiv ℝ
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z v =
       ∫ t : Fin m -> ℝ,
         (ψ t) •
           fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
             (z - realEmbed t) v
   ```

   Proof transcript.  Let
   ```
   F :=
     (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m)) (schwartzTensorProduct₂ θ ψ)
   ```
   and rewrite the left side to
   `fderiv ℝ (complexRealFiberIntegralRaw F) z v`.  Use
   `congrFun (fderiv_complexRealFiberIntegralRaw_eq F) z` to replace the
   derivative by `complexRealFiberIntegralRaw (baseFDerivSchwartz F) z`.
   Change this to
   `(∫ t, baseFDerivSchwartz F (z,t)) v`, move evaluation through the
   Bochner integral by
   `ContinuousLinearMap.integral_apply
     (integrable_complexRealFiber (baseFDerivSchwartz F) z) v`,
   and close by `integral_congr_ae` plus
   `baseFDeriv_realConvolution_kernel_apply`.

   The unevaluated continuous-linear-map version is also part of this stage:

   ```lean
   theorem integrable_smul_fderiv_translate
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       Integrable (fun t : Fin m -> ℝ =>
         (ψ t) •
           fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
             (z - realEmbed t))

   theorem fderiv_realConvolutionTest_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       fderiv ℝ
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z =
       ∫ t : Fin m -> ℝ,
         (ψ t) •
           fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
             (z - realEmbed t)
   ```

   Proof transcript: for integrability, reuse
   `integrable_complexRealFiber (baseFDerivSchwartz F) z` for the same
   sheared tensor `F` and transfer by ae-equality, extensional in the
   continuous-linear-map argument, using
   `baseFDeriv_realConvolution_kernel_apply`.  For the equality, ext on a
   direction `v`, move evaluation through the integral using
   `ContinuousLinearMap.integral_apply`, and apply
   `fderiv_realConvolutionTest_apply_eq_integral`.

   The all-orders theorem should not be proved by fragile `Fin 1`
   curry/uncurry conversions.  The clean route is to commute **directional**
   derivatives through the convolution test, then use
   `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`.

   First prove:

   ```lean
   theorem lineDerivOp_realConvolutionTest
       (v : ComplexChartSpace m)
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       ∂_{v} (realConvolutionTest θ ψ) =
         realConvolutionTest (∂_{v} θ) ψ
   ```

   Proof transcript: ext on `z`; rewrite the left side with
   `SchwartzMap.lineDerivOp_apply_eq_fderiv`; use
   `fderiv_realConvolutionTest_apply_eq_integral`; rewrite the right side by
   `realConvolutionTest_apply`; close by `integral_congr_ae`,
   `SchwartzMap.lineDerivOp_apply_eq_fderiv`, and commutativity of complex
   multiplication.

   Then prove the iterated directional version:

   ```lean
   theorem iteratedLineDerivOp_realConvolutionTest
       {l : ℕ} (u : Fin l -> ComplexChartSpace m)
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       ∂^{u} (realConvolutionTest θ ψ) =
         realConvolutionTest (∂^{u} θ) ψ
   ```

   Proof transcript: induction on `l`.  The zero case is
   `LineDeriv.iteratedLineDerivOp_fin_zero`.  In the successor case rewrite
   both sides by `LineDeriv.iteratedLineDerivOp_succ_left`, apply the
   induction hypothesis to `Fin.tail u`, and finish with
   `lineDerivOp_realConvolutionTest (u 0) (∂^{Fin.tail u} θ) ψ`.

   The applied all-orders derivative-through-convolution theorem is then:

   ```lean
   theorem iteratedFDeriv_realConvolutionTest_eq_integral_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (l : ℕ) (z : ComplexChartSpace m)
       (v : Fin l -> ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z v =
       ∫ t : Fin m -> ℝ,
         (ψ t) *
           iteratedFDeriv ℝ l
             (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) v
   ```

   Proof transcript: rewrite the left side to
   `(∂^{v} (realConvolutionTest θ ψ)) z` using
   `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`, then use
   `iteratedLineDerivOp_realConvolutionTest` and
   `realConvolutionTest_apply`.  Convert
   `(∂^{v} θ) (z - realEmbed t)` back to
   `iteratedFDeriv ℝ l θ (z - realEmbed t) v` pointwise by
   `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`; finish with
   commutativity of multiplication under `integral_congr_ae`.

   The non-applied continuous-multilinear theorem above is recovered by
   extensionality and `ContinuousMultilinearMap.integral_apply` using the
   already checked `integrable_smul_iteratedFDeriv_translate`.

   With `hψ_norm`, the exact consumer form is:

   ```lean
   theorem iteratedFDeriv_realConvolutionTest_sub_eq_integral_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_norm : ∫ t : Fin m -> ℝ, ψ t = 1)
       (l : ℕ) (z : ComplexChartSpace m)
       (v : Fin l -> ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ - θ : ComplexChartSpace m -> ℂ) z v =
       ∫ t : Fin m -> ℝ,
         (ψ t) *
           (iteratedFDeriv ℝ l
              (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) v -
            iteratedFDeriv ℝ l
              (θ : ComplexChartSpace m -> ℂ) z v)

   theorem iteratedFDeriv_realConvolutionTest_sub_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_norm : ∫ t : Fin m -> ℝ, ψ t = 1)
       (l : ℕ) (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ - θ : ComplexChartSpace m -> ℂ) z =
         ∫ t : Fin m -> ℝ,
           (ψ t) •
             (iteratedFDeriv ℝ l
                (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) -
              iteratedFDeriv ℝ l
                (θ : ComplexChartSpace m -> ℂ) z)
   ```

   Proof transcript for the non-applied theorem: rewrite the Schwartz-map
   subtraction as function addition with a negative term, apply
   `iteratedFDeriv_add_apply` and `iteratedFDeriv_neg_apply`, then insert
   `iteratedFDeriv_realConvolutionTest_eq_integral`.  Rewrite
   ```
   ∫ t, (ψ t) • iteratedFDeriv ℝ l θ z
   ```
   as `iteratedFDeriv ℝ l θ z` by `integral_smul_const` and `hψ_norm`.
   Use `integral_sub` at the continuous-multilinear-map level, with
   integrability from `integrable_smul_iteratedFDeriv_translate` and
   `ψ.integrable.smul_const`, and finish by pointwise `smul_sub`.  The applied
   theorem follows afterward by applying both sides to `v` and moving
   evaluation through the integral with `ContinuousMultilinearMap.integral_apply`;
   the final scalar simplification is `smul_eq_mul` and `mul_sub`.

   The global small-translation estimate is the real mathematical heart of
   the convergence proof.  The endorsed Lean route is the direct mean-value
   estimate below, not the older compact/tail split.  For Schwartz functions
   the mean-value proof is stronger and shorter: one derivative is spent, and
   the polynomial weight at `z` is compared to the polynomial weight at
   `z - s • realEmbed t` using `‖t‖ ≤ 1`.

   First prove the quantitative linear estimate:

   ```lean
   theorem exists_weighted_iteratedFDeriv_realTranslate_sub_le_linear
       (θ : SchwartzMap (ComplexChartSpace m) ℂ) (k l : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ (z : ComplexChartSpace m) (t : Fin m -> ℝ),
           ‖t‖ ≤ 1 ->
             ‖z‖ ^ k *
               ‖iteratedFDeriv ℝ l
                   (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) -
                 iteratedFDeriv ℝ l
                   (θ : ComplexChartSpace m -> ℂ) z‖ ≤ C * ‖t‖
   ```

   Lean proof transcript.  Let
   `D w = iteratedFDeriv ℝ l (θ : ComplexChartSpace m -> ℂ) w` and set
   ```
   C = 2 ^ (k - 1) *
     (SchwartzMap.seminorm ℂ k (l + 1) θ +
      SchwartzMap.seminorm ℂ 0 (l + 1) θ)
   ```
   (any nonnegative larger constant is fine).  For fixed `z,t`, define the
   one-variable path
   ```
   γ s = ‖z‖ ^ k • D (z - s • realEmbed t)
   ```
   and apply `norm_image_sub_le_of_norm_deriv_le_segment_01'` on `[0,1]`.
   The derivative is
   ```
   ‖z‖ ^ k •
     fderiv ℝ D (z - s • realEmbed t) (-(realEmbed t))
   ```
   by the chain rule.  Use `norm_fderiv_iteratedFDeriv` to rewrite
   `‖fderiv ℝ D w‖` as
   `‖iteratedFDeriv ℝ (l + 1) (θ : ComplexChartSpace m -> ℂ) w‖`.
   If `s ∈ Set.Ico 0 1` and `‖t‖ ≤ 1`, then
   `norm_realEmbed_le t` gives `‖s • realEmbed t‖ ≤ 1` and therefore
   ```
   ‖z‖ = ‖(z - s • realEmbed t) + s • realEmbed t‖
        ≤ ‖z - s • realEmbed t‖ + 1.
   ```
   The elementary inequality `add_pow_le` yields
   ```
   ‖z‖ ^ k * ‖D_{l+1} θ (z - s • realEmbed t)‖
     ≤ 2 ^ (k - 1) *
       (SchwartzMap.seminorm ℂ k (l + 1) θ +
        SchwartzMap.seminorm ℂ 0 (l + 1) θ).
   ```
   Multiplying by `‖realEmbed t‖ ≤ ‖t‖` gives the derivative bound required by
   the mean-value theorem.  Finally identify
   `γ 1 - γ 0` with
   `‖z‖ ^ k • (D (z - realEmbed t) - D z)` and remove the scalar norm.

   The qualitative small-translation theorem is then just this linear estimate
   with `δ = min 1 (ε / (C + 1))`:

   ```lean
   theorem weighted_iteratedFDeriv_realTranslate_sub_tendsto_zero
       (θ : SchwartzMap (ComplexChartSpace m) ℂ) (k l : ℕ) :
       ∀ ε > 0, ∃ δ > 0, ∀ (z : ComplexChartSpace m) (t : Fin m -> ℝ),
         ‖t‖ < δ ->
           ‖z‖ ^ k *
             ‖iteratedFDeriv ℝ l
                 (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) -
               iteratedFDeriv ℝ l
                 (θ : ComplexChartSpace m -> ℂ) z‖ < ε
   ```

   The convergence theorem then has a short transcript.  Given `k,l,ε`, take
   `δ` from the weighted translation theorem with `ε / 2`.  From
   `tendsto_one_div_add_atTop_nhds_zero_nat`, choose `N` so
   `1 / (n + 1 : ℝ) < δ` for `n ≥ N`.  For such `n`, if
   `ψn n t ≠ 0`, `hψ_support n` and
   `kernel_eq_zero_of_not_mem_closedBall` force `‖t‖ ≤ 1 / (n + 1) < δ`.
   Hence the weighted derivative difference is `< ε / 2` on the support and
   the integrand is zero off the support.  Using
   `iteratedFDeriv_realConvolutionTest_sub_eq_integral`,
   `norm_integral_le_integral_norm`, `norm_smul`, and
   `integral_norm_eq_one_of_real_nonneg_normalized`, prove for every `z`
   ```
   ‖z‖ ^ k *
     ‖iteratedFDeriv ℝ l
       (realConvolutionTest θ (ψn n) - θ : ComplexChartSpace m -> ℂ) z‖
       ≤ ε / 2.
   ```
   Then apply
   ```lean
   SchwartzMap.seminorm_le_bound ℂ k l
     (realConvolutionTest θ (ψn n) - θ)
   ```
   and finish with `half_lt_self hε`.

   Finally, package the checked bump sequence:

   ```lean
   theorem exists_realConvolutionTest_approxIdentity
       {m : ℕ} {r : ℝ} (hr : 0 < r) :
       ∃ ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1) ∧
         (∀ n,
           KernelSupportWithin (ψn n)
             (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
         (∀ n, KernelSupportWithin (ψn n) r) ∧
         (∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto
             (fun n => realConvolutionTest θ (ψn n))
             atTop
             (nhds θ))
   ```

   Its proof uses `exists_shrinking_normalized_schwartz_bump_sequence hr`;
   the nonnegativity and real-valuedness fields are kept internally to call
   `tendsto_realConvolutionTest_of_shrinking_normalized_support`, while the
   public theorem only exports the fields consumed by
   `translationCovariantKernel_distributionalHolomorphic`.

   This approximate-identity package is now checked in
   `SCV/DistributionalEOWApproxIdentity.lean`.  It is the concrete input
   consumed by the checked
   `translationCovariantKernel_distributionalHolomorphic`; no opaque
   approximate-identity assumption is used.
7. Apply `distributionalHolomorphic_regular` to obtain a genuine holomorphic
   function `H` on `U0` representing `Hdist`.

   Lean-ready transcript for `distributionalHolomorphic_regular`.  This is the
   standard local Weyl regularity theorem for the `∂bar` complex, specialized
   to the repo's complex-chart tempered-distribution surface.  It is pure SCV:
   no OS, Wightman, BHW, Hamiltonian, or boundary-value hypotheses enter this
   theorem.

   The public theorem surface remains:

   ```lean
   theorem distributionalHolomorphic_regular
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0) :
       ∃ H : ComplexChartSpace m -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         RepresentsDistributionOnComplexDomain Hdist H U0
   ```

   Implement it in a new focused file
   `SCV/DistributionalEOWRegularity.lean`, importing the checked
   `DistributionalEOWApproxIdentity` and mathlib's distribution derivative
   files.  Do not put it back into the large kernel file.

   The first internal layer is the test-function `∂/∂z_j` operator, support
   preservation, commutation of the real coordinate derivatives, and the real
   Laplacian identity.  These are genuine finite-dimensional calculus facts,
   not wrappers.  The Lean implementation should be staged so that the
   support/commutation package is checked before the Laplacian and Weyl
   layers are attempted.

   ```lean
   def dzSchwartzCLM {m : ℕ} (j : Fin m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     (1 / 2 : ℂ) •
       (directionalDerivSchwartzCLM (complexRealDir j) -
         Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

   theorem dzSchwartzCLM_tsupport_subset
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ)

   theorem SupportsInOpen.dz
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (j : Fin m) :
       SupportsInOpen ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) U0

   theorem dbar_dzSchwartzCLM_comm
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       dbarSchwartzCLM j (dzSchwartzCLM j φ) =
         dzSchwartzCLM j (dbarSchwartzCLM j φ)
   ```

   The first checked slice of `SCV/DistributionalEOWRegularity.lean` now
   contains the following local calculus package:

   ```lean
   def dzSchwartzCLM {m : ℕ} (j : Fin m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ

   theorem dzSchwartzCLM_tsupport_subset
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ)

   theorem SupportsInOpen.dz
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (j : Fin m) :
       SupportsInOpen ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) U0

   theorem lineDerivOp_comm_complex
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (v w : ComplexChartSpace m) :
       ∂_{v} ((∂_{w} φ : SchwartzMap (ComplexChartSpace m) ℂ)) =
         ∂_{w} ((∂_{v} φ : SchwartzMap (ComplexChartSpace m) ℂ))

   theorem directionalDerivSchwartzCLM_comm
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (v w : ComplexChartSpace m) :
       directionalDerivSchwartzCLM v (directionalDerivSchwartzCLM w φ) =
         directionalDerivSchwartzCLM w (directionalDerivSchwartzCLM v φ)

   theorem dbar_dzSchwartzCLM_comm
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       dbarSchwartzCLM j (dzSchwartzCLM j φ) =
         dzSchwartzCLM j (dbarSchwartzCLM j φ)
   ```

   Proof transcript for this first slice.  The definition of `dzSchwartzCLM`
   is the standard Wirtinger operator
   `1/2 (D_{x_j} - i D_{y_j})` on tests.  Its support lemma is literally the
   checked `dbarSchwartzCLM_tsupport_subset` proof with `Complex.I` replaced
   by `-Complex.I`: use `directionalDerivSchwartzCLM_tsupport_subset` for
   both real coordinate derivatives, then use `tsupport_smul_subset_right` and
   `tsupport_add` for the finite linear combination.  `SupportsInOpen.dz`
   follows by the same `subset_tsupport` argument as `SupportsInOpen.dbar`.
   The commutation lemma is copied from the checked
   `SCV.TranslationDifferentiation.lineDerivOp_comm` proof, with domain
   `ComplexChartSpace m`: at each point, `φ.contDiffAt 2` gives
   `isSymmSndFDerivAt`; converting both iterated line derivatives to
   `iteratedFDeriv ℝ 2` and swapping the two inputs proves equality.  Finally
   `dbar_dzSchwartzCLM_comm` expands the two continuous linear maps and uses
   the real-direction commutation for `complexRealDir j` and
   `complexImagDir j`.  The scalar algebra is the identity
   `(D_x + i D_y)(D_x - i D_y) = (D_x - i D_y)(D_x + i D_y)` after the two
   mixed derivatives have been identified.

   The second internal layer is now also checked, with one important Lean-side
   correction.  The repo's `ComplexChartSpace m` is the plain finite Pi chart
   carrying the existing Schwartz-space norm, not Mathlib's `PiLp 2`
   Euclidean type.  Therefore the production theorem must not impose a fake
   `InnerProductSpace ℝ (ComplexChartSpace m)` instance just to call
   `LineDeriv.laplacianCLM`.  Instead, define the honest coordinate Laplacian
   used by the SCV proof:

   ```lean
   def complexChartLaplacianSchwartzCLM {m : ℕ} :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     ∑ j : Fin m,
       ((directionalDerivSchwartzCLM (complexRealDir j)).comp
           (directionalDerivSchwartzCLM (complexRealDir j)) +
         (directionalDerivSchwartzCLM (complexImagDir j)).comp
           (directionalDerivSchwartzCLM (complexImagDir j)))

   theorem complexChartLaplacianSchwartzCLM_apply
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexChartLaplacianSchwartzCLM φ =
         ∑ j : Fin m,
           (directionalDerivSchwartzCLM (complexRealDir j)
               (directionalDerivSchwartzCLM (complexRealDir j) φ) +
             directionalDerivSchwartzCLM (complexImagDir j)
               (directionalDerivSchwartzCLM (complexImagDir j) φ))

   theorem four_dbar_dzSchwartzCLM_eq_real_imag_second
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       (4 : ℂ) • dbarSchwartzCLM j (dzSchwartzCLM j φ) =
         directionalDerivSchwartzCLM (complexRealDir j)
             (directionalDerivSchwartzCLM (complexRealDir j) φ) +
           directionalDerivSchwartzCLM (complexImagDir j)
             (directionalDerivSchwartzCLM (complexImagDir j) φ)

   theorem complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexChartLaplacianSchwartzCLM φ =
         (4 : ℂ) •
           ∑ j : Fin m, dbarSchwartzCLM j (dzSchwartzCLM j φ)

   theorem local_laplacian_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       Hdist (complexChartLaplacianSchwartzCLM φ) = 0
   ```

   Proof transcript for the checked coordinate Laplacian layer.  The apply
   theorem is just evaluation of a finite sum of continuous linear maps.
   For each coordinate, expand `dbarSchwartzCLM` and `dzSchwartzCLM`, use
   `directionalDerivSchwartzCLM_comm` to identify the mixed derivatives, and
   simplify the scalar identity `I^2 = -1`; this proves
   `four_dbar_dzSchwartzCLM_eq_real_imag_second`.  Summing over `Fin m` gives
   `complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz`.  The distributional
   harmonicity theorem then pushes `Hdist` through the scalar and finite sum
   and applies `hCR j (dzSchwartzCLM j φ) (hφ.dz j)`.

   The older candidate theorem below was intentionally rejected during
   implementation:

   ```lean
   theorem laplacianSchwartzCLM_eq_four_sum_dbar_dz
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       LineDeriv.laplacianCLM ℝ (ComplexChartSpace m)
           (SchwartzMap (ComplexChartSpace m) ℂ) φ =
           (4 : ℂ) •
           ∑ j : Fin m, dbarSchwartzCLM j (dzSchwartzCLM j φ)

   theorem local_laplacian_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       Hdist
         (LineDeriv.laplacianCLM ℝ (ComplexChartSpace m)
               (SchwartzMap (ComplexChartSpace m) ℂ) φ) = 0
   ```

   It is mathematically equivalent only after transporting the plain chart to
   a Euclidean `PiLp 2` model, but it is not a Lean-ready statement on
   `ComplexChartSpace m` itself.  The Euclidean transport belongs in the Weyl
   theorem proof, where norm-equivalence and chart linear-equivalence
   bookkeeping are unavoidable and mathematically meaningful.

   The hard analytic input is Weyl's lemma for the real Laplacian, localized to
   Schwartz tests.  This is the remaining genuine mathematical theorem for this
   stage; it must be proved or imported as a checked pure-analysis theorem, not
   smuggled as a theorem-2 wrapper:

   ```lean
   theorem weyl_laplacian_distribution_regular_on_open
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hΔ :
         ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
             T (complexChartLaplacianSchwartzCLM φ) = 0) :
       ∃ H : ComplexChartSpace m -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H U0 ∧
         RepresentsDistributionOnComplexDomain T H U0
   ```

   Lean helper sequence for the Weyl transport layer.  The chart equivalence,
   Schwartz-space equivalence, and their apply lemmas are now checked in
   `SCV/DistributionalEOWRegularity.lean`; the remaining transport targets are
   the coordinate-direction lemmas, Laplacian transport, support transport, and
   final Euclidean Weyl application:

   ```lean
   noncomputable def complexChartEuclideanCLE (m : ℕ) :
       ComplexChartSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m * 2)) :=
     (complexChartRealFlattenCLE m).trans
       (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm

   noncomputable def complexChartEuclideanSchwartzCLE (m : ℕ) :
       SchwartzMap (ComplexChartSpace m) ℂ ≃L[ℂ]
         SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ

   theorem complexChartEuclideanSchwartzCLE_apply
       (m : ℕ) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (x : EuclideanSpace ℝ (Fin (m * 2))) :
       complexChartEuclideanSchwartzCLE m φ x =
         φ ((complexChartEuclideanCLE m).symm x)

   theorem complexChartEuclideanSchwartzCLE_symm_apply
       (m : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ)
       (z : ComplexChartSpace m) :
       (complexChartEuclideanSchwartzCLE m).symm φ z =
         φ (complexChartEuclideanCLE m z)

   theorem complexChartEuclideanCLE_realDir
       (j : Fin m) :
       complexChartEuclideanCLE m (complexRealDir j) =
         (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm
           (fun k => if k = finProdFinEquiv (j, (0 : Fin 2)) then 1 else 0)

   theorem complexChartEuclideanCLE_imagDir
       (j : Fin m) :
       complexChartEuclideanCLE m (complexImagDir j) =
         (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm
           (fun k => if k = finProdFinEquiv (j, (1 : Fin 2)) then 1 else 0)

   theorem complexChartLaplacianSchwartzCLM_transport
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexChartEuclideanSchwartzCLE m
           (complexChartLaplacianSchwartzCLM φ) =
         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ (Fin (m * 2)))
           (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ)
           (complexChartEuclideanSchwartzCLE m φ)

   def transportedDistributionToEuclidean
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ) :
       SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ ->L[ℂ] ℂ :=
     T.comp
       ((complexChartEuclideanSchwartzCLE m).symm :
         SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ ->L[ℂ]
           SchwartzMap (ComplexChartSpace m) ℂ)

   theorem supportsInOpen_transport_to_euclidean
       {φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ}
       {U0 : Set (ComplexChartSpace m)}
       (hφ : SupportsInOpen (φ : EuclideanSpace ℝ (Fin (m * 2)) -> ℂ)
         ((complexChartEuclideanCLE m) '' U0)) :
       SupportsInOpen
         (((complexChartEuclideanSchwartzCLE m).symm φ :
             SchwartzMap (ComplexChartSpace m) ℂ) :
           ComplexChartSpace m -> ℂ) U0

   theorem supportsInOpen_transport_from_euclidean
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       {U0 : Set (ComplexChartSpace m)}
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       SupportsInOpen
         ((complexChartEuclideanSchwartzCLE m φ :
             SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) :
           EuclideanSpace ℝ (Fin (m * 2)) -> ℂ)
         ((complexChartEuclideanCLE m) '' U0)

   theorem euclidean_weyl_laplacian_distribution_regular_on_open
       {ι : Type*} [Fintype ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hV_open : IsOpen V)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T φ = ∫ x, H x * φ x

   theorem representsDistributionOnComplexDomain_of_euclidean
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (HE : EuclideanSpace ℝ (Fin (m * 2)) -> ℂ)
       (hHE :
         RepresentsEuclideanDistributionOn
           (transportedDistributionToEuclidean T) HE
           ((complexChartEuclideanCLE m) '' U0)) :
       RepresentsDistributionOnComplexDomain T
         (fun z => HE (complexChartEuclideanCLE m z)) U0
   ```

   Lean transcript for the Euclidean transport lemmas.

   1. `complexChartEuclideanCLE_realDir` and
      `complexChartEuclideanCLE_imagDir` are pure coordinate facts.  Prove
      each by extensionality on `k : Fin (m * 2)`, then write
      `k = finProdFinEquiv (i, b)` using
      `finProdFinEquiv.surjective k`, split `b : Fin 2` with `fin_cases`,
      and simplify with
      `complexChartRealFlattenCLE_apply_re`,
      `complexChartRealFlattenCLE_apply_im`,
      `complexRealDir`, `complexImagDir`, and
      `EuclideanSpace.single_apply`.  These lemmas are not wrappers: they are
      the exact basis-identification facts needed by the Laplacian transport.

   2. Introduce the Euclidean coordinate Laplacian as an internal proof
      adapter, not as a public theorem-2 surface:

      ```lean
      def euclideanCoordinateLaplacianSchwartzCLM
          {ι : Type*} [Fintype ι] [DecidableEq ι] :
          SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
            SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
        ∑ k : ι,
          (LineDeriv.lineDerivOpCLM ℂ
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
              (EuclideanSpace.single k (1 : ℝ))).comp
            (LineDeriv.lineDerivOpCLM ℂ
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
              (EuclideanSpace.single k (1 : ℝ)))

      theorem euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM
          {ι : Type*} [Fintype ι] [DecidableEq ι]
          (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          euclideanCoordinateLaplacianSchwartzCLM φ =
            LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ
      ```

      The proof uses `SchwartzMap.laplacian_eq_sum` with the standard
      Euclidean coordinate orthonormal basis; if Mathlib's
      `stdOrthonormalBasis` is not definitionally the `EuclideanSpace.single`
      basis, instantiate the sum theorem with the coordinate orthonormal basis
      generated by `PiLp.basisFun`/`EuclideanSpace.single` and reindex.  Do not
      assert a fake inner-product structure on `ComplexChartSpace m`.

   3. Prove first-derivative transport from the existing Mathlib theorem:

      ```lean
      theorem complexChartEuclidean_lineDeriv_realDir
          (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
          LineDeriv.lineDerivOp
              (EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) 1)
              (complexChartEuclideanSchwartzCLE m φ) =
            complexChartEuclideanSchwartzCLE m
              (directionalDerivSchwartzCLM (complexRealDir j) φ)

      theorem complexChartEuclidean_lineDeriv_imagDir
          (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
          LineDeriv.lineDerivOp
              (EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) 1)
              (complexChartEuclideanSchwartzCLE m φ) =
            complexChartEuclideanSchwartzCLE m
              (directionalDerivSchwartzCLM (complexImagDir j) φ)
      ```

      Proof skeleton: unfold `complexChartEuclideanSchwartzCLE`, view the
      forward map as `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (complexChartEuclideanCLE m).symm`, apply
      `SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv` with
      `g := (complexChartEuclideanCLE m).symm`, and simplify the transported
      direction using the preceding `realDir`/`imagDir` lemmas.  Apply the
      same theorem a second time for second derivatives.

   4. Prove `complexChartLaplacianSchwartzCLM_transport` by rewriting the
      left-hand side with `complexChartLaplacianSchwartzCLM_apply`, pushing
      `complexChartEuclideanSchwartzCLE m` through the finite sum and addition,
      using the two second-derivative transport identities, and reindexing
      `Fin (m * 2)` by `finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)`.  The
      two `Fin 2` cases produce exactly the real and imaginary coordinate
      summands; `euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM`
      finishes the comparison with Mathlib's Laplacian.

   5. `supportsInOpen_transport_to_euclidean` and
      `supportsInOpen_transport_from_euclidean` are topological-support
      transport lemmas for the two directions of the same homeomorphism.  Use
      `complexChartEuclideanSchwartzCLE_symm_apply` to identify the pulled-back
      function with `φ ∘ complexChartEuclideanCLE`; show compact support from
      `hφ.1.comp_homeomorph` or the corresponding compact-image/preimage
      theorem for the homeomorphism underlying `complexChartEuclideanCLE`; and
      show
      `tsupport (((complexChartEuclideanSchwartzCLE m).symm φ) : _ -> ℂ) ⊆ U0`
      by mapping any point in the support into
      `(complexChartEuclideanCLE m) '' U0` and applying injectivity of
      `complexChartEuclideanCLE m`.  The forward lemma is the same argument
      with `complexChartEuclideanSchwartzCLE_apply`: its support is the
      `complexChartEuclideanCLE m` image of the original support, so it lies in
      `(complexChartEuclideanCLE m) '' U0`.

   6. The final chart Weyl theorem is then a short transport proof once the
      Euclidean theorem is available:

      ```lean
      have hΔE :
          ∀ φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ,
            SupportsInOpen (φ : _ -> ℂ) ((complexChartEuclideanCLE m) '' U0) ->
              transportedDistributionToEuclidean T
                (LineDeriv.laplacianCLM ℝ
                  (EuclideanSpace ℝ (Fin (m * 2)))
                  (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) φ) = 0 := by
        intro φ hφ
        have hback := supportsInOpen_transport_to_euclidean (m := m) hφ
        simpa [transportedDistributionToEuclidean,
          complexChartLaplacianSchwartzCLM_transport] using
          hΔ ((complexChartEuclideanSchwartzCLE m).symm φ) hback

      obtain ⟨HE, hHE_smooth, hHE_rep⟩ :=
        euclidean_weyl_laplacian_distribution_regular_on_open
          (transportedDistributionToEuclidean (m := m) T)
          (hU0_open.image (complexChartEuclideanCLE m).toHomeomorph)
          hΔE
      refine ⟨fun z => HE (complexChartEuclideanCLE m z), ?smooth, ?rep⟩
      ```

      The representation proof is the checked helper
      `representsDistributionOnComplexDomain_of_euclidean`: rewrite `T φ` as
      the transported distribution applied to
      `complexChartEuclideanSchwartzCLE m φ`, use
      `supportsInOpen_transport_from_euclidean` to feed the Euclidean
      representative theorem, then apply
      `integral_comp_complexChartEuclideanCLE` to change variables.  This is
      the exact point where the volume-preserving theorem is consumed.

   The transport proof of `weyl_laplacian_distribution_regular_on_open` then
   applies the Euclidean theorem to
   `transportedDistributionToEuclidean T` on
   `(complexChartEuclideanCLE m) '' U0`.  The support transport lemma moves
   compact support back to `U0`, and
   `complexChartLaplacianSchwartzCLM_transport` converts the checked
   coordinate-Laplacian hypothesis into the Euclidean Laplacian hypothesis.
   The representative on `U0` is
   `fun z => HE (complexChartEuclideanCLE m z)`.  Its real smoothness follows
   by composing `hHE : ContDiffOn ℝ ⊤ HE _` with the continuous linear map
   `complexChartEuclideanCLE m`; the representation identity is transported
   by `SchwartzMap.compCLMOfContinuousLinearEquiv_apply` and the linear
   change-of-variables formula for the finite-dimensional equivalence.

   Checked status of the transport layer:

   ```lean
   theorem complexChartEuclideanCLE_realDir
   theorem complexChartEuclideanCLE_imagDir
   theorem complexChartEuclidean_lineDeriv_realDir
   theorem complexChartEuclidean_lineDeriv_imagDir
   theorem complexChartEuclidean_secondLineDeriv_realDir
   theorem complexChartEuclidean_secondLineDeriv_imagDir
   def euclideanCoordinateLaplacianSchwartzCLM
   theorem euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM
   theorem complexChartLaplacianSchwartzCLM_transport
   def transportedDistributionToEuclidean
   theorem transportedDistributionToEuclidean_apply
   theorem supportsInOpen_transport_to_euclidean
   theorem supportsInOpen_transport_from_euclidean
   theorem complexChartEuclideanCLE_volumePreserving
   theorem integral_comp_complexChartEuclideanCLE
   def RepresentsEuclideanDistributionOn
   theorem representsDistributionOnComplexDomain_of_euclidean
   def euclideanTranslateSchwartzCLM
   theorem euclideanTranslateSchwartz_apply
   def euclideanReflectedTranslate
   theorem euclideanReflectedTranslate_apply
   theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
   theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
   theorem continuous_apply_euclideanTranslateSchwartz_of_isCompactSupport
   theorem continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
   ```

   The chart/representative declarations are checked in
   `SCV/DistributionalEOWRegularity.lean`; the Euclidean moving-kernel
   declarations are checked in `SCV/EuclideanWeyl.lean`.  The remaining Lean
   work for this substage is no longer coordinate, support, Jacobian, or
   reflected-kernel bookkeeping; it is the genuine local Euclidean Weyl theorem.

   Exact remaining theorem surfaces for the Weyl package:

   ```lean
   theorem euclidean_laplacian_distribution_regular_on_ball
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (c : EuclideanSpace ℝ ι) {r R : ℝ}
       (hr : 0 < r) (hrR : r < R)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
             (Metric.ball c R) ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) ∧
         RepresentsEuclideanDistributionOn T H (Metric.ball c r)

   theorem euclidean_weyl_laplacian_distribution_regular_on_open
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hV_open : IsOpen V)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
         RepresentsEuclideanDistributionOn T H V
   ```

   The volume-preserving lemma is not a new analytic input.  It is a finite
   product/permutation calculation: compose the measurable real/imaginary
   complex chart, the coordinate-flattening permutation underlying
   `realBlockFlattenCLE`, and `PiLp.volume_preserving_toLp`.  This proves that
   no Jacobian factor appears in `integral_comp_complexChartEuclideanCLE`.

   Lean-ready Euclidean Weyl proof route.  Do not introduce a theorem-2
   wrapper and do not add an axiom.  Prove the pure Euclidean theorem by the
   standard mollifier-scale-invariance proof of Weyl's lemma.

   The first Euclidean translation, reflected-kernel support, and compact-kernel
   continuity layer is now checked in `SCV/EuclideanWeyl.lean`:

   ```lean
   noncomputable def euclideanTranslateSchwartzCLM
       {ι : Type*} [Fintype ι]
       (a : EuclideanSpace ℝ ι) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
         SchwartzMap (EuclideanSpace ℝ ι) ℂ

   theorem euclideanTranslateSchwartz_apply
       (a : EuclideanSpace ℝ ι)
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x : EuclideanSpace ℝ ι) :
       euclideanTranslateSchwartzCLM a φ x = φ (x + a)

   noncomputable def euclideanReflectedTranslate
       (x : EuclideanSpace ℝ ι)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
     euclideanTranslateSchwartzCLM (-x) ρ

   theorem euclideanReflectedTranslate_apply
       (x y : EuclideanSpace ℝ ι)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       euclideanReflectedTranslate x ρ y = ρ (y - x)

   theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
       {V : Set (EuclideanSpace ℝ ι)}
       {x : EuclideanSpace ℝ ι} {r : ℝ}
       (hx : Metric.closedBall x r ⊆ V)
       (hρ : tsupport (ρ : EuclideanSpace ℝ ι -> ℂ) ⊆
         Metric.closedBall 0 r) :
       SupportsInOpen
         (euclideanReflectedTranslate x ρ :
           EuclideanSpace ℝ ι -> ℂ) V

   theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hρ_compact : HasCompactSupport
         (ρ : EuclideanSpace ℝ ι -> ℂ))
       (a0 : EuclideanSpace ℝ ι) :
       Tendsto
         (fun a : EuclideanSpace ℝ ι =>
           euclideanTranslateSchwartzCLM a ρ)
         (𝓝 a0) (𝓝 (euclideanTranslateSchwartzCLM a0 ρ))

   theorem continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hρ_compact : HasCompactSupport
         (ρ : EuclideanSpace ℝ ι -> ℂ)) :
       Continuous
         (fun x : EuclideanSpace ℝ ι =>
           T (euclideanReflectedTranslate x ρ))
   ```

   The proofs are the existing `translateSchwartz` proofs transported from
   `Fin m -> ℝ` to `EuclideanSpace ℝ ι`: `SchwartzMap.compCLM` for
   translation, `tsupport_comp_eq_preimage` for support, and
   `isCompact_closedBall` for compactness.  This layer is already compiled and
   exported by `SCV.lean`.  The reflected convention is chosen so that the
   eventual regularization is
   `Hρ x = T (euclideanReflectedTranslate x ρ)` and
   `∫ Hρ x * φ x dx = T (ρ̌ * φ)` with Mathlib's convolution convention.

   Next upgrade the checked continuity of distributional mollifications to
   smoothness.  This is the Euclidean analogue of the checked
   translation-differentiation lemmas in `SCV/TranslationDifferentiation.lean`,
   but all variables are Euclidean and no OS data enter:

   ```lean
   theorem hasDerivAt_regularizedDistribution_along
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x v : EuclideanSpace ℝ ι) :
       HasDerivAt
         (fun t : ℝ =>
           T (euclideanReflectedTranslate (x + t • v) ρ))
         (-T (euclideanReflectedTranslate x
           (LineDeriv.lineDerivOp v ρ)))
         0

   theorem contDiff_regularizedDistribution
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hρ_compact : HasCompactSupport
         (ρ : EuclideanSpace ℝ ι -> ℂ)) :
       ContDiff ℝ (⊤ : ℕ∞)
         (fun x => T (euclideanReflectedTranslate x ρ))
   ```

   The first theorem is copied from
   `tendsto_translateSchwartz_nhds_of_isCompactSupport`.  For the derivative
   formula, start with one direction `v` and prove the displayed
   one-variable difference quotient
   using `SCV.exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le`
   ported to `EuclideanSpace`; compose the limit with `T.continuous`.
   Iterate this directional statement, or equivalently prove the corresponding
   Fréchet derivative statement, to obtain `contDiff_regularizedDistribution`.
   The exact sign is fixed by
   `euclideanReflectedTranslate x ρ y = ρ (y - x)`.

   The scale-invariance heart of Weyl's lemma is a pure radial-bump theorem.
   Use Mathlib `ContDiffBump (0 : EuclideanSpace ℝ ι)` and its normalized
   form.  For `0 < ε`, let `weylBump ε` be the normalized bump with support in
   `closedBall 0 ε`.

   ```lean
   noncomputable def euclideanWeylBump
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (ε : ℝ) (hε : 0 < ε) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ

   theorem euclideanWeylBump_normalized
       (ε : ℝ) (hε : 0 < ε) :
       ∫ x : EuclideanSpace ℝ ι, euclideanWeylBump ε hε x = 1

   theorem euclideanWeylBump_support
       (ε : ℝ) (hε : 0 < ε) :
       tsupport (euclideanWeylBump ε hε :
         EuclideanSpace ℝ ι -> ℂ) ⊆ Metric.closedBall 0 ε

   theorem exists_compactSmooth_laplacian_eq_bump_sub_bump
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
           (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A =
           euclideanWeylBump ε hε - euclideanWeylBump δ hδ
   ```

   The last theorem is the only hard scalar-analysis sublemma inside the Weyl
   proof.  It is the compactly supported radial Poisson equation for a
   zero-integral radial right-hand side.  Split its proof into the following
   scalar/profile lemmas so the final theorem is not an opaque parametrix
   wrapper:

   ```lean
   def radialProfileLaplacian (N : ℕ) (a : ℝ -> ℂ) (r : ℝ) : ℂ :=
     deriv (deriv a) r + ((N - 1 : ℝ) / r) * deriv a r

   theorem laplacian_radialProfile_off_origin
       {N : ℕ} (hN : N = Fintype.card ι)
       {a : ℝ -> ℂ}
       (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Set.Ioi 0))
       (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
       Laplacian.laplacian (fun y : EuclideanSpace ℝ ι => a ‖y‖) x =
         radialProfileLaplacian N a ‖x‖

   theorem exists_compactSupport_radialPrimitive_zeroMass
       {N : ℕ} (hNpos : 0 < N)
       {f : ℝ -> ℂ} {R : ℝ}
       (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
       (hf_support : Function.support f ⊆ Set.Icc 0 R)
       (hf_zeroMass :
         ∫ r in Set.Ioi 0, (r ^ (N - 1)) • f r = 0) :
       ∃ a : ℝ -> ℂ,
         ContDiff ℝ (⊤ : ℕ∞) a ∧
         Function.support a ⊆ Set.Icc 0 R ∧
         ∀ r ∈ Set.Ioi 0, radialProfileLaplacian N a r = f r

   theorem compactSmooth_laplacian_radialPrimitive
       {f : EuclideanSpace ℝ ι -> ℂ}
       (hf_radial : ∃ fp : ℝ -> ℂ, f = fun x => fp ‖x‖)
       (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
       (hf_compact : HasCompactSupport f)
       (hf_integral : ∫ x, f x = 0) :
       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
           (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A =
           hf_compact.toSchwartzMap hf_smooth
   ```

   The proof reduces radial functions on `EuclideanSpace ℝ ι` to the
   one-variable ODE `(r^(N-1) A'(r))' = r^(N-1) F(r)`, with
   `N = Fintype.card ι`; the zero-integral condition from the two normalized
   bumps makes `A'` vanish outside the larger support, hence `A` can be chosen
   compactly supported.  The `N = 0` case is degenerate and easier: the
   Euclidean space is a singleton and the zero-integral right-hand side is
   identically zero.  The `N = 1` case uses the same formula with
   `r^(N-1)=1`; no singular coefficient appears.  Keep these theorems pure
   analysis and independent of `T`, `U0`, OS, Wightman, or EOW.

   From this primitive theorem, prove local scale invariance of a harmonic
   distribution.  The support condition ensures every translated test fed to
   `hΔ` is supported in `V`:

   ```lean
   theorem regularizedDistribution_bump_scale_eq
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0)
       {x : EuclideanSpace ℝ ι} {ε δ : ℝ}
       (hε : 0 < ε) (hδ : 0 < δ)
       (hxε : Metric.closedBall x ε ⊆ V)
       (hxδ : Metric.closedBall x δ ⊆ V) :
       T (euclideanReflectedTranslate x (euclideanWeylBump ε hε)) =
       T (euclideanReflectedTranslate x (euclideanWeylBump δ hδ))
   ```

   Proof: obtain `A` from
   `exists_compactSmooth_laplacian_eq_bump_sub_bump`, translate it by `x`,
   prove its support lies in `V`, use derivative-translation commutation to
   rewrite the Laplacian of the translated `A` as the translated difference of
   bumps, and apply `hΔ` to this compactly supported Schwartz test.

   Now define the local representative on a ball by choosing any bump radius
   small enough to remain inside the larger ball:

   ```lean
   noncomputable def euclideanWeylBallRepresentative
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (c : EuclideanSpace ℝ ι) (R : ℝ)
       (x : EuclideanSpace ℝ ι) : ℂ :=
     if hx : x ∈ Metric.ball c R then
       let ε := (R - dist x c) / 2
       have hε : 0 < ε := by
         dsimp [ε]
         rw [Metric.mem_ball] at hx
         linarith
       T (euclideanReflectedTranslate x
         (euclideanWeylBump ε hε))
     else 0

   theorem euclideanWeylBallRepresentative_eq_regularized
       {r R ε : ℝ} (hrR : r < R) (hε : 0 < ε)
       (hε_support : ∀ x ∈ Metric.ball c r,
         Metric.closedBall x ε ⊆ Metric.ball c R) :
       ∀ x ∈ Metric.ball c r,
         euclideanWeylBallRepresentative T c R x =
           T (euclideanReflectedTranslate x (euclideanWeylBump ε hε))
   ```

   On a smaller ball `ball c r`, choose a uniform `ε < (R - r) / 2`; the
   scale-invariance theorem identifies the chosen variable-radius definition
   with this fixed-ε regularization.  Therefore smoothness on `ball c r`
   follows from `contDiff_regularizedDistribution`.

   Finally prove representation on the smaller ball by approximate identity:

   ```lean
   noncomputable def euclideanConvolutionTest
       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
     SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) φ ρ

   theorem euclideanConvolutionTest_apply
       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x : EuclideanSpace ℝ ι) :
       euclideanConvolutionTest φ ρ x =
         ∫ y : EuclideanSpace ℝ ι, φ (x - y) * ρ y

   theorem euclideanConvolutionTest_eq_integral_reflectedTranslate
       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       euclideanConvolutionTest φ ρ =
         ∫ x : EuclideanSpace ℝ ι,
           φ x • euclideanReflectedTranslate x ρ

   theorem regularizedDistribution_integral_pairing
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       ∫ x, T (euclideanReflectedTranslate x ρ) * φ x =
         T (euclideanConvolutionTest φ ρ)

   theorem tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (ρn : ℕ -> SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hρ_nonneg : ∀ n x, 0 ≤ (ρn n x).re)
       (hρ_real : ∀ n x, (ρn n x).im = 0)
       (hρ_norm : ∀ n, ∫ x, ρn n x = 1)
       (hρ_support : ∀ n,
         tsupport (ρn n : EuclideanSpace ℝ ι -> ℂ) ⊆
           Metric.closedBall 0 (1 / (n + 1 : ℝ))) :
       Tendsto (fun n => euclideanConvolutionTest φ (ρn n))
         atTop (𝓝 φ)

   theorem euclidean_laplacian_distribution_regular_on_ball
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (c : EuclideanSpace ℝ ι) {r R : ℝ}
       (hr : 0 < r) (hrR : r < R)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
             (Metric.ball c R) ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) ∧
         RepresentsEuclideanDistributionOn T H (Metric.ball c r)
   ```

   `euclideanConvolutionTest_eq_integral_reflectedTranslate` is the Bochner
   integral identity in Schwartz space; apply the available
   continuous-linear-map integral theorem to get
   `regularizedDistribution_integral_pairing`.  The pointwise formula is
   Mathlib's `SchwartzMap.convolution_apply`.

   For a test `φ` supported in `ball c r`, choose `ε` small enough that
   `closedBall x ε ⊆ ball c R` for every `x ∈ tsupport φ`; outside
   `tsupport φ` the integral is zero.  Scale invariance lets the fixed
   representative replace every smaller approximate-identity regularization in
   the integral.  The convergence theorem gives
   `T (euclideanConvolutionTest φ ρ_n) -> T φ` by continuity of `T`, while the
   left side is constant for all sufficiently small `ρ_n`; hence it equals
   `T φ`.  This proves the representation identity.

   The open-set theorem is a local assembly over balls:

   ```lean
   theorem exists_finite_schwartz_partitionOfUnity_on_compact
       {ι : Type*} [Fintype ι]
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
       {K : Set E} (hK : IsCompact K)
       {U : ι -> Set E}
       (hU_open : ∀ i, IsOpen (U i))
       (hcover : K ⊆ ⋃ i, U i) :
       ∃ χ : ι -> SchwartzMap E ℂ,
         (∀ i, HasCompactSupport (χ i : E -> ℂ)) ∧
         (∀ i, tsupport (χ i : E -> ℂ) ⊆ U i) ∧
         (∀ x ∈ K, ∑ i, χ i x = 1)

   theorem supportsInOpen_partition_mul
       {χ φ : SchwartzMap E ℂ} {U V : Set E}
       (hχ : tsupport (χ : E -> ℂ) ⊆ U)
       (hφ : SupportsInOpen (φ : E -> ℂ) V) :
       SupportsInOpen
         ((SchwartzMap.smulLeftCLM ℂ (χ : E -> ℂ) φ) : E -> ℂ)
         (U ∩ V)

   theorem euclidean_weyl_laplacian_distribution_regular_on_open
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hV_open : IsOpen V)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
         RepresentsEuclideanDistributionOn T H V
   ```

   For each `x ∈ V`, choose `R_x > 0` with `closedBall x R_x ⊆ V` and apply
   the ball theorem with `r = R_x / 2`.  Define `H x` by the corresponding
   local representative if `x ∈ V`, and `0` outside.  On overlaps, the two
   representatives have identical pairings against all compactly supported
   Schwartz tests in the overlap because both represent `T`; use
   `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` to prove
   pointwise equality.  Smoothness is local from the ball representatives.
   The global representation for a test supported in `V` follows by covering
   `tsupport φ` with finitely many such balls and applying
   `exists_finite_schwartz_partitionOfUnity_on_compact`.  Each product
   `χ i * φ` is a Schwartz test supported in the corresponding ball by
   `supportsInOpen_partition_mul`; apply the local representation to each
   product and sum.  The partition theorem is pure finite-dimensional
   topology/calculus: choose smaller closed neighborhoods inside the open
   cover using normality/compactness, obtain bump functions by
   `exists_contDiff_tsupport_subset`, divide by the finite positive sum on
   `K`, and convert the compactly supported smooth functions to
   `SchwartzMap`s with `HasCompactSupport.toSchwartzMap`.

   After Weyl regularity gives a smooth representative, recover the pointwise
   Cauchy-Riemann equations from the distributional equations.  The pointwise
   operator definition and its global-Schwartz compatibility lemma are now
   checked in `SCV/DistributionalEOWRegularity.lean`:

   ```lean
   def pointwiseDbar (j : Fin m) (H : ComplexChartSpace m -> ℂ)
       (z : ComplexChartSpace m) : ℂ :=
     (1 / 2 : ℂ) *
       (fderiv ℝ H z (complexRealDir j) +
        Complex.I * fderiv ℝ H z (complexImagDir j))

   theorem dbarSchwartzCLM_apply_eq_pointwiseDbar
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (z : ComplexChartSpace m) :
       (dbarSchwartzCLM j φ) z =
         pointwiseDbar j (φ : ComplexChartSpace m -> ℂ) z

   theorem pointwiseDbar_eq_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (H : ComplexChartSpace m -> ℂ)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (hRep : RepresentsDistributionOnComplexDomain Hdist H U0) :
       ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0
   ```

   Proof transcript.  Fix `j` and a compactly supported Schwartz test `φ`
   supported in `U0`.  From `hRep` and `hCR`,
   ```
   0 = Hdist (dbarSchwartzCLM j φ)
     = ∫ z, H z * (dbarSchwartzCLM j φ) z.
   ```
   Choose a smooth compact cutoff equal to one near `tsupport φ`; multiplying
   it by the smooth representative `H` gives a global Schwartz representative
   on the support.  Apply the checked integration-by-parts theorem
   `integral_mul_dbarSchwartzCLM_right_eq_neg_left` to get
   ```
   ∫ z, pointwiseDbar j H z * φ z = 0.
   ```
   Since `pointwiseDbar j H` is continuous on `U0`, the checked pointwise
   extraction theorem
   `eq_zero_on_open_of_compactSupport_schwartz_integral_zero` gives
   `pointwiseDbar j H z = 0` for every `z ∈ U0`.

   Finally convert smooth real differentiability plus the Cauchy-Riemann
   equations into complex differentiability:

   ```lean
   theorem differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero
       {H : ComplexChartSpace m -> ℂ} {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (hDbar : ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0) :
       DifferentiableOn ℂ H U0
   ```

   At `z ∈ U0`, the real derivative `fderiv ℝ H z` is a continuous real-linear
   map.  The equations `pointwiseDbar j H z = 0` say
   `L (complexImagDir j) = Complex.I * L (complexRealDir j)` for every
   coordinate.  Decompose an arbitrary vector into its real and imaginary
   coordinate directions to prove `L (Complex.I • v) = Complex.I * L v`; hence
   `L` is the restriction of a continuous complex-linear map.  This supplies
   the `HasFDerivAt` witness over `ℂ` and therefore `DifferentiableOn ℂ H U0`.

   Assembly of `distributionalHolomorphic_regular` is then:

   ```lean
   obtain ⟨H, hH_smooth, hRep⟩ :=
     weyl_laplacian_distribution_regular_on_open Hdist hU0_open
       (local_laplacian_zero_of_distributionalHolomorphic Hdist hCR)
   have hDbar :=
     pointwiseDbar_eq_zero_of_distributionalHolomorphic
       Hdist hU0_open hCR H hH_smooth hRep
   exact ⟨H,
     differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero
       hU0_open hH_smooth hDbar,
     hRep⟩
   ```

   This is the next proof-doc frontier before Lean implementation.  The only
   hard theorem in the list is the localized Weyl lemma/parametrix; everything
   else is finite-dimensional calculus, support preservation, integration by
   parts, and already checked pointwise extraction.
8. Use the representation identity with an approximate identity `ψι -> δ0`.
   The tests `realConvolutionTest φ ψι` converge to `φ`, while on wedge pieces
   `Gψι` agrees with the real mollifications of `Fplus`/`Fminus`; the existing
   `tendsto_realMollify_normedBump_tubeDomain` theorem supplies the pointwise
   wedge convergence.  Limit uniqueness gives `H = Fplus` on the plus wedge
   and `H = Fminus` on the minus wedge.

No theorem may be named
`HasCommonDistributionalBoundaryValueOn`, `BoundaryPairingLimit`, or similar:
the actual data are compact support, support margin, compact direction set,
slow growth, and the `TendstoUniformlyOn` boundary limits.

## 3. Package A: Tube boundary values from polynomial growth

The theorem surface to replace is:

```lean
tube_boundaryValueData_of_polyGrowth
```

The later Lean port should split it into:

```lean
lemma tubeSlice_polyGrowth_uniform
lemma tubeSlice_family_is_equicontinuous_on_schwartz
lemma tubeSlice_pairing_cauchy_as_epsilon_to_zero
lemma tubeSlice_limit_defines_continuous_functional
lemma tube_boundary_value_exists_of_polyGrowth
theorem tube_boundaryValueData_of_polyGrowth
```

This package is the honest SCV input behind later boundary-value reconstruction
steps. It should stay QFT-free.

## 4. Package B: Vladimirov-Tillmann

The theorem

```lean
vladimirov_tillmann
```

should not be treated as one indivisible axiom. The later implementation should
split it into:

1. boundary-value distribution gives Fourier support in the dual cone,
2. Fourier-Laplace representation on the tube,
3. compact-subcone polynomial growth,
4. global distance-to-boundary growth estimate.

Documentation-standard theorem slots:

```lean
lemma boundary_distribution_supports_dual_cone
lemma tube_function_has_fourier_laplace_repr
lemma compact_subcone_growth_of_fourier_laplace_repr
lemma global_boundary_distance_growth
theorem vladimirov_tillmann
```

This package is the natural supplier for later `HasFourierLaplaceReprRegular`
and uniqueness theorems.

## 5. Package C: Distributional cluster lifts to tube interior

The theorem

```lean
distributional_cluster_lifts_to_tube
```

should be documented as a Poisson-kernel / boundary-value transport package,
not as a free corollary of analyticity.

Documentation-standard theorem slots:

```lean
lemma poisson_kernel_for_tube_domain
lemma tube_interior_eval_as_boundary_pairing
lemma translated_boundary_pairing_tends_to_factorized_limit
lemma poisson_pairing_respects_block_translation
theorem distributional_cluster_lifts_to_tube
```

This package is currently on the reverse-direction cluster lane, not the active
`E -> R` theorem-3 lane.

## 6. Package D: Bochner tube extension

The remaining content in `BochnerTubeTheorem.lean` is already sharply isolated.

The later implementation should proceed as:

1. strengthen local extension to a standard convex local family,
2. prove compatibility on overlaps,
3. invoke `holomorphic_extension_from_local_family`,
4. conclude the global extension theorem.

Documentation-standard theorem slots:

```lean
lemma convex_local_tube_patch_around_convexHull_point
lemma cauchy_integral_local_extension_on_patch
lemma distinguished_boundary_of_patch_lies_in_original_tube
theorem bochner_local_extension
theorem bochner_tube_extension
```

The current docs should treat the remaining blocker as “construct the compatible
local family,” not “global gluing is missing.”

## 7. Exact dependency order

For theorem 2, the immediate SCV implementation order is:

1. `SCV/DistributionalEOWKernel.lean`: the QFT-free Schwartz substrate.
   The checked portion is `complexTranslateSchwartz`,
   `schwartzTensorProduct₂`, `realConvolutionShearCLE`,
   `complexRealFiberIntegralRaw`, `complexRealFiberIntegral`,
   `realConvolutionTest`, the real-fiber translation CLM, fiber-integral
   invariance under real-fiber translation, the product-test fiber integral
   identity, the real/complex translation composition laws, the
   sheared-functional / fiber-invariance predicates, the sheared tensor
   fiber-translation identity, the mixed fiber quotient, product density,
   translation-covariant descent, the product-kernel `∂bar` consumer, the
   distributional-holomorphicity continuity passage, and compact
   approximate-identity convergence.  The remaining portion is
   `distributionalHolomorphic_regular`, followed by the regularized-envelope
   recovery and local continuous EOW extraction;
2. `SCV/LocalContinuousEOW.lean`: expose the local continuous EOW theorem by
   refactoring `local_eow_extension` and `local_extensions_consistent` from
   `TubeDomainExtension.lean`;
3. `SCV/LocalDistributionalEOW.lean`: prove
   `local_distributional_edge_of_the_wedge_envelope` from the
   Streater-Wightman regularization transcript above;
4. return to `WickRotation/OSToWightmanLocalityOS45...` and instantiate the
   SCV theorem as `BHW.os45_adjacent_commonBoundaryEnvelope`.

The broader SCV infrastructure should still be implemented in this order after
the theorem-2 local EOW package is no longer blocking:

1. finish `BochnerTubeTheorem.lean`,
2. replace `tube_boundaryValueData_of_polyGrowth`,
3. replace `vladimirov_tillmann`,
4. replace `distributional_cluster_lifts_to_tube`.

The order matters because:

1. Bochner extension is a local analyticity/gluing theorem,
2. boundary values need polynomial growth input,
3. Vladimirov-Tillmann supplies the global growth machinery,
4. cluster lifting is a later consumer of the full boundary-value transport
   package.

## 8. Consumers

The current main consumers are:

1. theorem 2 locality uses the new local distributional EOW envelope package
   through `BHW.os45_adjacent_commonBoundaryEnvelope`;
2. the general-`k` continuation blueprint uses Bochner/Malgrange-Zerner style
   SCV infrastructure,
3. the GNS holomorphic bridge needs forward-tube boundary-value transport,
4. the reverse-direction cluster lane currently references
   `distributional_cluster_lifts_to_tube`.

## 9. Do not do this

1. Do not re-axiomatize `edge_of_the_wedge`; it is already proved.
2. Do not mix QFT-specific support hypotheses into the SCV theorem statements.
3. Do not state Vladimirov-Tillmann as a single future proof obligation without
   the Fourier-support / Laplace-representation / growth subpackages.
4. Do not let later proof docs say “by several-complex-variables machinery”
   unless they point to an exact theorem slot here.

## 10. What counts as implementation-ready

This SCV blueprint should be considered ready only when:

1. the remaining axioms/sorries are decomposed into theorem packages,
2. each package has a named consumer,
3. the dependency order is explicit,
4. already-proved SCV theorems are kept separate from the live open ones,
5. the theorem-2 local EOW route names the exact pure-SCV substrate lemmas
   instead of using informal “kernel theorem” or product-tensor placeholders.

This note now records all five.  In particular, the theorem-2 local EOW route
is implementation-ready at the proof-doc level for the checked substrate
layers below.  The first Lean file is `SCV/DistributionalEOWKernel.lean`; it
now contains the checked QFT-free
definitions `ComplexChartSpace`, `SupportsInOpen`, `KernelSupportWithin`,
`complexRealDir`, `complexImagDir`, `directionalDerivSchwartzCLM`,
`dbarSchwartzCLM`, `IsDistributionalHolomorphicOn`,
`RepresentsDistributionOnComplexDomain`, `complexTranslateSchwartzCLM`, and
`complexTranslateSchwartz`, plus the checked SCV-owned two-space tensor
product `schwartzTensorProduct₂`, the real-direction shear
`realConvolutionShearCLE`, the raw generic fiber integral
`complexRealFiberIntegralRaw`, the fixed-fiber integrability lemma
`integrable_complexRealFiber`, the base-direction derivative field
`baseFDerivSchwartz`, the zeroth-order weighted decay estimate
`exists_norm_pow_mul_complexRealFiberIntegralRaw_le`, the uniform integrable
bound `exists_integrable_bound_baseFDerivSchwartz`,
`hasFDerivAt_complexRealFiberIntegralRaw`,
`fderiv_complexRealFiberIntegralRaw_eq`,
`contDiff_nat_complexRealFiberIntegralRaw`,
`contDiff_complexRealFiberIntegralRaw`,
`decay_complexRealFiberIntegralRaw`, `complexRealFiberIntegral`,
`realConvolutionTest` with its apply theorem,
`complexRealFiberTranslateSchwartzCLM`,
`complexRealFiberIntegral_fiberTranslate`,
`complexRealFiberIntegral_schwartzTensorProduct₂`,
`translateSchwartz_translateSchwartz`,
`complexTranslateSchwartz_complexTranslateSchwartz`,
`shearedProductKernelFunctional`, and
`IsComplexRealFiberTranslationInvariant`, plus
`complexRealFiberTranslate_shearedTensor_eq`.  It also now contains the
checked pure coordinate-transport layer `headBlockShift`,
`realBlockFlattenCLE`, `complexToFinTwoCLE`, `complexChartRealFlattenCLE`,
`finAppendCLE`, `mixedChartFiberFirstCLE`, the head/tail real-imaginary apply
lemmas, `mixedChartFiberFirstCLE_symm_headBlockShift`, and
`mixedChartFiberFirstCLE_translate`.  The transported fiber-integral identity,
pure-SCV head-block factorization extraction, mixed fiber quotient,
normalized-cutoff factorization, product-density theorem, and product-kernel
descent are now checked.  The support-preservation companion
`SCV/DistributionalEOWSupport.lean` is also checked, with
`KernelSupportWithin_hasCompactSupport`,
`directionalDerivSchwartzCLM_tsupport_subset`,
`directionalDerivSchwartzCLM_supportsInOpen`,
`dbarSchwartzCLM_tsupport_subset`, and `SupportsInOpen.dbar`.  The checked
approximate-identity companion now also supplies
`tendsto_realConvolutionTest_of_shrinking_normalized_support` and
`exists_realConvolutionTest_approxIdentity`.  The next declarations should
therefore address the distributional-regularity layer
`distributionalHolomorphic_regular` and the regularized-envelope kernel
recovery surfaces listed in Section 2.4.

## 11. Exact proof transcript for tube boundary values from polynomial growth

Package A should now be written at theorem-3-style detail. The later Lean proof
should proceed in the following order.

1. Fix a compact subcone `Γ₀` of the open cone `Γ`.
2. For each `y ∈ Γ₀` and `ε > 0`, define the slice functional
   `L_{ε,y}(φ) := ∫ F(x + i ε y) φ(x) dx`.
3. Use polynomial growth of `F` on the tube to prove a uniform Schwartz
   seminorm bound on `L_{ε,y}` as `ε -> 0`.
4. Prove the family `L_{ε,y}` is Cauchy on Schwartz test functions by applying
   Cauchy estimates to differences in the imaginary direction.
5. Define the limiting continuous functional `L_y`.
6. Prove `L_y` is independent of the chosen approach direction `y` inside the
   same cone component.
7. Package the common limit as the boundary-value distribution.
8. Prove the recovered distribution gives back the original tube function by
   the standard Poisson/Fourier-Laplace reconstruction formula.

The implementation theorem slots should therefore be:

```lean
def tubeSliceFunctional (ε : ℝ) (y : ConeDir) : SchwartzMap →L[ℂ] ℂ
lemma tubeSliceFunctional_seminorm_bound
lemma tubeSliceFunctional_cauchy_as_epsilon_to_zero
lemma tubeSliceFunctional_limit_exists
lemma tubeSliceFunctional_limit_independent_of_direction
def tubeBoundaryValueDistribution
lemma tubeBoundaryValueDistribution_isContinuous
lemma tubeBoundaryValueDistribution_recovers_tube_function
theorem tube_boundaryValueData_of_polyGrowth
```

The critical documentation point is that this theorem is a QFT-free
distributional boundary-value package. It should not mention Wightman,
Schwinger, or Borchers data anywhere in its final statement.

## 12. Exact one-point forward-tube bridge used by theorem 2 and GNS

The repo now has two consumers that want the same one-variable forward-tube
package:

1. theorem 2 locality, through the flattened regular-input constructor,
2. the GNS matrix-coefficient holomorphic bridge.

So the SCV docs should isolate the common one-point package explicitly:

```lean
lemma onePoint_forward_support_to_flatRegular
    (u : TemperedDistribution (MinkowskiSpace d))
    (hsupp : ForwardSupported u) :
    HasFourierLaplaceReprRegularOnePoint u

lemma onePoint_boundary_value_recovery
    (u : TemperedDistribution (MinkowskiSpace d))
    (hreg : HasFourierLaplaceReprRegularOnePoint u) :
    boundaryValueOfOnePointExtension hreg = u

lemma onePoint_forwardTube_uniqueness
    (F G : ComplexSpacetime d → ℂ)
    (hF : DifferentiableOn ℂ F (TranslationForwardTube d))
    (hG : DifferentiableOn ℂ G (TranslationForwardTube d))
    (hbdry : sameOnePointBoundaryValue F G) :
    EqOn F G (TranslationForwardTube d)
```

This package is deliberately smaller than the full tube-boundary theorem. The
future Lean port should prove it first if theorem 2 / GNS resume before the
full SCV boundary-value package is complete.

### 12.1. Exact proof transcript for the one-point forward-tube bridge

The later Lean proof should not leave the one-point package as a mere trio of
consumer theorem names. The exact mathematical route should be:

1. start from a one-point tempered distribution `u` with forward support,
2. take its Fourier transform `û`,
3. use forward support to prove `supp û` lies in the closed dual forward cone,
4. define the candidate holomorphic extension on the one-point forward tube by
   the Fourier-Laplace integral
   `F(z) := ∫ e^{-i⟨p,z⟩} dû(p)`,
5. prove the integral is absolutely/convergently well-defined for
   `Im z ∈ ForwardCone`,
6. prove holomorphy by differentiating under the integral,
7. prove the boundary value along `z = x + i ε y` tends to `u` in tempered
   distribution sense as `ε -> 0+`,
8. prove uniqueness by applying the one-variable tube identity theorem to the
   difference of two candidate extensions with the same boundary value.

So the real theorem-slot inventory should be:

```lean
lemma onePoint_distribution_supports_dual_forwardCone
lemma onePoint_fourierLaplace_integral_converges
lemma onePoint_fourierLaplace_integral_holomorphic
def onePoint_forwardTube_extension
lemma onePoint_forward_support_to_flatRegular
lemma onePoint_boundary_value_recovery
lemma onePoint_zero_boundaryValue_implies_zero
lemma onePoint_forwardTube_uniqueness
```

The proof discipline should be:

1. support theorem first,
2. explicit Fourier-Laplace construction second,
3. boundary-value recovery third,
4. uniqueness last.

That is the route both theorem 2 and the GNS matrix-coefficient bridge should
consume. Neither should build its own one-point SCV theory.

## 13. Exact proof transcript for Vladimirov-Tillmann

Package B should be written as a four-stage chain, not a single theorem.

1. Start with a boundary-value distribution on the real edge of a tube.
2. Use dual-cone test-function estimates to prove Fourier support in the dual
   cone.
3. Use that support theorem to build the Fourier-Laplace representation of the
   tube function.
4. Prove growth on compact subcones by estimating the Laplace kernel against
   the supported Fourier transform.
5. Convert compact-subcone growth to a global distance-to-boundary estimate.

The theorem slots should therefore be read as:

```lean
lemma boundary_distribution_supports_dual_cone
lemma dual_cone_supported_distribution_has_laplace_repr
lemma laplace_repr_matches_tube_function
lemma compact_subcone_growth_bound
lemma distance_to_boundary_growth_bound
theorem vladimirov_tillmann
```

The later Lean proof should not skip directly from "boundary distribution" to
"global boundary-distance growth." The Fourier-support / Laplace-representation
middle layer is the real mathematical content of the theorem.

## 14. Exact proof transcript for Bochner tube extension

Package D should also be made proof-transcript-level explicit.

1. Fix a point in the convex hull of the original tube base.
2. Construct a small convex neighborhood whose translated distinguished
   boundary still lies in the original tube.
3. Define the local holomorphic extension on that patch by a Cauchy integral on
   the distinguished boundary.
4. Prove that on overlaps of two such patches, the two local extensions agree
   by the identity theorem.
5. Feed the compatible local family to the already-proved global gluing theorem
   `holomorphic_extension_from_local_family`.
6. Conclude the global Bochner extension on the convex hull.

The implementation theorem slots should therefore be:

```lean
lemma convex_local_tube_patch_around_convexHull_point
lemma distinguished_boundary_of_patch_lies_in_original_tube
lemma cauchy_integral_local_extension_on_patch
lemma local_extensions_agree_on_overlap
lemma local_family_is_compatible
theorem bochner_local_extension
theorem bochner_tube_extension
```

The important route constraint is that the global gluing theorem is already in
place. So the later proof should spend its effort on the explicit local family
construction and overlap agreement, not on reproving a general sheaf-gluing
result.

## 15. Estimated Lean size by SCV package

The SCV docs should now record rough proof sizes so later implementation can be
split honestly.

1. one-point forward-tube bridge:
   `80-180` lines.
2. tube boundary values from polynomial growth:
   `180-320` lines.
3. Vladimirov-Tillmann:
   `220-420` lines.
4. Bochner local/global tube extension:
   `140-260` lines.

So the live open SCV package should now be thought of as roughly
`620-1180` lines of QFT-free analysis, split across four packages rather than
one monolithic "SCV machinery" theorem.
