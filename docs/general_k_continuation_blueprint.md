# General-k Continuation Blueprint

Purpose: this note is the implementation blueprint for the general
`k > 2` continuation package behind the OS II route.

It is not a replacement for `docs/os2_detailed_proof_audit.md`. That audit is
the proof transcript. This note is the implementation dependency graph for the
later Lean port.

This note should be read together with:
- `docs/os2_detailed_proof_audit.md`,
- `docs/os1_detailed_proof_audit.md`,
- `docs/theorem3_os_route_blueprint.md` as the already-completed `k = 2`
  specialization discipline.

## 0. Paper-to-repo dictionary for the general-k route

The general-k implementation should keep the following dictionary explicit.

OS II paper objects:
1. `C_k^(N)` — analyticity domains at stage `N`,
2. `D_n^(N)` — mixed real/complex domains for the Hilbert-vector fields,
3. `Ψ_n(x,ζ)` — Hilbert-valued fields,
4. `T_k` — the VI.1 regularized Schwinger family,
5. `S_{k,ε}` — the VI.2 renormalized family.

Repo-side implementation objects:
1. tube / reduced-tube / mixed-domain predicates in the `SCV` and WickRotation
   layers,
2. explicit Lean structures for the scalar continuation data on `C_k^(N)`,
3. explicit Lean structures for the vector continuation data on `D_n^(N)`,
4. flattened Fourier-Laplace or boundary-value transport data only after the
   Chapter V/VI route has already produced the needed analyticity and growth.

The main discipline rule is:

1. use the paper domain names in the docs,
2. use exact Lean theorem slots for their future implementations,
3. do not hide the dictionary in prose.

## 1. What this blueprint is for

The current `k = 2` frontier on `main` does not require the full general
OS II Chapter V-VI package. But the complete `E -> R` formalization eventually
will.

The implementation goal of this blueprint is therefore:

1. isolate the exact theorem packages from OS II that later Lean work will need,
2. make the dependency order explicit,
3. keep the future port faithful to the paper's one-variable-first discipline.

## 2. Global route discipline extracted from OS II

The route rules that later Lean work must treat as binding are:

1. one continuation variable at a time,
2. all other parameters fixed during that continuation step,
3. many-variable continuation only through the `(A_N)/(P_N)` induction ladder,
4. regularize before proving growth,
5. take boundary values only after the growth estimate is in place.

Anything that skips those rules is not the OS II route.

## 3. The implementation DAG

The later Lean port should be organized into the following packages.

Package A. Chapter V.1 local analyticity:
- Lemma 5.1 and its quantitative local polydisc.

Package B. The induction ladder:
- `(A_0) -> (P_0)`,
- `(A_N) -> (P_N)`,
- `(P_N) -> (A_{N+1})`,
- Lemma 5.2 and Corollary 5.3 for domain growth.

Package C. VI.1 regularization:
- mollifier/regularizer support,
- regularized vector construction,
- derivative estimates,
- `E0'` norm bound,
- directional bounds,
- local holomorphic bound,
- real-domain estimate.

Package D. VI.2 renormalized induction:
- normalized family `S_{k,ε}`,
- algebraic reduction to the VI.1 estimate,
- elimination of the auxiliary stage index `N`.

Package E. Appendix:
- `E0'' => E0'`,
- any residual support/Schwartz/approximation lemmas needed by the final main
  theorem.

That is the correct order. The later implementation should not start with VI.2
or with a several-variable boundary-value theorem detached from the Chapter V
ladder.

## 4. Exact theorem-slot inventory already written in the audit

The detailed OS II audit already names the exact theorem slots for the key
packages. This blueprint records the implementation grouping.

### 4.1. Chapter V.1 local analyticity

Implementation theorem slots:

1. `cone_angle_from_positive_time`
2. `dual_cone_basis_exists`
3. `directional_semigroup_continuation`
4. `malgrange_zerner_glue_directional_pieces`
5. `explicit_radius_from_coordinate_estimates`

These are the five pieces of Lemma 5.1. Nothing larger should be attempted
before those five names are individually understood.

#### 4.1.1. Proof transcript for Lemma 5.1

The later Lean proof should follow this exact order.

1. Fix a real positive-time point `ξ`.
2. Extract a cone angle `γ` from the inequalities
   `ξ_i^0 > |ξ_i|`.
3. Choose finitely many dual-cone directions `e_μ` indexed by `Fin (d + 1)`.
4. For each `e_μ`, apply the one-variable OS I semigroup continuation theorem
   to the scalar function `u ↦ S_k (ξ + u • e_μ)`.
5. Record those one-variable continuations on overlapping flat tubes.
6. Glue them by Malgrange-Zerner.
7. Extract the quantitative polydisc radius by unrolling the coordinate
   inequalities exactly as in Lemma 5.1.

If the later Lean script does not explicitly display steps 4 and 6, the proof
has almost certainly skipped the core OS II content.

#### 4.1.2. Lean-style theorem script

```lean
theorem local_polydisc_of_real_positive_time
    (ξ : TimeDiffConfig k)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    ∃ ρ > 0,
      IsHolomorphicOn
        (fun ζ => S_k (ξ + ζ))
        (polydisc (0 : TimeDiffConfig k) ρ) := by
  obtain ⟨γ, hγ_pos, hγ⟩ := cone_angle_from_positive_time ξ hξ
  obtain ⟨e, he⟩ := dual_cone_basis_exists hγ
  have hdir :
      ∀ μ : Fin (d + 1),
        directionalContinuationData (ξ := ξ) (γ := γ) (e μ) := by
    intro μ
    exact directional_semigroup_continuation hξ (he μ)
  obtain ⟨F, hF⟩ := malgrange_zerner_glue_directional_pieces hdir
  obtain ⟨ρ, hρ_pos, hρ⟩ := explicit_radius_from_coordinate_estimates hF
  refine ⟨ρ, hρ_pos, ?_⟩
  exact hF.mono hρ
```

### 4.2a. The base step `(A_0) -> (P_0)`

The base step deserves its own file-level plan rather than being hidden under
the general `(A_N) -> (P_N)` heading.

Mathematical content:

1. choose the delta-family / real-slice scalar,
2. use the Chapter IV analytic input and Lemma 5.1 local analyticity,
3. build the vector candidate from the scalar pairings,
4. upgrade equality of pairings to the actual Hilbert vector.

Implementation theorem slots:

1. `base_delta_family_exists`
2. `base_scalar_candidate_from_pairings`
3. `base_scalar_candidate_local_holomorphic`
4. `base_scalar_candidate_matches_real_slice`
5. `base_vector_reconstruction_from_delta_family`

#### 4.2a.1. Proof transcript

The base-step Lean proof should read:

1. import the `k = 2` / Chapter IV scalar analyticity theorem;
2. restrict it to the real basepoint needed for the delta family;
3. prove local holomorphy of the scalar candidate by Lemma 5.1;
4. identify the real slice with the target scalar pairing;
5. use the Hilbert-space Riesz/uniqueness package already available at this
   stage to obtain the vector value.

This is the place where the docs should keep the "OS II Theorem 4.1 + Lemma
5.1 + OS I semigroup scalar-product formula" chain explicit.

### 4.2. `(A_N) -> (P_N)`

Implementation theorem slots:

1. `real_polydisc_inside_mixed_domain`
2. `scalar_derivatives_control_hilbert_derivatives`
3. `hilbert_remainder_norm_sq_eq_scalar_remainder`
4. `vector_taylor_series_norm_converges`

This is the Hilbert-valued Taylor reconstruction package. The crucial point is
that the squared norm of the vector remainder is identified with the scalar
remainder of the reflected Schwinger function. If that theorem is not written
down explicitly, the package is not ready.

#### 4.2.1. Proof transcript for `(A_N) -> (P_N)`

The later Lean script should follow this exact decomposition.

1. From `(x,ζ) ∈ D_n^(N)`, choose a closed polydisc still contained in
   `D_n^(N)`.
2. Define the formal Hilbert-valued Taylor polynomial sequence at the real
   center.
3. Expand the squared norm of the remainder as a scalar double sum.
4. Use the already-proved scalar-product formula `(5.17)` to identify that
   double sum with the scalar Taylor remainder of
   `S_{2n-1}(-\bar ζ, 2x, ζ)`.
5. Use scalar analyticity on the polydisc to prove that scalar remainder tends
   to zero.
6. Conclude norm convergence and therefore the existence of the analytic vector.

The indispensable theorem in this chain is still
`hilbert_remainder_norm_sq_eq_scalar_remainder`.

#### 4.2.2. Lean-style theorem script

```lean
theorem hilbert_vector_from_scalar_taylor
    (hA : ScalarContinuationOn DnN)
    (x : ℝ)
    (ζ : TimeVector (n - 1))
    (hxζ : (x, ζ) ∈ DnN) :
    ∃ Ψ : HilbertSpaceVector,
      HasStrongTaylorExpansionAt
        (fun w => PsiField n x w)
        Ψ ζ := by
  obtain ⟨ξ, r, hpolydisc⟩ := real_polydisc_inside_mixed_domain hxζ
  have hderiv :=
    scalar_derivatives_control_hilbert_derivatives hA hpolydisc
  have hrem :
      ∀ N, ‖vectorTaylorRemainder (Ψn := Ψ_n) ξ r N‖^2 =
        scalarTaylorRemainder
          (fun z => S_(2 * n - 1) (-conj z, 2 * x, z)) ξ r N := by
    intro N
    exact hilbert_remainder_norm_sq_eq_scalar_remainder ξ r hpolydisc N
  exact vector_taylor_series_norm_converges hA hrem
```

### 4.3. `(P_N) -> (A_{N+1})`

Implementation theorem slots:

1. `scalar_candidate_from_vector_pairing`
2. `scalar_candidate_agrees_on_real_slice`
3. `scalar_candidate_holomorphic_on_generating_union`
4. `scalar_candidate_extends_to_envelope`
5. `mixed_domain_is_contained_in_Ck`

This is the stage where the envelope-of-holomorphy / tube-domain SCV input
must be named explicitly. The extension is not free.

#### 4.3.1. Proof transcript for `(P_N) -> (A_{N+1})`

The later Lean proof should be organized as:

1. define the scalar candidate as the inner product of the already-continued
   `Ψ`-vectors;
2. prove that on the real slice this scalar candidate agrees with the old
   Schwinger data;
3. prove holomorphy on each generating mixed domain separately;
4. prove those domains glue to the union used in the paper;
5. invoke the exact envelope theorem for that union to reach `C_k^(N+1)`.

The key implementation warning is that step 5 must be visible in the code. If
the later Lean file goes directly from "holomorphic on the generating union" to
"holomorphic on `C_k^(N+1)`" without naming the envelope theorem, the proof is
still incomplete at the documentation level.

#### 4.3.2. Lean-style theorem script

```lean
theorem scalar_continuation_from_hilbert_vectors
    (hP : VectorContinuationOn DnN)
    (k : ℕ) :
    ScalarContinuationOn (Ck (N + 1)) := by
  obtain ⟨Fnm, hFnm⟩ := scalar_candidate_from_vector_pairing hP rfl
  have hreal := scalar_candidate_agrees_on_real_slice hP hFnm
  have hgen := scalar_candidate_holomorphic_on_generating_union hP hFnm
  have henv := generating_union_has_required_envelope (N := N) (k := k)
  obtain ⟨Fk, hFk⟩ := scalar_candidate_extends_to_envelope hgen
  exact package_scalar_continuation_on_Ck hFk hreal
```

#### 4.3.3. Hidden infrastructure theorems behind the envelope step

The later Lean port should not leave the envelope step as a single black box.
At minimum the following theorem slots must exist explicitly in the file plan:

1. `mixed_domain_generating_union_open`
2. `scalar_candidate_agrees_on_pairwise_overlaps`
3. `glued_scalar_candidate_on_generating_union`
4. `generating_union_has_required_envelope`
5. `Ck_next_eq_required_envelope`
6. `envelope_extension_unique_on_generating_union`

The point of listing these separately is that two different mathematical moves
are happening:

1. glue the locally defined scalar candidates on overlaps of the generating
   mixed domains;
2. extend the glued function from that open union to its envelope of
   holomorphy.

Only the second step is the actual envelope theorem. If the future Lean port
bundles both steps under one opaque theorem name, the package will again be too
implicit for later maintenance.

### 4.4. Lemma 5.2 and Corollary 5.3

Implementation theorem slots:

1. `angles_recursive_construction`
2. `angles_stage_membership`
3. `angles_lower_bound_528`
4. `stage_selection_from_cor53`

The docs should not reintroduce the previously false closed-form angle formula.
The recursive construction plus the quantitative lower bound `(5.28)` is the
paper-faithful route.

#### 4.4.1. Proof transcript for Lemma 5.2 / Corollary 5.3

The later Lean script should explicitly keep the recursion visible.

1. Define the angle sequence recursively.
2. Prove by induction that the stage-`N` points lie in the desired domains.
3. Prove the quantitative lower bound `(5.28)` for that recursive sequence.
4. Use Corollary 5.3 to choose `N = N(ζ)` for the later VI.2 step.

The docs should not allow any shortcut such as "define the angles by a closed
form and verify afterwards." That route already produced a false statement once
and is banned here.

### 4.5. VI.1 regularization

Implementation theorem slots:

1. `regularizer_exists_with_mass_one`
2. `regularizer_support_bound`
3. `regularized_kernel_support_control`
4. `regularized_pairing_vector_exists`
5. `regularized_derivative_bound`
6. `e0prime_norm_estimate`
7. `directional_bound_from_semigroup_estimate`
8. `local_bound_from_directional_bounds`
9. `real_domain_estimate_from_local_bound`

These are the true moving parts of VI.1. The later Lean port should keep the
support normalization explicit:

1. choose `supp g_ρ ⊆ {|z| < ρ/8}`,
2. deduce `supp k_ρ ⊆ {|z| < ρ/4}`.

#### 4.5.1. Proof transcript for the regularization package

The later Lean implementation should be split into the following actual proof
files or namespaces:

1. radial bump / normalization,
2. support and mass bookkeeping for `g_ρ` and `k_ρ`,
3. mean-value identity `(6.6)`,
4. regularized pairing vectors `(6.10)`,
5. derivative and support estimates `(6.17)`-`(6.18)`,
6. the `E0'` norm estimate,
7. directional bounds,
8. local bound via maximum principle,
9. real-domain estimate.

The important mathematical point is that VI.1 is not "one theorem with many
sublemmas." Each item above is a genuinely distinct proof package and later
Lean code should reflect that.

#### 4.5.2. Lean-style theorem script

```lean
theorem regularized_real_domain_estimate
    (hE0' : LinearGrowthCondition) :
    realDomainTemperedEstimate := by
  obtain ⟨h, hh⟩ := radial_bump_exists_with_osii_normalization
  have hker := regularizingKernel_support_and_mass (d := d) hρ
  have hmean := schwinger_mean_value_identity (d := d) hρ hζ
  have hpair := regularized_pairing_vectors_exist (d := d) hρ hξ hdir
  have hsup := abs_schwinger_le_sup_regularized (d := d) hρ hζ
  have hnorm := e0prime_norm_bound_for_regularized_vectors hE0' hρ hξ
  have hdirb := directional_regularized_bound hE0' hρ hξ
  have hlocal := local_bound_from_directional_bounds hdirb
  exact real_domain_estimate_from_local_bound hlocal
```

#### 4.5.3. Micro-lemma inventory behind support and norm estimates

The VI.1 package becomes implementation-ready only when the following support
and estimate sublemmas are named explicitly.

Regularizer construction:

1. `radial_bump_exists_with_mass_one`
2. `radial_bump_support_subset_ball_rho_div_eight`
3. `regularizer_g_rho_definition`
4. `regularizer_k_rho_definition`
5. `support_g_rho_subset_ball_rho_div_eight`
6. `support_k_rho_subset_ball_rho_div_four`
7. `integral_g_rho_eq_one`
8. `integral_k_rho_eq_one`

Mean-value / convolution step:

1. `regularized_scalar_mean_value_identity`
2. `regularized_scalar_support_preserved`
3. `regularized_scalar_derivative_formula`

Hilbert-vector construction:

1. `regularized_pairing_vector_exists`
2. `regularized_pairing_vector_derivative_bound`
3. `regularized_pairing_vector_support_control`

Norm and growth transfer:

1. `e0prime_bound_for_regularized_pairing_vector`
2. `directional_bound_for_regularized_scalar`
3. `local_sup_bound_from_directional_family`
4. `real_domain_estimate_from_local_sup_bound`

If any of these steps remains unnamed, then the VI.1 blueprint is still too
coarse. The later Lean implementation should be able to assign each of those
bullets to a concrete theorem or lemma before coding begins.

### 4.6. VI.2 renormalized induction

Implementation theorem slots:

1. `normalized_family_definition`
2. `normalized_family_uniform_bound`
3. `algebraic_reduction_624_to_627`
4. `renormalized_family_temperedness`
5. `stage_elimination_from_cor53`
6. `limit_family_is_original_family`

The later port should keep the role of `N = N(ζ)` explicit. It is not an
implementation nuisance; it is how the paper re-enters the correct analyticity
stage before applying VI.1.

#### 4.6.1. Proof transcript for VI.2

The later Lean proof should follow the paper literally:

1. define the renormalized family `S_{k,ε}`,
2. prove the algebraic identities `(6.24)`-`(6.27)`,
3. apply the VI.1 estimate to `S_{k,ε}` at the stage `N = N(ζ)` selected by
   Corollary 5.3,
4. remove the auxiliary index `N`,
5. let `ε -> 0` and identify the original family again.

If the code tries to jump straight from VI.1 to a final general-`k` theorem
without an explicit renormalized family declaration, it is not following OS II
VI.2 faithfully.

#### 4.6.2. Exact theorem slots behind the algebraic heart

```lean
lemma renormalized_family_satisfies_stage_hypotheses
    (hstage : ζ ∈ Ck (N + 1)) :
    stageHypothesesFor (S_{k,ε}) := by
  -- this is the algebraic content of `(6.21)`-`(6.23)`

lemma renormalized_family_bound_from_vi1
    (hvi1 : realDomainTemperedEstimateFor (S_{k,ε})) :
    localAnalyticBoundFor (S_{k,ε}) := by
  -- this is where VI.1 is plugged into VI.2

lemma original_family_recovered_from_renormalized_limit
    :
    Tendsto (fun ε => S_{k,ε}) (nhdsWithin 0 (Set.Ioi 0)) (nhds S_k) := by
  -- final limit passage from the normalized family back to `S_k`
```

#### 4.6.3. Exact theorem slots for the `ε -> 0` recovery step

The end of VI.2 should also be split into explicit theorem slots rather than a
single slogan "let `ε -> 0`."

1. `normalized_family_has_uniform_local_bound`
2. `normalized_family_tends_to_original_on_real_slice`
3. `normalized_family_tends_to_original_distributionally`
4. `boundary_value_of_normalized_family_matches_original`
5. `original_family_recovered_from_renormalized_limit`

The later Lean port should be able to say exactly at which level the limit is
taken:

1. first on the real slice or against test functions,
2. then on the holomorphic family by uniqueness,
3. finally in the theorem statement of the original `S_k`.

That staging mirrors the current theorem-3 route discipline and should remain
visible in the general-k port as well.

## 5. Infrastructure that must be treated as first-class

Three infrastructure packages are genuinely on the critical path.

1. Malgrange-Zerner gluing for flat tubes.
2. Envelope-of-holomorphy / tube-domain extension on the mixed domains used in
   `(P_N) -> (A_{N+1})`.
3. The several-variable SCV comparison theorems already isolated in the repo,
   especially those now replacing older edge-of-the-wedge axioms.

Those are not "background details." They are named theorem dependencies of the
paper route and should be documented that way in later Lean work.

## 5.1. File plan for the later Lean port

The later implementation should be split into small files matching the proof
packages, for example:

1. `OS2ChapterV1LocalAnalyticity.lean`
2. `OS2BaseStep.lean`
3. `OS2InductionLadder.lean`
4. `OS2DomainGrowth.lean`
5. `OS2VI1Regularization.lean`
6. `OS2VI2Renormalized.lean`
7. `OS2AppendixE0Prime.lean`

The point is not the exact filenames but the discipline:

1. one paper package per file,
2. theorem-slot names matching the doc,
3. no giant catch-all continuation file.

## 5.2. Package dependency matrix

The later Lean port should keep the package boundaries visible in the import
graph as well as in prose.

1. `OS2ChapterV1LocalAnalyticity.lean`
   imports only cone/tube geometry, the OS I one-variable continuation
   package, and the Malgrange-Zerner interface.
2. `OS2BaseStep.lean`
   imports `OS2ChapterV1LocalAnalyticity.lean` plus the Chapter IV `k = 2`
   scalar continuation input.
3. `OS2InductionLadder.lean`
   imports `OS2BaseStep.lean` and the scalar-product formula package `(5.17)`.
4. `OS2DomainGrowth.lean`
   imports `OS2InductionLadder.lean` but should stay independent of VI.1.
5. `OS2VI1Regularization.lean`
   imports `OS2DomainGrowth.lean` and the appendix `E0'` infrastructure.
6. `OS2VI2Renormalized.lean`
   imports `OS2VI1Regularization.lean` and the stage-selection theorem from
   `OS2DomainGrowth.lean`.
7. `OS2AppendixE0Prime.lean`
   should remain import-light and feed into VI.1, not depend on it.

This dependency matrix matters because it prevents the future port from
smuggling late VI.1/VI.2 arguments backward into the Chapter V continuation
files.

## 5.3. Exact SCV infrastructure hooks the general-k port is allowed to use

The later general-k Lean port should not rediscover its SCV dependencies ad
hoc. The acceptable infrastructure hooks are:

1. `SCV.edge_of_the_wedge_theorem` in `SCV/TubeDomainExtension.lean`
   for the several-variable continuation/gluing steps already formalized;
2. `identity_theorem_SCV`, `identity_theorem_tubeDomain`, and
   `identity_theorem_product` in `SCV/IdentityTheorem.lean`;
3. `bochner_tube_extension` in `SCV/BochnerTubeTheorem.lean` once its local
   extension theorem is completed;
4. `vladimirov_tillmann` and `distributional_cluster_lifts_to_tube` in
   `SCV/VladimirovTillmann.lean`, but only after their axiomatic status has
   been replaced or explicitly accepted;
5. the regular flattened boundary-value transport package in
   `Wightman/Reconstruction/ForwardTubeDistributions.lean`.

The route rule is:

1. reuse already-proved SCV theorems when they match the paper package;
2. if a needed SCV theorem is still axiomatic or sorry-backed, document that
   dependency under its exact theorem name before any later Lean proof relies
   on it.

## 5.4. Malgrange-Zerner implementation plan

The general-k blueprint should be explicit that Malgrange-Zerner is not just a
name. The later Lean implementation should break it into:

1. a local directional-extension datum for each basis direction,
2. a compatibility theorem on pairwise overlaps,
3. an open-star-shaped union theorem for the directional flats,
4. a gluing theorem producing one holomorphic function on that union,
5. a conversion from the glued flat-union domain to the desired local polydisc.

Documentation-standard theorem slots:

```lean
lemma directional_flat_extension_exists
lemma directional_flat_extensions_agree_on_overlap
lemma directional_flat_union_isOpen
lemma directional_flat_union_starShaped
lemma malgrange_zerner_glue_directional_pieces
lemma local_polydisc_inside_directional_flat_union
```

The later Lean files should make the domain geometry explicit. In particular,
the proof should never jump directly from "one-variable continuations in finitely
many directions" to "holomorphic on a polydisc" without a named overlap/gluing
theorem in between.

### 5.4.1. Exact gluing mechanism behind `malgrange_zerner_glue_directional_pieces`

The later Lean proof should also record *how* the gluing theorem is supposed to
work, not just what sublemmas it uses.

1. Each directional continuation produces a holomorphic function `F_μ` on a
   flat tube `U_μ`.
2. For each pair `μ, ν`, the intersection `U_μ ∩ U_ν` contains a real slice
   segment through the basepoint where both continuations are already known to
   agree with the same original Schwinger function.
3. Because `U_μ ∩ U_ν` is connected and open, the identity theorem upgrades
   equality on that real slice segment to equality on the whole overlap.
4. Those overlap equalities make the family `{F_μ}` a compatible holomorphic
   local family on the union `⋃_μ U_μ`.
5. The general local-gluing theorem for holomorphic functions on compatible
   open covers then yields one holomorphic function on the union.
6. The quantitative cone-angle geometry is used only after gluing, to show a
   concrete local polydisc lies inside that union.

So the later file should not need to "discover" the gluing mechanism. It is:

1. real-slice agreement,
2. identity theorem on overlaps,
3. compatible-family gluing on the union,
4. geometric inclusion of the target polydisc.

That is the exact mathematical content of the Malgrange-Zerner step needed by
OS II in this repo.

## 5.5. Envelope-of-holomorphy implementation plan

The `(P_N) -> (A_{N+1})` step uses two distinct SCV inputs:

1. gluing the scalar candidate on the generating union,
2. identifying the envelope of that union with the required `C_k^(N+1)` domain.

The later Lean proof should therefore be organized around these theorem slots:

```lean
lemma generating_union_isOpen
lemma generating_union_nonempty
lemma scalar_candidate_holomorphic_on_each_generator
lemma scalar_candidate_agrees_on_generator_overlaps
lemma scalar_candidate_holomorphic_on_generating_union
lemma generating_union_has_required_envelope
lemma Ck_next_eq_required_envelope
lemma scalar_candidate_extends_to_envelope
```

This is the minimum documentation needed to keep the envelope step honest. The
general-k port should never write "by envelope-of-holomorphy" as a single proof
line unless every theorem slot above has already been implemented or deliberately
accepted as an external dependency.

## 5.6. Production hook inventory for the future general-k port

Even though the full Chapter V/VI package is not yet implemented, the docs
should record which current repo surfaces already exemplify the allowed theorem
shapes:

1. the theorem-3 `k = 2` route in
   `docs/theorem3_os_route_blueprint.md`,
2. the forward-tube distribution transport package in
   `Wightman/Reconstruction/ForwardTubeDistributions.lean`,
3. the several-variable uniqueness and edge-of-the-wedge theorems in
   `SCV/IdentityTheorem.lean` and `SCV/TubeDomainExtension.lean`,
4. the reduced BHW input discipline in
   `Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean`.

The future general-k port should look like a disciplined enlargement of those
packages, not a separate theory with a different proof style.

## 6. Exact implementation order

The later Lean port should proceed in the following order.

1. Finish the Chapter V.1 local analyticity package.
2. Formalize the base step `(A_0) -> (P_0)`.
3. Generalize to `(A_N) -> (P_N)`.
4. Formalize `(P_N) -> (A_{N+1})`.
5. Formalize Lemma 5.2 / Corollary 5.3.
6. Build the entire VI.1 regularization package.
7. Build the VI.2 normalized-family induction.
8. Only then widen the `k = 2` route to the full general `k` theorem surface.

The order matters because VI.2 is unusable until the Chapter V and VI.1 inputs
exist in exact theorem form.

## 6.1. Trusted-vs-untrusted checklist before any later Lean work

Trusted from the documentation side:

1. the package order,
2. the theorem-slot inventories,
3. the recursive-angle route,
4. the regularizer support convention,
5. the need for explicit envelope and Malgrange-Zerner inputs.

Not yet implemented:

1. the actual Malgrange-Zerner theorem,
2. the exact envelope theorem on the mixed domains,
3. the full renormalized-family algebra in Lean,
4. the final general-`k` boundary-value theorem.

So the later Lean port should present itself as implementing named packages
from this blueprint, not as discovering the route on the fly.

## 7. What should not be externalized as new axioms

The later Lean port should not introduce new axioms unless the user explicitly
approves them. In particular, the following are mathematically legitimate
topics but should not be silently externalized:

1. Malgrange-Zerner gluing,
2. envelope-of-holomorphy continuation on the mixed domains,
3. general Fourier-Laplace support/analyticity equivalence.

If any of those is proposed as an axiom, the exact theorem statement and the
reason it actually shrinks the blocker should be written in `agents_chat.md`
first.

## 8. Exact connection to the current k=2 frontier

The current `k = 2` theorem-3 route is already a disciplined specialization of
OS II:

1. one distinguished time variable,
2. all other data fixed,
3. common kernel first,
4. uniqueness/boundary-value comparison after the one-variable object is in
   place.

So the general-k blueprint should not try to rewrite theorem 3. It should use
the theorem-3 blueprint as the model for how the later general port ought to
look once the larger OS II packages are available.

## 9. Do not do this

1. Do not start from a many-variable contour slogan.
2. Do not reintroduce 4-dimensional hardcoding into the general-`d` theorem
   surface unless the note explicitly says "paper's 4D case" and then gives the
   general-`d` translation.
3. Do not replace the recursive angle package by a false closed-form shortcut.
4. Do not prove growth before regularization.
5. Do not state a new several-variable boundary-value theorem without pointing
   to the exact Chapter V / VI package it comes from.
6. Do not hide the renormalized family `S_{k,ε}` inside a proof term.
7. Do not let the later Lean files collapse the package boundaries back into a
   single monolithic theorem.

## 10. Minimal Lean pseudocode for the full implementation order

```lean
/- Package A: Chapter V.1. -/
theorem local_polydisc_of_real_positive_time := by
  -- cone angle -> dual directions -> directional continuation ->
  -- Malgrange-Zerner -> explicit radius

/- Package B: induction ladder. -/
theorem A_to_P_step := by
  -- scalar analyticity on a mixed domain -> Hilbert-valued Taylor vector

theorem P_to_A_step := by
  -- vector pairings -> scalar candidate -> envelope extension

/- Package C: VI.1. -/
theorem regularized_real_domain_estimate := by
  -- regularizer support -> vector existence -> derivative bounds ->
  -- E0' norm -> directional bounds -> local bound -> real-domain estimate

/- Package D: VI.2. -/
theorem general_k_temperedness_and_boundary_values := by
  -- normalized family -> VI.1 estimate -> stage elimination -> main theorem
```

The point of this pseudocode is that every package named here already has its
mathematical theorem-slot inventory in `docs/os2_detailed_proof_audit.md`.

## 11. What counts as implementation-ready documentation for general k

The general-k docs should be considered ready for later Lean work only when the
following are all explicit:

1. the Chapter V.1 theorem slots,
2. the base-step theorem slots,
3. the full `(A_N) -> (P_N)` transcript,
4. the full `(P_N) -> (A_{N+1})` transcript,
5. the recursive-angle package,
6. the complete VI.1 regularization package,
7. the complete VI.2 renormalized-family package,
8. the infrastructure theorems that are still external to Mathlib/current repo,
9. the file/package split for the future Lean implementation.

This blueprint now records all nine items. The remaining gap is no longer
"what is the route?" but "which theorem gets implemented next in Lean?"

## 12. Expanded theorem-slot inventory by proof package

The general-`k` port should now be documented at the same granularity as the
theorem-3 blueprint: exact theorem slots, exact package boundaries, and exact
"this is where the paper uses SCV input" markers.

### 12.1. Package A: Chapter V.1 local analyticity

The later Lean file should expose the local analyticity package as the
following theorem inventory.

```lean
lemma positive_time_real_configuration_mem_Ck_zero
lemma dual_cone_direction_exists_for_each_time_gap
lemma directional_slice_mem_forward_tube
lemma directional_slice_holomorphic
lemma one_variable_slice_continuation_exists
lemma one_variable_slice_boundary_agrees
lemma finitely_many_directional_slices_cover_local_polydisc
lemma directional_slices_agree_on_pairwise_overlap
lemma local_directional_union_isOpen
lemma local_directional_union_connected
lemma malgrange_zerner_local_polydisc_extension
theorem local_polydisc_of_real_positive_time
```

The documentation should keep the meaning of each slot explicit:

1. the first three are cone/domain geometry,
2. the next three are one-variable continuation inputs,
3. the next three are the gluing geometry,
4. the final two are the actual several-variable analyticity conclusions.

### 12.2. Package B: base step `(A_0) -> (P_0)`

The base step should not be summarized as "delta-family argument." It should be
recorded as:

```lean
lemma delta_family_mem_positive_time_core
lemma scalar_pairing_eq_os_semigroup_formula
lemma scalar_pairing_holomorphic_on_base_domain
lemma scalar_pairing_and_candidate_agree_on_real_edge
lemma scalar_pairing_eq_candidate_on_base_domain
lemma delta_family_limit_recovers_vector
lemma candidate_vector_defined_from_scalar_pairings
lemma candidate_vector_pairings_match_required_scalar_family
lemma candidate_vector_is_unique
theorem A0_to_P0
```

The later implementation should make the scalar-to-vector transition explicit.
The base step is not done once the scalar equality is proved; the vector
reconstruction still needs its own theorem slots.

### 12.3. Package C: induction ladder `(A_N) -> (P_N)`

The induction step should be documented as:

```lean
lemma mixed_domain_scalar_family_defined
lemma mixed_domain_scalar_family_holomorphic
lemma mixed_domain_scalar_family_restricts_to_previous_stage
lemma mixed_domain_scalar_family_agrees_on_real_positive_edge
lemma scalar_family_eq_on_overlap_by_identity_theorem
lemma scalar_family_has_uniform_local_bound
lemma vector_candidate_taylor_coefficients_exist
lemma vector_candidate_series_converges
lemma vector_candidate_pairings_recover_scalar_family
lemma vector_candidate_unique
theorem AN_to_PN
```

The "Taylor coefficients exist" and "series converges" lines should not be
omitted. OS II uses a Hilbert-valued Taylor argument, and the docs should name
that argument as an actual package rather than collapsing it into "by local
analyticity."

### 12.4. Package D: scalar continuation `(P_N) -> (A_{N+1})`

The next-step analyticity package should be recorded as:

```lean
lemma scalar_candidate_defined_from_vector_pairings
lemma scalar_candidate_holomorphic_on_each_generator
lemma scalar_candidate_agrees_on_generator_overlaps
lemma scalar_candidate_holomorphic_on_generating_union
lemma generating_union_contains_real_positive_configurations
lemma generating_union_is_path_connected
lemma generating_union_has_required_envelope
lemma envelope_identifies_with_Ck_next
lemma scalar_candidate_extends_to_Ck_next
lemma extended_scalar_candidate_has_required_boundary_values
theorem PN_to_A_next
```

The generating-union and envelope steps are the exact places where later Lean
files must call out the SCV infrastructure. The docs should never let them hide
inside one unnamed sentence.

### 12.5. Package E: Lemma 5.2 / Corollary 5.3 domain-growth package

The recursive angle package should be written as:

```lean
lemma recursive_angle_sequence_defined
lemma recursive_angle_sequence_monotone
lemma recursive_angle_sequence_positive
lemma recursive_angle_configuration_mem_stage
lemma recursive_angle_time_component_lower_bound
lemma stage_selection_from_time_component
lemma corollary53_uniform_stage_exists
theorem stage_selection_for_given_positive_time
```

The docs should continue to ban any fake closed form for the angles. The only
safe route is the recursive sequence plus the quantitative lower bound.

### 12.6. Package F: VI.1 regularization and real-domain estimates

VI.1 is the longest single package in the general-`k` blueprint. The theorem
inventory should therefore be recorded explicitly:

```lean
lemma regularizer_h_exists
lemma regularizer_h_smooth
lemma regularizer_h_nonnegative
lemma regularizer_h_support_small_ball
lemma regularizer_h_integral_one
lemma scaled_regularizer_support
lemma convolution_regularizer_support
lemma regularized_vector_Psi1_defined
lemma regularized_vector_Psi2_defined
lemma Psi1_Psi2_pairing_formula
lemma regularized_pairing_derivative_formula
lemma regularized_pairing_E0prime_bound
lemma regularized_pairing_directional_bound
lemma regularized_pairing_local_polydisc_bound
lemma regularized_pairing_real_domain_bound
theorem regularized_real_domain_estimate
```

The later implementation should visibly prove the support and normalization
facts before trying to prove any estimate. Those are not optional preliminaries.

### 12.7. Package G: VI.2 renormalized family and `ε -> 0` recovery

The normalized-family package should be documented as:

```lean
lemma normalized_family_defined
lemma normalized_family_holomorphic
lemma normalized_family_uniform_bound_on_fixed_stage
lemma normalized_family_tempered_distribution_limit
lemma normalized_family_boundary_values_match_original
lemma stage_selection_applies_to_given_configuration
lemma epsilon_family_estimate_uniform_in_stage
lemma epsilon_to_zero_recovers_original_distribution
lemma recovered_distribution_is_tempered
theorem general_k_temperedness_and_boundary_values
```

The critical documentation point is that the VI.2 file must keep the
`S_{k,ε}` family explicit. Any later Lean proof that suppresses that family
inside a proof term is already drifting away from the paper.

## 13. Concrete current production hook inventory

The general-`k` port should reuse current production shapes whenever possible.
The following theorem names are already available and should be treated as the
reference interfaces for later package design.

### 13.1. SCV / tube-domain infrastructure

1. `DifferentiableOn.analyticOnNhd_of_finiteDimensional`
2. `identity_theorem_SCV`
3. `SCV.tubeDomain'_isOpen`
4. `SCV.tubeDomain'_isConnected`
5. `identity_theorem_tubeDomain`
6. `SCV.flattenCLE_symm_apply`
7. `SCV.flattenCLE_apply`
8. `SCV.flattenCLE_symm_update`
9. `analyticAt_of_differentiableOn_product`
10. `identity_theorem_product`
11. `SCV.osgood_lemma_product`
12. `tubeDomain_isOpen`
13. `tubeDomain_isPreconnected`
14. `tubeDomain_neg`
15. `edge_of_the_wedge_theorem`

### 13.2. Forward-tube distribution transport

16. `forwardTube_eq_imPreimage`
17. `inForwardCone_iff_mem_forwardConeAbs`
18. `forwardConeFlat_isOpen`
19. `forwardConeFlat_convex`
20. `forwardConeFlat_nonempty`
21. `forwardConeFlat_isCone`
22. `forwardTube_flatten_eq_tubeDomain`
23. `distributional_uniqueness_forwardTube`
24. `boundary_function_continuous_forwardTube_of_flatRegular`
25. `boundary_value_recovery_forwardTube_of_flatRegular`
26. `distributional_uniqueness_forwardTube_of_flatRegular`
27. `polynomial_growth_forwardTube_of_flatRegular`
28. `schwartz_bv_to_flat_repr_dist_apply`
29. `flatRegular_dist_eq_schwartz_bv`
30. `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`
31. `distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero`

### 13.3. Reduced BHW / Route 1 infrastructure

32. `pullbackReducedExtension_translate_uniform`
33. `reduced_pullback_translation_invariant`
34. `route1ReducedWightmanFamily_eq_of_cutoff_canonical`
35. `safeBasepointVec_mem_forwardCone`
36. `safeSection_mem_forwardTube`
37. `descendAlongSafeSection_eq_of_translation_invariant`
38. `exists_uniformShift_eq_of_reducedDiffMap_eq`
39. `route1ReducedPreInputFromSpectrumCondition_factorization`
40. `absoluteDirectionOfReduced_mem_forwardCone`
41. `absoluteApproachOfReduced_mem_forwardTube`
42. `route1ReducedPreInputFromSpectrumCondition_factorization_absoluteApproach`
43. `integral_realDiffCoord_change_variables`
44. `route1ReducedBoundaryIntegral_eq_absoluteBoundaryIntegral`
45. `route1ReducedBoundaryValuesFromSpectrumCondition`
46. `route1AbsoluteBHWExtensionCanonical_translate`

### 13.4. Current theorem-3 / `k = 2` positivity route hooks

47. `tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero`
48. `bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger`
49. `bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit`
50. `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
51. `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
52. `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
53. `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
54. `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
55. `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
56. `eqOn_rightHalfPlane_of_ofReal_eq`
57. `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
58. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero`

### 13.5. K2VI1 concrete one-variable kernel route

59. `differenceOnlyKernel_productShell_to_same_center_of_package_local`
60. `integral_centerDiffShell_eq_of_compactSupport_schwartz_pairing_eq_continuousOn_positiveStrip_local`
61. `integral_centerDiffShell_eq_via_shifted_realDifference_representative_local`
62. `integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local`
63. `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`
64. `zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
65. `exists_common_lifted_difference_slice_strip_bound_of_compactSupport_pairing_eq_comparison_local`
66. `commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_positiveSupport_local`
67. `commonK2TimeParametricKernel_real_eq_schwinger_of_ae_eq_k2TimeParametricKernel_local`
68. `schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectorPackage_local`
69. `commonK2TimeParametricKernel_real_eq_piecewise_local`
70. `commonK2TimeParametricKernel_real_eq_of_pos_local`
71. `commonK2TimeParametricKernel_real_eq_of_neg_local`

The general-`k` port should be visibly shaped like a multi-variable enlargement
of those exact current interfaces.

### 13.6. Exact module-to-package correspondence for the future OS II port

The current `k = 2` lane already exhibits the small-file discipline the later
general-`k` port should follow. The correspondence should be documented
explicitly:

1. Chapter V.1 local analyticity:
   emulate the separation of local-domain, continuity, and holomorphy concerns
   visible in `BHWReducedExtension.lean` and
   `WickRotation/K2VI1/InputCSwapSymmetry.lean`.
2. Base-step scalar continuation:
   emulate `OSToWightmanBoundaryValueLimits.lean`, where the scalar
   holomorphic family, positive-real identification, and uniqueness step are
   distinct declarations.
3. VI.1-style kernel transport:
   emulate the split across
   `K2VI1/InputAFixedTime.lean`,
   `K2VI1/InputACommonBoundary.lean`,
   `K2VI1/InputAKernelReduction.lean`, and
   `K2VI1/InputAHeadBlockTransport.lean`.
   Those files already separate:
   domain theorem,
   common-kernel theorem,
   transport theorem,
   and boundary-value comparison theorem.
4. VI.2-style positivity/closure:
   emulate the split across
   `OSToWightmanBoundaryValuesCompactApprox.lean`,
   `OSToWightmanBoundaryValuesBase.lean`, and
   `OSToWightmanSpatialMomentum.lean`,
   where compact approximation, algebraic summation, and final positivity
   closure are isolated.

So the later OS II port should imitate not only current theorem names but also
the current package architecture:

1. local input files first,
2. uniqueness/boundary transport files second,
3. algebraic closure files third,
4. public frontier wrappers last.

## 14. Exact file/module split with estimated line counts

The future Lean port should now be sized explicitly. A disciplined split would
look like this.

1. `OS2ChapterV1LocalAnalyticity.lean`
   `180-280` lines.
2. `OS2BaseStep.lean`
   `120-220` lines.
3. `OS2InductionLadder.lean`
   `180-300` lines.
4. `OS2DomainGrowth.lean`
   `120-220` lines.
5. `OS2VI1Regularization.lean`
   `260-420` lines.
6. `OS2VI2Renormalized.lean`
   `180-320` lines.
7. `OS2AppendixE0Prime.lean`
   `120-220` lines.

So the full general-`k` port should be expected to land as roughly
`1160-1980` lines of proof-oriented Lean, spread across seven focused files.

## 15. Mathlib/current-repo availability checklist for VI.1 and Chapter V

The general-`k` docs should also record what is already available, so later
implementation does not waste time rediscovering tooling.

### 15.1. Available and reusable now

1. differentiability and `HolomorphicOn` on open domains,
2. connectedness/open-set infrastructure for tube domains,
3. identity theorems and Osgood-style several-variable uniqueness,
4. measure-preserving change of variables,
5. dominated convergence and Fatou-style measure theorems,
6. forward-tube boundary-value transport from regular input,
7. reduced BHW route-1 factorization and boundary-value transport.

### 15.2. Still missing or external to current proved infrastructure

1. Malgrange-Zerner gluing on the mixed directional unions,
2. the required envelope-of-holomorphy theorem for the generating union,
3. the QFT-free tube-boundary-value theorem from polynomial growth,
4. the full Vladimirov-Tillmann package,
5. the final general-`k` renormalized-family boundary-value recovery theorem.

### 15.3. Route consequence

If a later Lean proof of Chapter V or VI.1 reaches for any tool outside those
two lists, the docs should first be updated to say why that new dependency is
mathematically necessary. The general-`k` port should not accrete hidden
external requirements.

## 16. Package-by-package trusted-vs-untrusted checklist

The later port should keep the following status partition explicit.

### 16.1. Trusted at the documentation level

1. package ordering,
2. theorem-slot granularity,
3. recursive-angle route instead of fake closed forms,
4. regularizer support normalization,
5. K2/theorem-3 specialization as the correct model for the one-variable core.

### 16.2. Not yet implemented and therefore still live proof obligations

1. the Chapter V.1 Malgrange-Zerner gluing theorem,
2. the envelope theorem identifying the generating union with the next-stage
   domain,
3. the full VI.1 estimate chain in Lean,
4. the VI.2 `ε -> 0` recovery in Lean,
5. the final general-`k` tempered boundary-value theorem.

### 16.3. Forbidden simplifications

1. hiding the scalar-to-vector reconstruction inside one theorem,
2. hiding the renormalized family `S_{k,ε}`,
3. reusing 4-dimensional paper notation without a general-`d` translation,
4. replacing the envelope step by an unexplained "SCV continuation" line,
5. inserting new axioms without prior documentation and approval.

## 17. Package-by-package proof transcripts

The inventory above names the theorem slots. This section records the order in
which each package should actually be proved, so that the later Lean port does
not have to reconstruct the micro-order from prose.

### 17.1. Chapter V.1 local analyticity transcript

1. Fix a real positive-time configuration.
2. Choose the finitely many directional slices supplied by the cone geometry.
3. Prove one-variable analyticity on each slice.
4. Prove the slices agree on their overlaps.
5. Glue the slices by the Malgrange-Zerner package.
6. Extract the final local polydisc.

The port should not swap steps 3 and 5, and should not try to build the
polydisc before the overlap/gluing theorem exists.

#### 17.1.1. Exact proof transcript for `malgrange_zerner_glue_directional_pieces`

The later Lean file should not treat the Malgrange-Zerner step as a single
black-box theorem. The proof should be split into the following micro-order.

1. For each directional basis vector `e_μ`, define the local flat-tube domain
   `U_μ` on which the one-variable continuation already exists.
2. Prove `U_μ` is open.
3. Prove the directional continuation `F_μ` is holomorphic on `U_μ`.
4. For each pair `μ, ν`, identify an explicit overlap region
   `U_μν ⊆ U_μ ∩ U_ν` containing a real segment through the basepoint.
5. Prove `U_μν` is nonempty and connected.
6. Prove `F_μ = F_ν` on the real segment inside `U_μν`.
7. Apply the identity theorem on `U_μν` to conclude `F_μ = F_ν` on all of the
   overlap.
8. Define the glued function on `⋃_μ U_μ` by choosing any index `μ` with
   `z ∈ U_μ`.
9. Prove that definition is independent of the chosen `μ` by the overlap
   theorem from step 7.
10. Prove the glued function is holomorphic on the union by the local
    holomorphic gluing lemma.
11. Prove the target local polydisc is contained in `⋃_μ U_μ`.
12. Restrict the glued function to that polydisc.

The required theorem-slot inventory should therefore be understood as:

```lean
def directionalFlatDomain (μ : Fin (d + 1)) : Set (TimeDiffConfig k)
lemma directionalFlatDomain_isOpen
lemma directionalFlatExtension_holomorphic
lemma overlap_real_segment_nonempty
lemma overlap_connected
lemma directionalFlatExtensions_agree_on_real_segment
lemma directionalFlatExtensions_agree_on_overlap
def gluedDirectionalFunction : Set.iUnion directionalFlatDomain → ℂ
lemma gluedDirectionalFunction_wellDefined
lemma gluedDirectionalFunction_holomorphic
lemma local_polydisc_subset_directional_union
```

Without these steps, the general-k documentation is still hiding the hardest
part of Lemma 5.1 behind a theorem name.

### 17.2. Base step `(A_0) -> (P_0)` transcript

1. Define the scalar candidate from the already-known `k = 2` Schwinger data.
2. Show that candidate is holomorphic on the base domain.
3. Prove agreement with the required real-edge scalar pairing.
4. Use a delta-family approximation to reconstruct the corresponding vector.
5. Prove uniqueness from equality of all scalar pairings.

The docs should keep step 4 explicit. The vector is not obtained "for free"
from the scalar identity theorem.

### 17.3. Induction step `(A_N) -> (P_N)` transcript

1. Fix the mixed domain and define the scalar family by pairing with the
   previous-stage vectors.
2. Prove holomorphy on each variable block.
3. Use the local analyticity package to obtain joint analyticity.
4. Establish the required local bounds.
5. Build the Hilbert-valued Taylor coefficients.
6. Sum the resulting series and verify it matches the scalar pairings.

The docs should treat the Taylor package as the exact bridge from scalar
analyticity to vector-valued analyticity.

### 17.4. Scalar continuation `(P_N) -> (A_{N+1})` transcript

1. Start from the vector family already constructed at stage `N`.
2. Pair that family against arbitrary test vectors to get scalar candidates.
3. Prove those scalar candidates agree on overlaps of the generating union.
4. Glue them to one scalar holomorphic function on the generating union.
5. Invoke the envelope package to extend to the whole next-stage domain.
6. Check the required real-edge values.

This transcript is the exact place where the envelope theorem enters. It should
never be hidden elsewhere.

#### 17.4.1. Exact proof transcript for the envelope step

The later Lean file should separate the overlap-gluing stage from the actual
envelope extension stage. The proof should read:

1. For each generator domain `G_i`, define the scalar candidate `F_i`.
2. Prove `F_i` is holomorphic on `G_i`.
3. For each pair `i, j`, identify an explicit real-edge subset
   `R_ij ⊆ G_i ∩ G_j`.
4. Prove `R_ij` is nonempty and has accumulation in the overlap.
5. Prove `F_i = F_j` on `R_ij` from the common real-slice data.
6. Apply the identity theorem to deduce `F_i = F_j` on `G_i ∩ G_j`.
7. Glue the `F_i` to one holomorphic function `F_union` on the generating
   union `G := ⋃_i G_i`.
8. Prove the envelope theorem
   `EnvelopeOfHolomorphy G = C_k^(N+1)`.
9. Extend `F_union` uniquely to the envelope.
10. Rewrite the envelope as the next-stage OS II domain and package the result
    as `A_{N+1}`.

So the later theorem slots should be read as:

```lean
def generatingUnionCandidate (i : GeneratorIndex) : GeneratorDomain i → ℂ
lemma generatingUnionCandidate_holomorphic
lemma real_edge_subset_generator_overlap
lemma generator_overlap_has_accumulation
lemma generatingUnionCandidates_agree_on_real_edge
lemma generatingUnionCandidates_agree_on_overlap
def gluedScalarCandidateOnGeneratingUnion : GeneratingUnion → ℂ
lemma gluedScalarCandidateOnGeneratingUnion_holomorphic
lemma generatingUnion_envelope_eq_Ck_next
lemma gluedScalarCandidate_extends_to_envelope
lemma extendedScalarCandidate_has_realSlice_values
```

The envelope theorem itself should be treated as a QFT-free SCV package. The
OS II proof is only allowed to *consume* it here, not silently rebuild it.

### 17.5. Lemma 5.2 / Corollary 5.3 transcript

1. Define the recursive angle sequence.
2. Prove positivity and monotonicity.
3. Prove the stage-membership induction.
4. Prove the quantitative lower bound on the selected component.
5. Choose a stage large enough for a given positive-time configuration.

The docs should continue to ban any closed-form shortcut in step 1.

### 17.6. VI.1 transcript

1. Build the regularizer and prove support/normalization.
2. Define `Ψ₁` and `Ψ₂`.
3. Derive the regularized pairing formula.
4. Prove the derivative bounds.
5. Use `E0'` to prove the norm estimate.
6. Convert the norm estimate to directional bounds.
7. Convert directional bounds to local-polydisc bounds.
8. Convert local-polydisc bounds to the real-domain estimate.

The later Lean file should visibly move through those eight steps in order.

### 17.7. VI.2 transcript

1. Define the renormalized family `S_{k,ε}`.
2. Prove holomorphy and the fixed-stage estimate.
3. Use Corollary 5.3 to choose a stage for the target configuration.
4. Apply the VI.1 estimate at that stage.
5. Pass to the `ε -> 0` limit.
6. Recover the original distribution.
7. Package temperedness and boundary values.

This is the exact point where the docs should guard against hiding the
renormalized family inside an unnamed proof term.

## 18. Completion checklist for the future general-k Lean port

The later port should not be described as "ready to start" unless all of the
following are explicitly pinned in the docs:

1. exact theorem slots for Packages A-G,
2. exact current production hooks reused as models,
3. exact external SCV packages still missing,
4. exact file/module split,
5. exact proof transcript order inside each package,
6. exact trusted-vs-untrusted partition.

This blueprint now records all six.

## 19. Final fixed implementation choices for the general-k port

The purpose of this section is to remove the last planning ambiguity before a
later Lean port begins. The choices below should be treated as fixed
documentation guidance, not as optional cross-checks to be reinvented during
implementation.

The fixed choices are:

1. use the `GeneratorIndex` structure below for the `(P_N) -> (A_{N+1})`
   generating union,
2. keep `generatingUnion_envelope_eq_Ck_next` and
   `gluedScalarCandidate_extends_to_Ck_next` as two separate declarations,
3. use the one-point SCV interface from
   `docs/scv_infrastructure_blueprint.md` as the only allowed boundary-value
   input to VI.1,
4. keep the seven-file split and import boundaries from Section 5.1/5.2 unless
   an exact compile failure later forces a local adjustment.

There is therefore no remaining route ambiguity at the documentation level. A
later implementation may still discover theorem-proof difficulty, but it should
not need to rediscover the package shape.

### 19.1. Recommended exact indexing scheme for the generating union

The later Lean port should not invent a fresh ad hoc indexing scheme for the
`(P_N) -> (A_{N+1})` generating union. The recommended documentation-standard
choice is:

```lean
structure GeneratorIndex where
  n m : ℕ
  hn : 1 ≤ n
  hm : 1 ≤ m
  hnm : k = n + m - 1
```

With this choice:

1. each generator domain corresponds to one admissible split `k = n + m - 1`,
2. each scalar candidate is literally the pairing
   `(Ψ_n(x,ζ), Ψ_m(x',ζ'))`,
3. the overlap statements are formulated between two such splits
   `i j : GeneratorIndex`.

The documentation rule should therefore be:

1. define `GeneratorDomain i`,
2. define `generatingUnion := ⋃ i : GeneratorIndex, GeneratorDomain i`,
3. phrase all overlap and envelope theorems using that exact indexing type.

That removes one implementation choice that otherwise would be rediscovered
later during the Lean port.

### 19.2. Recommended exact theorem surface for the envelope package

The later SCV/OS II interface should also be fixed now rather than deferred to
the implementation phase. The recommended theorem statement is:

```lean
theorem generatingUnion_envelope_eq_Ck_next
    (N k : ℕ) :
    EnvelopeOfHolomorphy (generatingUnion (N := N) (k := k)) =
      Ck (N + 1)
```

and the consumer theorem in the OS II file should be:

```lean
lemma gluedScalarCandidate_extends_to_Ck_next
    (hhol : HolomorphicOn gluedScalarCandidateOnGeneratingUnion
      (generatingUnion (N := N) (k := k))) :
    ∃ Fnext,
      HolomorphicOn Fnext (Ck (N + 1)) ∧
      EqOn Fnext gluedScalarCandidateOnGeneratingUnion
        (generatingUnion (N := N) (k := k))
```

The later port should not hide the equality of domains inside the extension
lemma itself. The domain-identification theorem and the extension theorem are
two separate mathematical steps and should remain two separate declarations in
the docs and in Lean.

### 19.3. Recommended exact import boundaries for the seven-file split

The file split in Section 14 is now strong enough that the import boundaries
can also be fixed more concretely:

1. `OS2ChapterV1LocalAnalyticity.lean`
   imports:
   - `SCV/IdentityTheorem.lean`
   - `SCV/TubeDomainExtension.lean`
   - the one-variable OS I continuation support file(s)
2. `OS2BaseStep.lean`
   imports:
   - `OS2ChapterV1LocalAnalyticity.lean`
   - the current `k = 2` scalar continuation support package
3. `OS2InductionLadder.lean`
   imports:
   - `OS2BaseStep.lean`
   - the scalar-product formula / reflected Schwinger pairing package
4. `OS2DomainGrowth.lean`
   imports:
   - `OS2InductionLadder.lean`
   - no VI.1 regularization files
5. `OS2VI1Regularization.lean`
   imports:
   - `OS2DomainGrowth.lean`
   - the appendix `E0'` package
   - the SCV one-variable tube-boundary constructor package
6. `OS2VI2Renormalized.lean`
   imports:
   - `OS2VI1Regularization.lean`
   - `OS2DomainGrowth.lean`
7. `OS2AppendixE0Prime.lean`
   imports:
   - only the measure/Schwartz/Hermite infrastructure it needs

So even the import graph is now close to fixed. The remaining work is mostly to
realize those boundaries in Lean, not to decide them from scratch.

### 19.4. Recommended first theorem to implement in each future file

The later port should not open all seven files and then decide locally where to
start. The first theorem in each file should already be fixed by the docs:

1. `OS2ChapterV1LocalAnalyticity.lean`
   starts with
   `dual_cone_direction_exists_for_each_time_gap`,
   because every later slice/domain theorem depends on having the admissible
   directional basis in hand.
2. `OS2BaseStep.lean`
   starts with
   `scalar_pairing_eq_os_semigroup_formula`,
   because the base-step vector reconstruction is pointless until the scalar
   candidate is identified.
3. `OS2InductionLadder.lean`
   starts with
   `mixed_domain_scalar_family_defined`,
   because every later Taylor/vector theorem in that file is downstream of the
   scalar family itself.
4. `OS2DomainGrowth.lean`
   starts with
   `recursive_angle_sequence_defined`,
   because the stage-membership induction and Corollary 5.3 both depend on that
   sequence package.
5. `OS2VI1Regularization.lean`
   starts with
   `regularizer_h_exists`,
   because every later estimate in VI.1 depends on support/normalization of the
   mollifier.
6. `OS2VI2Renormalized.lean`
   starts with
   `normalized_family_defined`,
   because suppressing `S_{k,ε}` is exactly what the docs are trying to forbid.
7. `OS2AppendixE0Prime.lean`
   starts with
   `hermite_projection_defined`,
   or whatever exact local theorem name is chosen for the Hermite-expansion
   basis package behind `E0'' => E0'`.

That means a later implementation can begin each file with one theorem that is
mathematically first, rather than re-deciding the local entry point.

### 19.5. Package-by-package exit criteria for the future OS II port

The later Lean work should consider a package complete only when the following
end-of-file conditions hold:

1. `OS2ChapterV1LocalAnalyticity.lean`
   ends with
   `local_polydisc_of_real_positive_time`.
2. `OS2BaseStep.lean`
   ends with
   `A0_to_P0`.
3. `OS2InductionLadder.lean`
   ends with
   `AN_to_PN`.
4. `OS2DomainGrowth.lean`
   ends with
   `stage_selection_for_given_positive_time`.
5. `OS2VI1Regularization.lean`
   ends with
   `regularized_real_domain_estimate`.
6. `OS2VI2Renormalized.lean`
   ends with
   `general_k_temperedness_and_boundary_values`.
7. `OS2AppendixE0Prime.lean`
   ends with the exact `E0'' => E0'` theorem slot documented in
   [os2_detailed_proof_audit.md](/Users/xiyin/OSReconstruction/docs/os2_detailed_proof_audit.md).

The docs should therefore be read as giving each future file both:

1. a fixed first theorem to write,
2. a fixed final theorem whose proof closes the package.

That is the strongest project-level protection against future route drift.
