# OS I Detailed Proof Audit

Purpose: this note records a close reading of Osterwalder-Schrader I,
`references/Reconstruction theorem I.pdf`, with the explicit goal of guiding the
Lean formalization and preventing theorem-shape drift. It is not a historical
summary. It is a proof audit: what the paper actually proves, what each step
uses, where hidden lemmas enter, and which parts are no longer safe after OS II.

This note should be read together with:
- `docs/os_reconstruction_reading_notes.md`
- `docs/openclaw_comprehensive_reading_note.md`
- `docs/os2_detailed_proof_audit.md`

## 1. What OS I Actually Does

OS I proves an `E -> R` and `R -> E` correspondence under Euclidean axioms
`E0-E4`, but the forward direction relies on its Section 8 Lemma 8.8. OS II
later corrects that step. So the right modern reading is:

- OS I Section 4 contains the sound semigroup/Hilbert-space and one-variable
  continuation mechanism.
- OS I Section 5 contains the sound Wick-rotation construction of Euclidean
  Green's functions from Wightman functions.
- OS I Section 8.8 is not sound as a many-variable continuation theorem.

The formalization should therefore treat OS I as:
- authoritative for the semigroup construction, formulas `(4.3)`-`(4.11)`,
  the explicit test-function transform `(4.19)`-`(4.20)`, positivity transfer,
  cluster transfer, and the basic `R -> E` restriction;
- not authoritative for the leap from separate one-variable continuation to a
  joint many-variable Fourier-Laplace statement.

But there is one crucial nuance for theorem 3: the **test-function transform**
in Section 4.3 is explicit and one-variable in nature, whereas the
**distribution** `\tilde W` used in `(4.24)`-`(4.28)` is imported from `(4.12)`
and therefore from the Lemma-8.8 route. In production this dependence is
repaired by the OS II `OSLinearGrowthCondition` route; the docs must keep that
split explicit.

## 2. Section 2: Test Functions and Distribution Surfaces

The key spaces are:
- `°S(R^{4n})`: Schwartz functions vanishing with all derivatives on
  coincidence diagonals;
- `S_+(R^{4n})`: positive-time ordered Schwartz tests;
- `S(R_+) = S(R) / S(R_-)`;
- sequence spaces built from finite-support tuples of such tests.

What matters for Lean:
- OS I already works on an off-diagonal Euclidean surface. The present
  zero-diagonal / `ZeroDiagonalSchwartz` discipline is not an artificial
  restriction; it is faithful to the paper's information content.
- the quotient-space point of view on positive-time test functions is essential
  for the semigroup construction and later support statements.

Hidden mathematical input:
- completeness and nuclearity facts for these Schwartz-type spaces;
- equivalence of quotient and restriction seminorms for `S(R_+)`.

These are not the live frontier in the current Lean work, but they explain why
the formalization keeps quotient and support-control infrastructure close to the
OS route.

## 3. Section 3: Axiom Surfaces

OS I uses:
- `E0` temperedness,
- `E1` Euclidean covariance,
- `E2` reflection positivity,
- `E3` symmetry,
- `E4` cluster.

The paper's first main conceptual claim is that the spectral condition on the
Wightman side is not an extra Euclidean axiom. It is extracted from the
semigroup built using `E2` and `E1`.

For the formalization this remains an important route constraint:
- one should not import spectral information into the Euclidean side by hand if
  the OS semigroup route is available;
- the positive semigroup is the engine that generates the positive-energy
  support statement.

## 4. Section 4.1: Hilbert Space and Semigroup

This is the most important sound part of OS I for the current project.

### 4.1.1. The OS form

The sesquilinear form is

`(f,g) = Σ_{n,m} S_{n+m}(Θ f_n^* × g_m)`.

The paper uses:
- `E2` for positive semidefiniteness;
- the algebra of the cross product and time reflection for conjugate symmetry;
- quotient by the null space and completion to build the Hilbert space `H`.

Nothing in this step compares Euclidean and Minkowski test functions directly.
That is important: the Hilbert space is built intrinsically from the OS form.

### 4.1.2. Spatial translations and time semigroup

Spatial translations act unitarily because they preserve the OS form.
Positive time translations act by contractions on the quotient. The crucial
estimate is the iterative inequality yielding `||T_t|| <= 1`.

What the proof really uses:
- reflection positivity to get a positive form;
- Euclidean covariance to rewrite translated pairings;
- a semigroup law on positive-time-supported tests;
- continuity from the Schwartz/distribution topology.

This is the direct paper ancestor of:
- `OSToWightmanSemigroup.lean`,
- the OS Hilbert space,
- the positive self-adjoint generator `H`,
- holomorphic semigroup matrix elements.

### 4.1.2a. Detailed proof transcript for the contraction estimate

The contraction proof in OS I runs through formulas `(4.6)`-`(4.9)` and should
be read as follows.

1. Define the positive-time translation operator `T_t` on the Euclidean test
   sequence space by shifting every argument backward in time by `t e_0`.
2. Euclidean covariance implies
   `(T_t f, g) = (f, T_t g)` for `t >= 0`.
3. The semigroup property on test functions gives `T_t T_s = T_{t+s}`.
4. A crude polynomial bound `(4.7)` shows `|(f, T_t f)|` grows at most
   polynomially in `t`.
5. Apply Cauchy-Schwarz repeatedly to the sequence
   `(f, T_t f), (f, T_{2t} f), (f, T_{4t} f), ...`.
6. This yields the iterative estimate
   `|(f, T_t f)| <= (f,f)^{1 - 2^{-n}} (f, T_{2^n t} f)^{2^{-n}}`.
7. Insert the polynomial bound on `(f, T_{2^n t} f)` and let `n -> ∞`.
8. The polynomial factor disappears in the limit because it is raised to
   `2^{-n}`.
9. Conclude `|(f, T_t f)| <= (f,f)`, hence `‖T_t‖ <= 1` on the quotient.

The hidden algebra in step 5 should also be written explicitly, because this is
exactly where a later Lean implementation can easily lose the semigroup/symmetry
bookkeeping.

The first Cauchy-Schwarz step is:

1. start from `|(f, T_t f)|^2`;
2. apply Cauchy-Schwarz in the positive OS inner product:
   `|(f, T_t f)|^2 <= (f,f) (T_t f, T_t f)`;
3. use the covariance/symmetry identity from step 2,
   `(T_t f, g) = (f, T_t g)`, with `g = T_t f`;
4. conclude `(T_t f, T_t f) = (f, T_{2t} f)`.

So the real one-step inequality is

`|(f, T_t f)|^2 <= (f,f) (f, T_{2t} f)`.

Iterating this inequality gives

`|(f, T_t f)|^(2^n) <= (f,f)^(2^n - 1) (f, T_{2^n t} f)`,

and taking the `2^{-n}` power yields the displayed estimate in step 6.

This matters because the proof does not use Cauchy-Schwarz on an arbitrary
sequence of unrelated scalars. It uses:
- positivity of the OS form,
- the semigroup identity,
- and the symmetry relation `(T_t f, g) = (f, T_t g)`.

So the contraction estimate is not immediate from positivity alone. It uses:
- covariance,
- semigroup iteration,
- a polynomial growth estimate,
- and a limiting argument.

### 4.1.2b. Why the time generator is positive

Once `T_t` is a weakly continuous semigroup of self-adjoint contractions on the
completed Hilbert space, standard semigroup theory gives:
- `T_t = e^{-tH}` for a positive self-adjoint operator `H`.

The positivity of `H` is not an extra axiom. It is exactly the Hilbert-space
encoding of the contraction property `‖T_t‖ <= 1`.

### 4.1.3. What should be preserved in Lean

The right theorem shape is:
- first construct the Hilbert space and contraction semigroup;
- then study scalar matrix elements of `e^{-τH}`;
- only after that identify these scalars with Schwinger/Wightman analytic
  objects.

This rules out category-jumping shortcuts where a later boundary-value theorem
is smuggled in before the semigroup factorization is understood.

## 5. Section 4.1 and 4.2: One-Variable Analytic Continuation

The formulas around `(4.10)` and `(4.11)` are the heart of OS I.

The paper packages a Schwinger function with one distinguished time gap as a
matrix element:

`<Ψ_left, e^{-τH} Ψ_right>`.

The remaining variables are treated as parameters collected into a test object
`h_m`. The continuation variable is only one complex time.

This is the key disciplined reading:
- OS I does not first build a fully many-variable analytic function and then
  retroactively factor it.
- it starts from a one-gap scalar matrix element with all remaining variables
  already packaged as parameters.

This is exactly the theorem shape the current Lean `k = 2` frontier should
respect. In present repo language:
- the genuine content is a one-variable parameterized semigroup object;
- any center/difference or shell bookkeeping is acceptable only insofar as it
  isolates that parameter object faithfully.

### 5.1. Detailed proof transcript for `(4.10)`-`(4.11)`

The one-variable continuation mechanism is:

1. Fix left and right Euclidean test data `f_m`, `g_n`.
2. Form the corresponding Hilbert vectors `v(f_m)` and `v(g_n)`.
3. Insert the complex semigroup `T_{t+is} = e^{-(t+is)H}` between them.
4. Smear the resulting scalar function in the real parameter `s` against a
   one-variable test `h`.
5. View the resulting functional as acting on the tensor-product test object
   `Θ f_m^* × g_n × h`.
6. By nuclearity / Schwartz continuity, that functional is represented by a
   distribution `S^{(m)}` in the distinguished time variable.
7. The Cauchy-Riemann equation in the half-plane then implies that this
   distribution is the boundary value of a holomorphic function.
8. This holomorphic function is exactly the analytic continuation of the
   Schwinger function in the chosen time gap.

The key discipline point is step 5: all other variables are already packaged
into the left/right Hilbert vectors before the complex variable enters.

### 5.2. Why this is only a one-gap theorem

The paper proves analyticity in the single variable `t + is` because:
- there is one semigroup parameter,
- the remaining spacetime variables sit inside fixed test data,
- the Cauchy-Riemann argument is one-variable.

So even though the resulting Schwinger expression still depends on many
parameters, the analytic theorem itself is one-dimensional. This is exactly why
OS I Section 8.8 later overreaches: it tries to globalize this one-gap result
to many gaps without the Chapter V induction that OS II later provides.

## 6. Section 4.2: Spectrum Condition

OS I derives the spectral condition from the semigroup:
- the positive generator gives a Fourier-Laplace representation with support in
  the forward cone;
- Lorentz covariance is then recovered from Euclidean covariance through the
  analytic continuation.

This matters for Lean in two ways:
- it justifies treating the spectral condition as downstream from the OS
  semigroup construction rather than upstream data on the Euclidean side;
- it warns against replacing the semigroup argument by a direct support claim
  unless that replacement is already formalized and route-approved.

## 7. Section 4.3: Positivity

OS I proves Wightman positivity by identifying the reconstructed Wightman
pairing with the Hilbert-space norm obtained from the OS form.

### 7.0. Production note: OS I Section 4.3 is used only through the OS II repair

The current production route is **not** the literal OS I `(4.12)` route.

Production's `bvt_W` is built from
`full_analytic_continuation_with_symmetry_growth OS lgc n` in
`OSToWightmanBoundaryValuesBase.lean`, and that construction explicitly records
that the linear-growth condition `OSLinearGrowthCondition` is the OS II repair
of the gap in OS I Lemma 8.8.

So the later Lean implementation of Section 4.3 should keep two objects
separate:

1. the Section-4.3 **test-function transform** `f ↦ \check f` from
   `(4.19)`-`(4.20)`, which is explicit and one-variable in character;
2. the Wightman-side kernel `\tilde W` / `bvt_W`, which in production is
   imported from the OS II repaired analytic-continuation route rather than
   from the broken OS I Lemma 8.8.

Whenever this audit mentions "Section 4.3" below, read it under that
production convention.

The theorem-shape lesson is subtle:
- OS I does not prove Euclidean positivity by rewriting the OS form as a
  Minkowski pairing on the same test function.
- rather, it constructs the Minkowski pairing from the common semigroup /
  Fourier-Laplace object and then identifies it with a Hilbert norm.

This is exactly why later false routes of the form

`OS inner product = Wightman inner product on the nose`

are mathematically wrong even if they look psychologically close to the paper.

The paper's route is:
- build a common analytic object;
- recover the Wightman distribution as a boundary value of that object;
- prove positivity because both arise from the same positive Hilbert-space
  construction.

More explicitly, the proof package is:
1. start with a finite Borchers-type sequence of test functions on the
   Minkowski side;
2. package it into the OS Hilbert-space vectors already used for the semigroup;
3. identify the reconstructed Wightman pairing with the scalar product of those
   vectors via the Fourier-Laplace / boundary-value theorem;
4. conclude nonnegativity from positivity of the OS Hilbert norm.

What is absent from the paper:
- no equality between the Euclidean OS pairing and the Minkowski pairing on the
  same literal test-function formula;
- no direct rewriting of `S_n(f)` as `W_n(f)` before the common analytic object
  has been identified.

This is the single most important positivity-route warning for the repo.

### 7.1. Detailed proof chain of Section 4.3

The paper's positivity proof is not a single comparison theorem. It is a chain
of constructions:

1. For each Minkowski test sequence `f`, define Euclidean positive-time data by
   the inverse Laplace/Fourier transform in `(4.19)` and `(4.20)`.
2. Prove in Lemma 4.1 that this transform is:
   - continuous,
   - injective,
   - and has dense range onto the target Euclidean test space.
3. Compose with the OS quotient map `v` from Section 4.1 to obtain
   `w(f) = v(\tilde f)`.
4. Prove in Lemma 4.2 that `w` is continuous for the Wightman test topology.
5. Extend `w` by continuity to all Wightman test sequences and rename the map
   `u`.
6. Show that the Wightman quadratic form is exactly `(u(f), u(f))`.
7. Conclude positivity because OS Hilbert norms are positive.

The logical dependency behind step 1 should be spelled out even more literally:

1. Section 4.1 constructs the Hilbert space and the distribution `\tilde W`
   through `(4.12)`, and in the original paper this uses Lemma 8.8;
2. formulas `(4.19)`-`(4.20)` then define the **test-function** transform
   `f ↦ \check f` explicitly as a Fourier-Laplace integral on positive-time
   inputs;
3. Lemma 4.1 studies that explicit transform on the test-function side;
4. Lemma 4.2 and Eq. `(4.28)` combine the explicit transform with the already
   constructed `\tilde W` kernel.

So the positivity proof is not allowed to conflate:
- the explicit test-function transform `(4.19)`-`(4.20)`, and
- the Wightman-side kernel `\tilde W` consumed later in `(4.24)`-`(4.28)`.

In the production formalization, the second object must come from the repaired
OS II `full_analytic_continuation_with_symmetry_growth` / `OSLinearGrowthCondition`
route rather than from the flawed OS I Lemma 8.8.

Every one of those steps is mathematically necessary. If a later proof attempt
tries to jump straight from "Wightman data" to "positive norm" without the
intermediate continuity-and-density package, it is skipping part of OS I.

### 7.2. Lemma 4.1 unpacked

Lemma 4.1 is the first hidden workhorse. The map `f_n -> \check f_n` is an
explicit Fourier-Laplace transform on test functions:

- the Laplace factor forces positive-energy support,
- the codomain is the half-space Schwartz space `L(R_+^{4n})`,
- and the kernel is trivial.

The proof uses:
1. the isomorphism between the intermediate positive-energy test space and the
   Euclidean positive-time test space,
2. the safe one-variable Section 8 lemmas, explicitly the lemma cited in the
   paper text as Lemma 8.2 together with the fact that the Fourier transform is
   an automorphism of Schwartz space,
3. continuity of the Fourier transform on Schwartz space.

So when formalizing this map, the honest local sublemmas are:
- continuity of the Laplace/Fourier transform on the chosen Schwartz quotient,
- injectivity from positive-support uniqueness,
- and, if needed later, density only on the honest quotient-side half-space
  carrier rather than on the current support-restricted subtype source.

The documentation should name a different hidden dependency instead:
- the transform in `(4.19)`-`(4.20)` is explicit on test functions,
- but the later quadratic identity uses `\tilde W` from `(4.12)`,
- and in the original paper `(4.12)` comes from Lemma 8.8.

So the later Lean port should break the Section-4.3 dependency chain as:

1. define the explicit test-function transform `(4.19)`-`(4.20)`;
2. prove continuity and injectivity of that transform on the current
   support-restricted positive-time source;
3. record the honest quotient-side dense map separately, rather than asserting
   dense range for the support-restricted source itself;
4. import the Wightman-side kernel from the OS II repaired continuation route;
5. combine the two through Lemma 4.2 and Eq. `(4.28)`.

Implementation-level theorem-slot inventory for that corrected chain:

```lean
lemma section43_testFunctionTransform
    :
    EuclideanPositiveTimeTestSequence d → Section43PositiveEnergyTestSequence d := by
  -- formulas `(4.19)`-`(4.20)` as an explicit Fourier-Laplace transform

lemma section43_testFunctionTransform_continuous :
    Continuous (section43_testFunctionTransform (d := d)) := by
  -- continuity of the explicit transform on the chosen half-space codomain

lemma section43_testFunctionTransform_injective
    :
    Function.Injective (section43_testFunctionTransform (d := d)) := by
  -- one-variable positive-support uniqueness in each time variable

lemma not_denseRange_section43_testFunctionTransform
    :
    ¬ DenseRange (section43_testFunctionTransform (d := d)) := by
  -- current support-restricted subtype is too small; see production 1D obstruction

lemma denseRange_section43PositiveEnergyQuotientMap
    :
    DenseRange (section43PositiveEnergyQuotientMap (d := d)) := by
  -- quotient-side dense map from ambient Schwartz space

lemma section43_wightmanKernel_from_os2_repair
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ K, CorrectedSection43Kernel d OS lgc K := by
  -- this is where production replaces the broken OS I Lemma 8.8 route
```

This is intentionally more detailed than the paper, because otherwise the later
Lean implementation would still have to choose where the explicit
Fourier-Laplace test-function package stops and the OS-II-repaired Wightman
kernel package begins.

### 7.2.1. What part of Section 4.3 is one-variable, and what part is not

The extracted paper text is explicit about the **Lemma 4.1** part:

- Lemma 4.1 reduces the claim to the map `/^J -> f_n`,
- then says this is "an easy consequence of Lemma 8.2 and the fact that the
  Fourier transform is a homomorphism of Schwartz space onto itself."

So the correct mathematical reading is split into two pieces:

1. **Test-function transform (Lemma 4.1):**
   `f ↦ \check f` uses only Lemma 8.2 (one-variable positive-support
   Fourier/Laplace) plus the Schwartz Fourier automorphism. This step is safe
   in OS I paper logic and does not depend on the broken Lemma 8.8.

2. **Section-4.3 positivity argument as a whole (Eq. (4.28)):**
   it consumes the Wightman distribution `\tilde W` from `(4.12)` inside
   `(4.13)` / `(4.24)` / `(4.28)`. In OS I, `\tilde W` is built using
   Lemma 8.8, so the Section-4.3 positivity argument transitively depends on
   Lemma 8.8 in the original paper.

3. **Production reading:**
   the Lemma-8.8 dependency is bypassed via the OS II
   `OSLinearGrowthCondition` repair. Production's `bvt_W` is constructed from
   `full_analytic_continuation_with_symmetry_growth OS lgc n` in
   `OSToWightmanBoundaryValuesBase.lean`, so the formalization is safe even
   though the original OS I route is not.

For Lean purposes, the map `f_n -> \tilde f_n` should therefore be decomposed
into the following theorem slots:

1. a one-variable positive-support Fourier/Laplace equivalence on Schwartz
   quotients;
2. a tensor-product / iterated-variable lifting theorem that assembles the
   `n`-variable transform from repeated one-variable transforms;
3. the honest quotient-side dense map onto the positive-energy codomain,
   rather than a false dense-range theorem for the support-restricted
   positive-time transport itself;
4. an injectivity theorem whose proof uses only one-variable positive-support
   uniqueness in each time variable.

### 7.2.2. Exact implementation transcript for Lemma 4.1

The later Lean implementation should treat Lemma 4.1 as a three-layer proof,
not as one theorem proved by a single magical Paley-Wiener invocation.

Layer A. One-variable transform.

1. Define the one-variable Section-4.3 operator on positive-time Schwartz test
   functions.
   - this operator is the actual Euclidean-time Laplace/Fourier transform from
     `(4.19)`-`(4.20)`;
   - it lands in the positive-energy half-line codomain `q⁰ ≥ 0`.

2. Prove its key honest property:
   - injective / kernel-zero on the current support-restricted Euclidean
     source.

3. Record the honest quotient-side density statement separately:
   - the ambient-Schwartz quotient map onto the half-line codomain has dense
     range;
   - the support-restricted transport itself does not.

4. The exact analytic suppliers for this one-variable package are:
   - `SCV.fourierLaplaceExt`,
   - `SCV.paley_wiener_half_line`,
   - the automorphism property of the Fourier transform on Schwartz space.

Layer B. Multi-variable assembly.

1. Freeze all variables except one Euclidean time variable.
2. Apply the one-variable transform in that distinguished variable.
3. Iterate over the `n` time variables.
4. Apply the ordinary spatial Fourier transform.
5. Conclude that the full degree-`n` image lies in the positive-energy
   Schwartz codomain.

This is the exact sense in which the full map is "an easy consequence of
Lemma 8.2 and Fourier automorphism": the paper is not appealing to a genuine
many-variable Paley-Wiener theorem here.

Layer C. Topological consequences.

1. continuity of the degree-`n` map follows from continuity of each elementary
   one-variable transform and the spatial Fourier automorphism;
2. injectivity follows from the one-variable kernel-zero theorem, applied one
   time variable at a time;
3. no separate dense-range theorem is needed on the support-restricted source;
   the honest dense map is the ambient-Schwartz quotient map onto the
   half-space codomain. For positive degree, the literal support-restricted
   transport is in fact not dense; degree `0` is exceptional because the
   source already equals the ambient Schwartz space there.

So the honest implementation theorem package is:

```lean
lemma section43_oneVar_transform
    : EuclideanPositiveTimeTest1D →L[ℂ] Section43PositiveEnergy1D := by
  ...

lemma section43_oneVar_transform_injective :
    Function.Injective section43_oneVar_transform := by
  ...

lemma denseRange_section43PositiveEnergyQuotientMap1D :
    DenseRange section43PositiveEnergyQuotientMap1D := by
  ...

lemma section43_component_transform
    (n : ℕ) :
    EuclideanPositiveTimeComponent d n →L[ℂ]
      Section43PositiveEnergyComponent d n := by
  ...

lemma section43_component_transform_injective
    (n : ℕ) :
    Function.Injective (section43_component_transform (d := d) n) := by
  ...

lemma denseRange_section43PositiveEnergyQuotientMap
    (n : ℕ) :
    DenseRange (section43PositiveEnergyQuotientMap (d := d) n) := by
  ...

/-- Stage-5 prerequisite: multivariate quotient descent from the abstract
Section-4.3 transform to the concrete iterated Fourier-Laplace formula. -/
lemma section43_iteratedSlice_descendedPairing
    (n : ℕ) :
    ... := by
  ...

Exact current-code milestone:
- the full slice-descent theorem is now formalized as
  `section43_iteratedSlice_descendedPairing`;
- the older theorem `section43_iteratedSlice_descendedPairing_imagAxis`
  remains as the first explicit one-variable fragment inside that proof;
- the reusable one-variable interchange step is now formalized privately as
  `one_variable_time_interchange_for_wightman_pairing`, together with the
  kernel-reduction chain down to an ambient upper-half-plane witness, in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- `OSToWightmanPositivity.lean` is now `sorry`-free, and
  `bvt_W_positive` in
  [OSToWightmanBoundaryValues.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean)
  is now closed by
  `OSReconstruction.bvt_W_positive_of_component_dense_preimage`;
- the slice-side vanishing package is now available on both pairing
  orientations, including
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
  and
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`;
- the flattened spectral / one-sided-support package is now closed in
  `OSToWightmanBoundaryValueLimits.lean`, culminating in
  `bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened`;
- the next exact analytic blocker is therefore the witness-consuming seam
  itself: the ambient witness has been canonicalized as an explicit
  `fourierLaplaceExt` of the real-time Wightman pairing functional, so the
  remaining content is the positive-imaginary-axis identification with the
  semigroup-side holomorphic matrix element (spectral Laplace comparison),
  together with the canonical-shell limit theorem;
- the Section-4.3 adapter `lemma42_matrix_element_time_interchange` and the
  kernel-level theorem `bvt_W_matrixElement_onImage` remain the immediate
  public consumers of that witness, not the direct successor of slice descent;
- `lemma42_matrix_element_time_interchange` is now present in production on
  the honest witness-consuming surface, so the remaining blocker is not a
  missing reduction theorem but the actual proof of the witness-identification
  and canonical-shell limit hypotheses it assumes.

/-- Concrete Section-4.3 version of the Lemma-4.2 interchange step. This is
now implemented on the honest current surface: it consumes an upper-half-plane
witness together with the positive-imaginary-axis OS identification and the
canonical-shell limit theorem. The remaining analytic content is to prove those
hypotheses, not to add another theorem layer. -/
lemma lemma42_matrix_element_time_interchange
    (n : ℕ) :
    ... := by
  -- implemented in `OSToWightmanPositivity.lean`

/-- Stage-5 prerequisite: the OS-II `bvt_W` kernel on transformed-image inputs,
written in the same iterated coordinates as the previous lemma. -/
lemma bvt_W_matrixElement_onImage
    (n : ℕ) :
    ... := by
  ...
```

This transcript matters because it tells the later implementation exactly where
the real analytic work belongs: in the one-variable transform, not in a fake
many-variable theorem. It also makes explicit the final hidden bridge that the
blueprint previously left implicit: Eq. `(4.28)` is not reached directly from
injectivity/well-definedness alone, but through these two transformed-image
pairing lemmas.

### 7.3. Lemma 4.2 unpacked

Lemma 4.2 proves continuity of `w`, which is exactly what lets the positivity
map extend to all Wightman test sequences.

The proof starts from the OS scalar product `(4.22)` and then rewrites it by:

1. inserting the difference-variable Fourier-Laplace formula `(4.13)`,
2. inserting the transformed test data `(4.26)`,
3. changing the order of integration to obtain `(4.24)`,
4. recognizing the resulting expression as a continuous Wightman-space pairing.

The only potentially deceptive point is step 3. It is not a trivial Fubini
application:
- in the spatial variables it is standard tempered-distribution Fourier
  transform bookkeeping,
- in the time variables it uses the Section 8 Laplace/Fourier interchange
  result.

So if one later formalizes Section 4.3 faithfully, the proof inventory must
include a dedicated "time-variable interchange of Laplace/Fourier integration
against the Wightman distribution" lemma.

### 7.3.1. Exact theorem shape of the time-variable interchange lemma

The paper text after `(4.24)` is explicit:

- the spatial-variable interchange is justified by the ordinary definition of
  Fourier transform of a tempered distribution;
- the time-variable interchange `ζ⁰ <-> q⁰` is justified by Lemma 8.4.

**Paper citation:** OS I p. 96, immediately after `(4.23)`:

> "Interchanging the order of integration in (4.23) we obtain (4.24) ... For
> the space components ξ_k^{1,2,3} and q_k^{1,2,3} the change in the order of
> integration is justified by the definition of the Fourier transform of a
> distribution. For the time components ξ_k^0 and q_k^0 we refer to Lemma 8.4."

So the hidden theorem used in Lemma 4.2 is not a generic "swap some
integrals" statement. It is a one-variable positive-support
Fourier/Laplace-distribution theorem in the precise form needed to pass from
`(4.23)` to `(4.24)`.

In implementation-oriented form, the theorem slot should look like:

```lean
/-- OS I Lemma 4.2 hidden step: interchange the time-variable Laplace/Fourier
integration against the Wightman difference-variable distribution. -/
theorem time_variable_laplace_fourier_interchange
    (P : TemperedDistribution timeDifferenceSpace)
    (f_left : Section43SchwartzImageTest n)
    (f_right : Section43SchwartzImageTest m) :
    timeLaplaceIntegrate
        (fun ζ0 =>
          timeFourierIntegrate
            (fun q0 => kernelFromDifferenceDistribution P ζ0 q0
              * transformedLeftTest f_left q0
              * transformedRightTest f_right q0))
      =
    timeFourierIntegrate
        (fun q0 =>
          timeLaplaceIntegrate
            (fun ζ0 => kernelFromDifferenceDistribution P ζ0 q0
              * transformedLeftTest f_left q0
              * transformedRightTest f_right q0)) := by
  -- this is the one-variable lemma cited as OS I Lemma 8.4
```

Every symbol in that pseudocode corresponds to a mathematical ingredient that
must be fixed before Lean implementation:

1. the exact one distinguished time variable on the left block,
2. the exact one distinguished time variable on the right block,
3. the difference-variable tempered distribution `P_{n+m-1}^+`,
4. the positive-energy transformed tests coming from `(4.19)` and `(4.26)`,
5. the integrability / distribution-pairing hypotheses that make the
   interchange legal.

This is the theorem slot in OS I that is mathematically closest to the current
theorem-3 `E -> R` frontier: both are one-variable analytic/boundary bridges,
not generic many-variable contour arguments.

### 7.4. Final quadratic-form identity `(4.28)`

The end of the positivity proof is formula `(4.28)`. This is where the abstract
construction pays off:

- the left-hand side is the Wightman quadratic form from the reconstruction
  theorem,
- the right-hand side is the Hilbert norm of the vector `u(f)`.

The key point is that the OS paper proves this *after* continuity of `u`, not
before. Thus the mathematically honest theorem surface is:

`WightmanQuadraticForm(f) = ‖u(f)‖^2`.

That is why theorem surfaces of the form

`OSInnerProduct = WightmanInnerProduct`

are category-confused: the paper compares the Wightman form with the Hilbert
norm of the transported vector, not with the raw Euclidean sesquilinear form on
the same literal test object.

For Lean implementation, `(4.28)` should be decomposed into the following exact
substeps:

1. define the transformed-image core `L_n` degreewise as the range of the
   Section-4.3 component transform;
2. define the finite-support transformed-image sequence space `L`;
3. choose Euclidean preimages of elements of `L`;
4. map those Euclidean preimages through the already-constructed OS quotient
   vector from Section 4.1;
5. prove preimage-independence using the injective half of Lemma 4.1;
6. expand the Wightman quadratic form degreewise;
7. rewrite each degreewise term by the corrected OS-II-backed Wightman kernel
   together with the Lemma-4.2 Fourier/Laplace interchange;
8. recognize the resulting sum as the Hilbert norm square of the transported
   vector.

The corresponding implementation theorem slots should therefore be:

```lean
lemma section43_transport_on_image
    (F : TransportImageSequence d) :
    OSHilbertSpace OS := by
  ...

lemma section43_transport_wellDefined
    (F : TransportImageSequence d) :
    ... := by
  ...

lemma section43_quadratic_identity_on_image
    (F : TransportImageSequence d) :
    WightmanInnerProduct reconstructedWightman F.1 F.1 =
      inner (section43_transport_on_image F)
        (section43_transport_on_image F) := by
  ...
```

Only after this diagonal identity is proved should the full public positivity
statement be recovered by density and continuity.

## 8. Section 4.4: Cluster

OS I transports cluster from the Euclidean side into the Hilbert-space / real
translation picture and then back to the Wightman side.

The important point for the current repo is that the cluster step is downstream
of the semigroup/Hilbert-space bridge. It is not the place where one should try
to solve the positive-time analytic continuation problem.

Theorem 3 on the current `E -> R` side is now closed, so theorem 4 should be
treated as a downstream consumer of that closed positivity/isometry package, not
as an independent route to repair theorem 3.

The internal proof shape is:
1. use the Euclidean cluster axiom on the OS side for spatially translated
   tests;
2. interpret the resulting pairings inside the same Hilbert-space framework
   used for reconstruction;
3. identify the limiting real-time/Wightman pairing only after the
   continuation-and-positivity bridge has already been established.

So cluster is a *consumer* of the isometry/positivity theorem, not a substitute
for it.

For the exact implementation ledger of the current theorem-4 frontier on
`main`, see `docs/theorem4_cluster_blueprint.md`.

### 8.1. Detailed proof chain of Section 4.4

The paper's displayed vector identity `(4.29)` is the whole proof in condensed
form. Unpacked, it is:

1. Rewrite the Euclidean cluster axiom as an OS Hilbert-space statement for the
   vectors `w(f)` and `w(g)`.
2. Use continuity of `w` and density of its range to extend the statement from
   the initial Euclidean test-sequence space to all Hilbert vectors.
3. Apply the extended statement to vectors of the form `u(h)` and `u(k)` from
   the positivity section.
4. Translate that vector statement back into the Wightman cluster statement.

So the logical dependency is linear:
- Section 4.4 depends on Section 4.3,
- not the other way around.

## 9. Section 4.5: Locality

Locality is obtained from symmetry plus analytic continuation, in the order OS
uses it:
- E3 and the earlier Fourier-Laplace/Lorentz-covariance equations produce a
  symmetric selected analytic continuation on the permuted forward-tube union;
- the Bargmann-Hall-Wightman theorem enlarges that continuation to the
  complex-Lorentz saturation;
- the cited Jost boundary theorem gives locality of the Wightman boundary
  distributions.

For the modern formalization this remains a good guide:
- locality lives on the analytic continuation and permutation side;
- it is not a semigroup positivity theorem.

This supports the current project discipline that theorem 2 belongs to the BHW /
Jost / PET / permutation package, not to the theorem-3 positivity lane.  It
also fixes the blueprint discipline: theorem-2 proof docs should follow OS I
§4.5 closely, with external BHW/Jost theorems isolated as external analytic
inputs rather than replaced by unrelated Lean-convenience routes.

The proof package can be restated more concretely:
1. use Euclidean symmetry to compare Schwinger functions on permuted real
   domains;
2. continue both sides to overlapping tube domains;
3. invoke uniqueness / edge-of-the-wedge style reasoning to identify the two
   analytic continuations;
4. take boundary values to get locality of the Wightman distributions.

Lean-facing correction: this is a **branch-difference** argument.  OS §4.5 does
not identify the value of one Euclidean Wick branch at `iτ` with the value of
the corresponding Wightman boundary branch at real time `τ`.  The safe formal
shape is:
- form the adjacent difference of two permuted analytic branches;
- use E3 to show this difference has zero Euclidean/Wick edge distribution;
- use EOW/BHW uniqueness to continue the same difference to the real Jost edge;
- conclude the real-edge adjacent difference vanishes.

Any theorem surface equating a single Wick value with a single real-time
`extendF` value on the same real configuration should be treated as a category
error unless an explicit paper bridge proves exactly that statement.

Implementation detail for the local EOW bridge: it is not enough for the SCV
theorem to return agreement on the two open tube sides.  The OS §4.5
branch-difference consumer needs the value on the real Jost edge itself, so the
local EOW strengthening must also export
`F(realEmbed y) = bv y`, and the chart-data packet must identify
`bv y` with the `extendF` real-edge branch difference.  This is still a boundary
limit statement at the real edge, not a same-shell Wick-to-real equality.

This is why locality should not be mixed into theorem 3:
- theorem 3 is about positivity/isometry through the semigroup bridge;
- theorem 2 is about permutation symmetry plus analytic continuation.

For the exact implementation ledger of the current theorem-2 frontier on
`main`, see `docs/theorem2_locality_blueprint.md`.

### 9.1. Detailed proof chain of Section 4.5

The locality proof uses three layers of analytic continuation:

1. On real noncoincident points, define the Wightman function from the
   supported momentum-space distribution.
2. Use Euclidean symmetry plus the already-built Fourier-Laplace continuation
   to analytically continue to the permuted-tube union `S_n'`.
3. Use the Bargmann-Hall-Wightman theorem to enlarge the domain to the
   `L_+(\C)`-saturation `S_n''`.
4. Invoke the cited several-complex-variable theorem from the Wightman book to
   convert that symmetric analytic continuation into locality of the boundary
   distributions.

Source-boundary update after the local Hall-Wightman and Streater-Wightman
audits:

1. Hall-Wightman and Streater-Wightman Theorem 2-11 justify the BHW analytic
   continuation step: Lorentz-covariant holomorphic tube functions continue
   single-valuedly to the extended tube.
2. Streater-Wightman's adjacent permuted-tube paragraph and Figure 2-4 justify
   only the local common-real-environment geometry for one adjacent
   transposition.
3. Neither source directly proves the fixed-`w` finite adjacent active-gallery
   theorem currently used as the Lean-facing Slot-6 target. That theorem must
   be treated as a derived chamber-stratification obligation, not as a direct
   citation.
4. Jost p. 83, second theorem, has been identified in the local image PDF as
   the theorem OS I cites after the BHW step: Wightman-function properties
   except locality, together with symmetry, imply locality. This supports the
   Slot-10 boundary theorem surface after the symmetric `S''_n` continuation
   has been supplied.

This matters because it shows exactly where the heavy analytic input sits:
- not in the semigroup package,
- but in the permutation-domain continuation and boundary-value uniqueness.

## 10. Section 5: `R -> E`

The reverse direction is conceptually cleaner:
- start from Wightman analyticity in the forward/permuted tube;
- evaluate at Euclidean points;
- verify Euclidean invariance, symmetry, positivity, cluster.

The precise lesson for Lean is that the Euclidean Schwinger functions are
obtained by restriction of the common holomorphic object at Wick-rotated
points. They are not introduced by an abstract algebraic recipe unrelated to
that analytic object.

More explicitly, the reverse direction has the following structure:
1. start from Wightman distributions satisfying the spectral condition and
   covariance;
2. use the Bargmann-Hall-Wightman theorem to obtain a holomorphic function on
   the forward/permuted tube;
3. evaluate that function on Wick-rotated Euclidean points;
4. prove Euclidean invariance and symmetry by transporting the corresponding
   Minkowski properties through the common holomorphic object;
5. prove reflection positivity and cluster by tracing those Euclidean values
   back to the positive-energy Hilbert-space representation.

So the trusted `R -> E` route always flows through a common holomorphic object.
This is exactly why false theorem surfaces of the form "Euclidean pairing
equals Wightman pairing on the same test expression" are off-paper.

This is why the repo's `R -> E` side should continue to center
`IsWickRotationPair`, `constructSchwingerFunctions`, and the BHW extension
lane, rather than inventing Euclidean surfaces detached from the analytic
continuation.

For the exact implementation ledger of the current reverse-direction theorem
surface on `main`, see `docs/r_to_e_blueprint.md`.

### 10.1. Detailed proof chain for `E0`

The hardest part of `R -> E` in OS I is not positivity or cluster; it is the
distribution estimate proving `E0`.

The structure is:

1. Define `S_n` on Euclidean points by restriction of the holomorphic Wightman
   function.
2. For compactly supported off-diagonal tests, define `S_n(f)` by ordinary
   Riemann integration.
3. Prove Proposition 5.1: this Riemann integral satisfies a Schwartz seminorm
   bound uniform in `f`.
4. Extend by density from compactly supported off-diagonal tests to the full
   off-diagonal Schwartz space.

So the true technical center of Section 5 is Proposition 5.1, not the Wick
restriction itself.

### 10.2. Proposition 5.1 in full structure

The proof is a finite-direction decomposition argument.

Geometric half:
1. Lemma 5.2 chooses finitely many unit vectors `e_k` so that every
   noncoincident Euclidean configuration has one direction in which all ordered
   successive gaps have positive projection.
2. Those directions and permutations define the open cover `Ω_{k,π}`.
3. A smooth partition of unity `χ_{k,π}` subordinate to that cover is built
   from a one-variable cutoff `τ`.

Analytic half:
4. On each piece `χ_{k,π} f`, rotate `e_k` to the time axis by an `SO_4`
   element.
5. After rotation and permutation, the support lies in the time-ordered region
   `Ω_<`.
6. Lemma 5.3 proves that restriction to `Ω_<` defines a distribution.
7. Lemma 5.4 shows that multiplying by `χ_{k,π}` does not lose Schwartz control
   beyond a bounded seminorm inflation.
8. Summing over finitely many `(k,π)` gives the global bound.

So Proposition 5.1 is a controlled reduction of arbitrary noncoincident
Euclidean configurations to the time-ordered region where the Wightman
holomorphic restriction is already understood.

### 10.2.1. Lemma 5.2 in proof-transcript form

Lemma 5.2 is the geometric engine of Proposition 5.1.

Its proof is:

1. For each ordered pair `(i,j)` define the unit direction
   `f_{ij} = (x_i - x_j)/|x_i - x_j|`.
2. In the 4-dimensional paper, choose finitely many unit vectors
   `e_1, ..., e_N` in `R^4` such that any four of them span `R^4`.
3. For the repo's general-`d` implementation, read this as the
   `R^(d+1)` analogue: choose finitely many unit vectors so that any
   `d + 1` of them span `R^(d+1)`.
4. Observe that a fixed `f_{ij}` can be orthogonal to at most three of the
   `e_k` in the paper case, or at most `d` of them in general dimension.
5. Therefore, for every finite tuple of unit directions `{f_{ij}}`, at least
   one `e_k` has nonzero pairing with each of them.
6. Compactness of the product of spheres upgrades this qualitative statement to
   a uniform lower bound `A > 0`.
6. That lower bound implies each configuration belongs to one of the finitely
   many open sets `Ω_{k,π}` after possibly reordering the points by a
   permutation `π`.

So the lemma is a compactness-plus-finite-direction argument, not an analytic
continuation argument.

### 10.2.2. Lemma 5.3 in proof-transcript form

Lemma 5.3 proves that the restriction to the time-ordered region already
defines a distribution.

The proof runs as follows:

1. Rewrite a time-ordered Euclidean configuration in difference variables
   `ξ_i = x_{i+1} - x_i` with positive time component.
2. Use the Fourier-Laplace formula for the Wightman distribution in those
   difference variables.
3. Reduce the problem by the nuclear theorem to the one-variable statement:
   if `W(q)` is supported in `[0,∞)` then
   `S(ξ) = W(e^{-ξ q})` defines a distribution on `(0,∞)`.
4. Estimate `S(ξ)` by polynomial growth in `ξ^{-1}` from the positive-support
   distribution estimate.
5. Write any test function vanishing to all orders at `0` as
   `f(x) = x^n f^{(n)}(y_x)/n!`.
6. Insert that representation into the integral and choose `n` large enough to
   absorb the singular power of `ξ^{-1}`.
7. Conclude continuity in the required Schwartz seminorm.

So the key hidden move is the high-order vanishing of the off-diagonal test
space at the boundary.

### 10.2.3. Lemma 5.4 in proof-transcript form

Lemma 5.4 says multiplying by the partition-of-unity functions `χ_{k,π}` does
not destroy Schwartz control.

The proof is:

1. Differentiate the explicit product formula for `χ_{k,π}`.
2. Use the chain rule and the compact support of `τ'` to bound derivatives by
   polynomial factors in the reciprocal distance function `ρ(x)^{-1}`.
3. Use the geometric estimate from Lemma 5.2 to bound those reciprocal
   distance factors uniformly on the support.
4. Conclude that every derivative of `χ_{k,π} f` is controlled by a finite
   Schwartz seminorm of `f`.

So Lemma 5.4 is a cutoff-regularity estimate, not a property of the Wightman
function itself.

### 10.2.4. Exact theorem-slot inventory behind Proposition 5.1

To keep the future Lean port of OS I Section 5 from collapsing back into prose,
the proof of Proposition 5.1 should be read as requiring the following exact
theorem slots.

Geometric slots:

1. a finite-direction lemma

```lean
theorem finite_direction_cover_noncoincident_configs
    (n : ℕ) :
    ∃ (N : ℕ) (e : Fin N → EuclideanUnitVector 4) (A : ℝ),
      0 < A ∧
      ∀ x ∈ noncoincidentEuclideanConfig n,
        ∃ k : Fin N, ∃ π : Equiv.Perm (Fin n),
          orderedGapProjectionLowerBound e k π x A := by
  -- this is Lemma 5.2
```

2. a partition-of-unity package subordinate to the open cover

```lean
theorem smooth_partition_of_unity_on_direction_cover
    (hcover : FiniteDirectionCover n) :
    ∃ χ : CoverIndex hcover → SchwartzCutoffOnConfig n,
      subordinateTo χ hcover.openSets ∧
      locallyFinite χ ∧
      partitionOfUnity χ := by
  -- built from the one-variable cutoff `τ`
```

Analytic slots:

3. a distribution theorem on the time-ordered region

```lean
theorem ordered_region_wick_restriction_is_distribution
    (W : WightmanData d)
    (n : ℕ) :
    ContinuousLinearMap
      (OrderedRegionOffDiagonalTests d n)
      ℂ := by
  -- this is Lemma 5.3
```

4. a cutoff-seminorm control theorem

```lean
theorem partition_cutoff_schwartz_bound
    (hcover : FiniteDirectionCover n)
    (χ : CoverIndex hcover → SchwartzCutoffOnConfig n) :
    ∀ i, ∃ C m,
      ∀ f,
        seminorm i (χ i * f) ≤ C * finiteSumOfSeminormsUpTo m f := by
  -- this is Lemma 5.4
```

5. a final summation theorem combining the geometric and analytic halves

```lean
theorem wick_restriction_satisfies_global_schwartz_bound
    (W : WightmanData d)
    (n : ℕ) :
    ∃ C m,
      ∀ f : OffDiagonalSchwartzTest d n,
        ‖wickRestrictionFunctional W n f‖ ≤ C * finiteSumOfSeminormsUpTo m f := by
  -- finite decomposition into `χ_{k,π} f`,
  -- estimate each term on the ordered region,
  -- sum over finitely many cover pieces
```

Those theorem slots are the actual mathematical backbone of `R -> E` in OS I.
Without them, Proposition 5.1 would still be only "understood globally" rather
than documented in a way that makes later implementation mechanical.

The final summation theorem itself should also be decomposed explicitly, because
otherwise the later Lean port still has to reconstruct the last assembly step
from prose. The proof transcript should be:

1. use the finite-direction cover to write
   `f = Σ_{i} χ_i f` on the noncoincident configuration space;
2. apply `ordered_region_wick_restriction_is_distribution` to each `χ_i f`
   after transporting it to the relevant ordered chart;
3. use `partition_cutoff_schwartz_bound` to bound each `χ_i f` by finitely many
   seminorms of `f`;
4. sum those finitely many bounds over the cover index;
5. absorb the finite sum into one global constant and one maximal seminorm
   order.

Implementation-level theorem slots for that last assembly:

```lean
lemma partition_recombines_off_diagonal_test
    (hcover : FiniteDirectionCover n)
    (χ : CoverIndex hcover → SchwartzCutoffOnConfig n)
    (f : OffDiagonalSchwartzTest d n) :
    f = ∑ i, χ i * f := by
  -- partition of unity on the noncoincident locus

lemma finite_sum_of_local_schwartz_bounds_is_global_bound
    (hcover : FiniteDirectionCover n)
    (hlocal :
      ∀ i, ∃ C_i m_i,
        ∀ f, ‖localTerm i f‖ ≤ C_i * finiteSumOfSeminormsUpTo m_i f) :
    ∃ C m,
      ∀ f, ‖∑ i, localTerm i f‖ ≤ C * finiteSumOfSeminormsUpTo m f := by
  -- take `m = max_i m_i`, `C = Σ_i C_i`, compare each local seminorm bound to
  -- the maximal one, then sum
```

These two lemmas are mathematically routine, but documenting them matters: they
are the exact point where Proposition 5.1 stops being a cover of local facts
and becomes one global Schwartz-bound theorem.

### 10.3. Why positivity and cluster in `R -> E` are easy only after Section 4

At the end of Section 5 the paper says positivity and cluster follow "by the
arguments of Sections 4.3 and 4.4". Concretely that means:

- positivity reuses the Section 4.3 map from Wightman test data to OS Hilbert
  vectors and the quadratic-form identity,
- cluster reuses the Section 4.4 vector identity and density argument.

So even the cleaner `R -> E` direction is not independent of the Section 4
Hilbert-space transport package.

### 10.3.1. Exact positivity reuse in Section 5

When the paper says positivity follows from the Section 4.3 argument, the
actual content is:

1. The Euclidean functions constructed by Wick restriction enter the same OS
   Hilbert-space construction as before.
2. The transformed Wightman test data define the same vectors `u(f)` as in the
   forward direction.
3. The quadratic-form identity `(4.28)` still holds because it only uses the
   common holomorphic object and the positive-support transform.
4. Therefore the Euclidean functions satisfy reflection positivity.

So the reverse direction is not proving a new positivity theorem. It is
reusing the already-identified common object.

### 10.3.2. Exact cluster reuse in Section 5

Similarly, when cluster is imported from Section 4.4, the content is:

1. The Euclidean cluster axiom is rewritten as the same vector limit as before.
2. The vectors are those coming from the same Hilbert-space transport map.
3. The argument uses no new analytic continuation; it only reuses the already
   established vector identity and density.

Thus the reverse-direction cluster proof is conceptually trivial only because
the Hilbert-space bridge is already built.

### 10.3.3. Exact theorem-slot inventory for Section 4.4 reuse

The reverse-direction cluster step should now be recorded as an explicit
four-layer transport package rather than a slogan.

```lean
lemma euclidean_cluster_on_positive_core
    (F G : PositiveTimeEuclideanData) :
    Tendsto
      (fun a => osPairingTranslated F G a)
      spatialInfinity
      (nhds (osPairing F unit * osPairing unit G)) := by
  -- the Euclidean cluster axiom on the positive-time core

lemma euclidean_cluster_rewritten_as_hilbert_vector_limit
    (F G : PositiveTimeEuclideanData) :
    Tendsto
      (fun a => inner (u F) (translateVector a (u G)))
      spatialInfinity
      (nhds (inner (u F) Ω * inner Ω (u G))) := by
  -- rewrite the Euclidean cluster axiom in the Hilbert-space model

lemma hilbert_vector_cluster_to_wightman_cluster_on_core
    (F G : PositiveTimeMinkowskiData) :
    Tendsto
      (fun a => WightmanPairingTranslated F G a)
      spatialInfinity
      (nhds (WightmanPairing F unit * WightmanPairing unit G)) := by
  -- use the Section 4.3 pairing identity on the core and rewrite back into
  -- Wightman language

lemma wightman_cluster_extended_by_density
    (F G : BorchersSequence d) :
    Tendsto
      (fun a => WightmanPairingTranslated F G a)
      spatialInfinity
      (nhds (WightmanPairing F unit * WightmanPairing unit G)) := by
  -- extend the core theorem by the same continuity/density package used in
  -- Section 4.3
```

So Section 4.4 is not just "cluster after positivity." It is:

1. Euclidean cluster on a positive-time core,
2. Hilbert-space rewriting,
3. Wightman rewriting on the same core,
4. density/continuity extension.

## 11. Section 8: Technical Lemmas and the Failure Point

### 11.1. Lemmas 8.5-8.7

These are the sound one-variable complex-analysis bridge:
- CR distribution on the half-plane;
- holomorphic function on the right half-plane;
- Fourier-Laplace transform of a positive-support distribution.

These are conceptually robust and remain part of the correct story.

### 11.2. Lemma 8.8

This is the bad step.

It tries to conclude a joint many-variable Laplace transform statement from
separate one-variable statements. OS II later gives the explicit counterexample
`exp(-xy)`.

So the correct formalization rule is:
- never infer full many-gap continuation merely from separate one-gap
  continuation unless the OS II induction or an equivalent modern theorem has
  been made explicit.

This remains one of the most important route-discipline constraints in the
project.

The important nuance is that Lemmas 8.5-8.7 remain useful while 8.8 fails.
That means the right reaction is not:
- "throw away the OS I complex-analysis lane entirely."

It is:
- keep the one-variable Fourier-Laplace machinery,
- replace only the unjustified many-variable upgrade.

But another nuance must stay explicit: OS I Section 4.3 uses `\tilde W` from
Eq. `(4.12)`, so in the original paper its positivity proof is not independent
of Lemma 8.8. The modern project route is safe only because production replaces
that dependence by the OS II repaired analytic-continuation package.

This distinction is exactly what OS II does, and the Lean documentation should
keep that distinction visible.

### 11.3. What Section 8 means for the current theorem-3 frontier

The current theorem-3 work in `OSToWightmanBoundaryValues` is a one-gap
positivity/isometry problem with parameters. Because of that:

- Section 8.8 warns against any attempt to prove theorem 3 by saying
  "we know the two relevant objects separately in each time variable, hence they
  define the same many-variable boundary value";
- Sections 8.5-8.7 do support one-variable half-plane / boundary-value
  arguments, provided the correct scalar continuation object has already been
  isolated.

So the correct use of OS I on theorem 3 is narrow and disciplined:
- use it for the one-variable semigroup and boundary-value theorem shape;
- do not use it as a license for a generic several-variable uniqueness step.

## 12. Formalization Consequences

1. The semigroup/Hilbert-space route in `OSToWightmanSemigroup.lean` is
   mathematically canonical and should stay central.
2. The live `k = 2` / theorem-3 frontier should be read as a one-gap
   parameter-packaging problem, not as a place to force a generic many-variable
   continuation theorem.
3. Same-test-function Euclidean/Minkowski equalities are not OS I.
4. Theorem 2 (locality) and theorem 3 (positivity) belong to different
   mathematical packages in the paper and should stay separated in Lean.
5. Any attempt to close a live blocker by "separate analyticity in each
   variable, therefore joint continuation" is immediately suspect unless it is
   backed by the explicit OS II machinery.
6. On the `R -> E` side, any theorem surface asserting direct equality of the
   OS pairing and Wightman pairing before going through the common holomorphic
   object should be treated as suspect until justified line by line.

## 13. Recommended Use of This Note

When working on the Lean frontier:
- use OS I for the semigroup matrix-element theorem shape;
- use OS II for the corrected many-variable continuation and temperedness
  estimates;
- if a proposed theorem surface does not look like either
  `(one-gap parameterized semigroup object)` or
  `(OS II inductive continuation / VI.1 estimate)`,
  stop and document the missing paper bridge before treating it as a viable
  theorem target.

## Appendix A. Lean-Pseudocode Skeletons for OS I

This appendix records the proof shapes from OS I in a later-implementation
format. The statements are not intended to compile directly; they are
mathematical scaffolds for future Lean theorems.

### A.1. OS Hilbert space and semigroup

```lean
/-- The OS sesquilinear form on positive-time test sequences. -/
def osForm (f g : PosTimeTestSeq) : ℂ :=
  -- double sum over left/right arities of the reflected Schwinger pairings
  -- `Σ_{n,m} S_{n+m}(Θ f_n^* × g_m)` on the positive-time Borchers algebra
  reflectedSchwingerPairing f g

theorem osForm_nonneg
    (hE2 : ReflectionPositivity) :
    0 ≤ (osForm f f).re := by
  -- direct use of the OS axiom

def OSHilbertSpace : Type := QuotientCompletion (nullSpace osForm)

def timeShiftContraction (t : ℝ) (ht : 0 ≤ t) :
    OSHilbertSpace →L[ℂ] OSHilbertSpace :=
  -- descend positive-time translation on representatives to the quotient,
  -- then complete continuously
  quotientLiftOfPositiveTimeTranslation t ht

theorem timeShiftContraction_norm_le_one
    (t : ℝ) (ht : 0 ≤ t) :
    ‖timeShiftContraction t ht‖ ≤ 1 := by
  -- repeated Cauchy-Schwarz + the iterative estimate around OS I (4.7)-(4.9)
```

This is the exact paper place where positivity, Euclidean covariance, and the
quotient construction meet. It should remain a separate proof stage in Lean.

Explicit theorem-slot inventory for A.1:

```lean
lemma reflected_schwinger_pairing_is_hermitian
    (f g : PosTimeTestSeq) :
    star (osForm f g) = osForm g f := by
  -- time reflection + conjugate symmetry of the Schwinger functions

lemma positive_time_translation_preserves_null_space
    (t : ℝ) (ht : 0 ≤ t) :
    MapsTo (positiveTimeTranslate t ht) (nullSpace osForm) (nullSpace osForm) := by
  -- covariance + positivity estimate on the OS form

lemma quotient_translation_is_contractive
    (t : ℝ) (ht : 0 ≤ t) :
    ‖quotientPositiveTimeTranslate t ht‖ ≤ 1 := by
  -- this is the quotient-level content of `(4.6)`-`(4.9)`

lemma contraction_semigroup_has_positive_generator :
    ∃ H : PositiveSelfAdjointOperator OSHilbertSpace,
      ∀ t ≥ 0, timeShiftContraction t ‹0 ≤ t› = expSemigroup (-t * H) := by
  -- standard contraction-semigroup theorem after the OS-space construction
```

So A.1 should later materialize as four separate stages:
1. Hermitian OS form,
2. quotient compatibility,
3. contraction estimate,
4. generator extraction.

### A.2. One-variable semigroup matrix element

```lean
/-- OS I (4.10)-(4.11): package one distinguished time gap as a semigroup
matrix element. -/
theorem one_gap_semigroup_matrix_element
    (left right : PosTimeTestData)
    (hparams : PackedRemainingVariables) :
    ∃ F : ℂ → ℂ,
      IsHolomorphicOn F rightHalfPlane ∧
      ∀ t > 0, F t = inner (psi left) (expSemigroup (-t * H) (psi right)) := by
  -- build from the OS semigroup and packaged parameters
```

This is the primary OS I theorem shape the current `k = 2` route should imitate.

Explicit theorem-slot inventory for A.2:

```lean
lemma packaged_parameters_define_hilbert_vectors
    (left right : PosTimeTestData)
    (hparams : PackedRemainingVariables) :
    ∃ ψL ψR : OSHilbertSpace,
      packagedAsHilbertVectors left right hparams ψL ψR := by
  -- package all nondistinguished variables into two OS vectors

lemma semigroup_matrix_element_is_holomorphic
    (ψL ψR : OSHilbertSpace) :
    IsHolomorphicOn
      (fun z : ℂ => inner ψL (expSemigroup (-z * H) ψR))
      rightHalfPlane := by
  -- standard semigroup holomorphy in the right half-plane

lemma semigroup_matrix_element_matches_real_gap
    (left right : PosTimeTestData)
    (hparams : PackedRemainingVariables)
    (t : ℝ) (ht : 0 < t) :
    oneGapScalar left right hparams t =
      inner (psi left) (expSemigroup (-t * H) (psi right)) := by
  -- identify the real positive-time gap with the semigroup parameter
```

So the one-gap theorem is really:
1. package parameters into vectors,
2. prove holomorphy of the semigroup matrix element,
3. identify its real positive-time boundary values with the target scalar.

### A.3. Positivity transfer

```lean
/-- OS I Section 4.3: reconstructed Wightman positivity from the common
Hilbert-space object. -/
theorem reconstructed_wightman_positive
    (F : BorchersSequence d) :
    0 ≤ (WightmanInnerProduct reconstructedWightman F F).re := by
  -- 1. map Minkowski test data to a dense family in OSHilbertSpace
  -- 2. identify the Wightman pairing with the Hilbert norm
  -- 3. conclude from nonnegativity of `‖u(F)‖^2`
```

Hidden local lemmas suggested by OS I Section 4.3:

```lean
lemma minkowski_test_to_hilbert_vector_dense :
    DenseRange u := by
  -- combine:
  -- 1. density of the image of `f_n ↦ \tilde f_n` from Lemma 4.1,
  -- 2. density of the quotient map image used in Section 4.1,
  -- 3. passage from the dense algebraic image to the completed Hilbert space

lemma wightman_inner_eq_hilbert_inner
    (F G : BorchersSequence d) :
    WightmanInnerProduct reconstructedWightman F G =
      inner (u F) (u G) := by
  -- first prove the diagonal identity
  -- `WightmanInnerProduct ... F F = inner (u F) (u F)`,
  -- then obtain the full sesquilinear identity by polarization,
  -- and finally extend from the initial dense subspace by continuity
```

The second lemma is the honest positivity bridge. It is strictly stronger and
more faithful than any theorem of the form

`OSInnerProduct F G = WightmanInnerProduct F G`.

Explicit theorem-slot inventory for A.3:

```lean
lemma inverse_laplace_fourier_transform_dense
    :
    DenseRange minkowskiToPositiveTimeEuclideanData := by
  -- this is the dense-range content of Lemma 4.1

lemma positivity_transport_map_continuous
    :
    Continuous u := by
  -- this is the continuity content of Lemma 4.2

lemma wightman_quadratic_form_eq_vector_norm_sq
    (F : BorchersSequence d) :
    WightmanInnerProduct reconstructedWightman F F =
      inner (u F) (u F) := by
  -- this is the diagonal specialization of `(4.28)`

lemma wightman_sesquilinear_form_eq_hilbert_inner
    (F G : BorchersSequence d) :
    WightmanInnerProduct reconstructedWightman F G =
      inner (u F) (u G) := by
  -- derive from the diagonal theorem by polarization,
  -- then use continuity/density to pass to the completed space

lemma polarization_recovers_sesquilinear_form_from_quadratic_form
    {Q : BorchersSequence d → ℂ}
    (hQ :
      ∀ F,
        Q F =
          WightmanInnerProduct reconstructedWightman F F) :
    ∀ F G,
      WightmanInnerProduct reconstructedWightman F G =
        (1 / 4 : ℂ) *
          (Q (F + G) - Q (F - G)
            - Complex.I * Q (F + Complex.I • G)
            + Complex.I * Q (F - Complex.I • G)) := by
  -- polarization on the algebraic Borchers-sequence space

lemma hilbert_polarization_recovers_inner_from_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (u v : V) :
    inner u v =
      (1 / 4 : ℂ) *
        (inner (u + v) (u + v) - inner (u - v) (u - v)
          - Complex.I * inner (u + Complex.I • v) (u + Complex.I • v)
          + Complex.I * inner (u - Complex.I • v) (u - Complex.I • v)) := by
  -- Hilbert-space polarization identity

lemma dense_polarization_extension
    (hdiag :
      ∀ F,
        WightmanInnerProduct reconstructedWightman F F =
          inner (u F) (u F))
    (hdense : DenseRange u)
    (hcontW : Continuous (fun p : BorchersSequence d × BorchersSequence d =>
      WightmanInnerProduct reconstructedWightman p.1 p.2)) :
    ∀ F G,
      WightmanInnerProduct reconstructedWightman F G =
        inner (u F) (u G) := by
  -- apply the two polarization identities and use density/continuity

lemma positivity_of_vector_norm_sq
    (v : OSHilbertSpace) :
    0 ≤ (inner v v).re := by
  -- Hilbert-space positivity
```

So positivity transfer in OS I is not one theorem but a five-step bridge:
1. dense transform,
2. continuous transport map,
3. diagonal quadratic-form identity,
4. sesquilinear extension by polarization,
5. Hilbert-space positivity.

For the current `E -> R` frontier, this five-step bridge is exactly the final
public layer that still sits *after* the positive-time compact-shell theorem-3
work. In other words:

1. the theorem-3 boundary-value / `xiShift` route proves the positive-time
   comparison statements on the OS side;
2. the Section 4.3 transport package above is what upgrades those core
   comparison statements to the public theorem over arbitrary
   `F : BorchersSequence d`;
3. so any later Lean implementation that tries to close theorem 3 directly on
   arbitrary Borchers sequences without supplying this transport/density layer
   is skipping part of the actual OS I proof.

This is why `docs/theorem3_os_route_blueprint.md` now treats the final
general-sequence closure as an explicit Section 4.3 transport problem rather
than as a vague approximation step.

### A.4. Reverse `R -> E` construction

```lean
/-- OS I Section 5: Schwinger functions arise by Wick restriction of the common
holomorphic Wightman object. -/
theorem schwinger_from_wightman_by_wick_restriction
    (W : WightmanData d) :
    ∃ S : EuclideanData d,
      (∀ x, S x = commonHolomorphicObject W (wickRotate x)) ∧
      EuclideanAxioms S := by
  -- 1. obtain the BHW holomorphic extension
  -- 2. evaluate on Wick-rotated Euclidean points
  -- 3. transport invariance / positivity / cluster through the same object
```

This is the paper-faithful antidote to false `R -> E` theorem surfaces that try
to define Euclidean objects independently of the common holomorphic extension.

Explicit theorem-slot inventory for A.4:

```lean
lemma bhw_extension_exists_from_wightman_axioms
    (W : WightmanData d) :
    ∃ Fext, HolomorphicOnPermutedTube Fext := by
  -- forward/permuted-tube BHW extension

lemma wick_restriction_defines_euclidean_family
    (Fext : HolomorphicOnPermutedTubeData d) :
    ∃ S : EuclideanData d,
      ∀ x, S x = Fext (wickRotate x) := by
  -- define Euclidean functions by Wick restriction of the common object

lemma euclidean_invariance_from_minkowski_covariance
    (Fext : HolomorphicOnPermutedTubeData d)
    (S : EuclideanData d)
    (hwick : ∀ x, S x = Fext (wickRotate x)) :
    EuclideanInvariance S := by
  -- transport covariance through the common holomorphic object

lemma euclidean_symmetry_from_permuted_tube_extension
    (Fext : HolomorphicOnPermutedTubeData d)
    (S : EuclideanData d)
    (hwick : ∀ x, S x = Fext (wickRotate x)) :
    EuclideanSymmetry S := by
  -- transport permutation symmetry through the common object

lemma euclidean_reflection_positivity_from_section4_transport
    (W : WightmanData d)
    (S : EuclideanData d)
    (hwick : WickRestrictionBridge W S) :
    ReflectionPositivity S := by
  -- reuse the Section 4.3 positivity transport package

lemma euclidean_cluster_from_section4_transport
    (W : WightmanData d)
    (S : EuclideanData d)
    (hwick : WickRestrictionBridge W S) :
    ClusterProperty S := by
  -- reuse the Section 4.4 cluster argument through the same common object
```

So the reverse `R -> E` direction should later decompose into:
1. BHW extension,
2. Wick restriction,
3. Euclidean invariance,
4. Euclidean symmetry,
5. positivity reuse,
6. cluster reuse.

### A.5. Technical one-variable Fourier-Laplace bridge

```lean
/-- Safe part of OS I Section 8: one-variable boundary-value / Fourier-Laplace
bridge. -/
theorem one_variable_boundary_value_to_positive_support
    (F : ℂ → ℂ)
    (hhol : IsHolomorphicOn F rightHalfPlane)
    (hcr : BoundaryCRCondition F)
    (hgrowth : PolynomialGrowthOnVerticalLines F) :
    ∃ u : TemperedDistribution ℝ,
      support u ⊆ Set.Ici 0 ∧
      FourierLaplaceTransform u = F := by
  -- this is the safe OS I / Vladimirov half-plane theorem
```

This theorem shape is still trustworthy. What OS I Section 8 does *not* give is
its many-variable analogue without the OS II induction ladder.

The exact companion theorem slot needed by Lemma 4.2 is:

```lean
/-- One-variable Fourier/Laplace interchange against the reconstructed
difference-variable distribution. This is the OS I Lemma 8.4 input hidden
inside the proof of Lemma 4.2. -/
theorem one_variable_time_interchange_for_wightman_pairing
    (P : TemperedDistribution timeDifferenceSpace)
    (f g : PositiveEnergyTimeTests) :
    pair_after_laplace_then_fourier P f g =
      pair_after_fourier_then_laplace P f g := by
  -- prove the hypotheses of the one-variable positive-support theorem,
  -- then rewrite both sides as the same boundary-value distribution pairing
```

This theorem was not optional documentation frosting. It has now been
formalized privately in
[OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean),
which is why the live analytic blocker has moved one step further down to the
ambient Paley-Wiener witness construction.

Implementation note:

- in the current repo, this slot should be supplied through the already-built
  one-variable theorem `SCV.paley_wiener_one_step` (and ultimately
  `SCV.paley_wiener_half_line`), not by inventing a new many-variable
  continuation principle;
- but `SCV.paley_wiener_half_line` naturally produces the ambient witness on
  `SCV.upperHalfPlane`, since it is a Fourier/Laplace continuation theorem for
  a real-line tempered pairing; it does **not** directly output the final
  right-half-plane witness used by the semigroup-side `singleSplit` formulas;
- so the honest implementation order is:
  1. build the ambient upper-half-plane witness from the Wightman pairing;
  2. prove the positive-imaginary-axis shell identification;
  3. use those axis values directly in the current kernel reduction whenever
     possible;
  4. only if a whole-domain comparison of witnesses is needed, use
     `identity_theorem_upperHalfPlane` or an explicit rotation bridge to
     compare with any right-half-plane scalar trace;
- in the current repo, step 1 has already been reduced to the closed flattened
  spectral package ending at
  `bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened`
  in
  [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean);
- so the remaining live content is no longer the shell-specific paired-
  vanishing theorem, but the witness-consuming seam itself: the positive-
  imaginary-axis identification and the canonical-shell limit theorem for the
  actual ambient upper-half-plane witness;
- a tempting simplification must be rejected here: on the corrected ambient
  theorem surface, the canonical shell
  `xiShift(... wickRotate(y) ..., t * I)` is not pointwise a `ForwardTube`
  evaluation for arbitrary ambient `y`, so the remaining step is not a trivial
  interior continuity / dominated-convergence argument on the ambient shell;
- the remaining work in Lemma 4.2 is therefore the concrete Section-4.3
  packaging of that one-variable theorem into the matrix-element shell, not
  the construction of a new Section-8 theorem family from scratch.

The later Lean port should also keep a still more local theorem-slot name in
reserve, because OS I Lemma 4.2 does not use a fully abstract positive-support
theorem in isolation. It uses that theorem in the concrete matrix-element
setting of Section 4.3. The implementation-level theorem slot should therefore
be recorded as:

```lean
/-- Concrete Section 4.3 version of the Lemma 4.2 interchange step. -/
theorem lemma42_matrix_element_time_interchange
    (W : WightmanDifferenceData d)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f_left : PositiveEnergyWightmanTest n)
    (f_right : PositiveEnergyWightmanTest m)
    (hφ : quotientClass φ = section43_transform f_left)
    (hψ : quotientClass ψ = section43_transform f_right) :
    section43_pairing_before_time_interchange W φ ψ f_left f_right
      =
    section43_pairing_after_time_interchange W φ ψ f_left f_right := by
  -- reduce both sides to the one-variable positive-support theorem,
  -- then discharge the spatial Fourier bookkeeping separately
```

The point of naming both theorem slots is:

1. `one_variable_time_interchange_for_wightman_pairing` is the reusable
   analytic theorem;
2. `lemma42_matrix_element_time_interchange` is the exact Section 4.3 adapter
   that the positivity proof will actually call.
3. the purely configuration-space shell inside that adapter is already
   formalized by `conjTensorProduct_timeShift_eq_tailTimeShift` and
   `simpleTensor_timeShift_integral_eq_xiShift_conj` in
   [OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean), so the
   remaining live gap is the genuine time-variable interchange /
   boundary-value step rather than another shell-rewrite subproblem.

Without the second name, a future implementation would still have to rediscover
how the abstract one-variable theorem plugs into the concrete OS I formula
`(4.23) -> (4.24)`.

### A.6. Exact dependency DAG for later Lean work on OS I

The audit should also keep the implementation order explicit:

1. Section 4.1 Hilbert-space construction,
2. Section 4.2 one-gap semigroup theorem,
3. Section 4.3 positivity transport,
4. Section 4.4 cluster transport,
5. Section 5 reverse-direction Wick restriction,
6. Section 8 one-variable Fourier-Laplace bridge only as support input for
   Lemma 4.2 and Section 5.

The later Lean port should not invert that order. In particular:

1. Section 5 positivity must depend on Section 4.3,
2. Section 5 cluster must depend on Section 4.4,
3. Section 8 does not replace Sections 4.3/4.4; it only supplies the hidden
   analytic input for the one-gap interchange theorem.
