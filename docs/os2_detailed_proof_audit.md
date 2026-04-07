# OS II Detailed Proof Audit

Purpose: this note is a detailed proof-oriented reading of
`references/reconstruction theorem II.pdf`. It is written to serve as a
route-discipline document for the `E -> R` formalization and, in particular, for
the active one-gap / `k = 2` frontier. It aims to make explicit not only the
headline theorems but the hidden sublemmas, proof packaging, and chapter split
that the Lean development must respect.

This note assumes familiarity with the notation in:
- `docs/os1_detailed_proof_audit.md`
- `docs/os_reconstruction_reading_notes.md`
- `docs/openclaw_comprehensive_reading_note.md`

## 1. Executive Summary

OS II corrects exactly one part of OS I:
- not the semigroup construction,
- not the one-variable continuation,
- not the positivity mechanism,
- but the unjustified leap from separate one-variable continuation to a full
  many-variable Fourier-Laplace statement.

The corrected theorem shape is:

1. Build one-variable continuation objects from the OS semigroup.
2. Use Euclidean covariance plus local geometry to obtain local analyticity in
   all time variables.
3. Enlarge the domain inductively via the `(A_N)/(P_N)` ladder.
4. Only afterwards prove polynomial growth / temperedness estimates using the
   linear growth condition `E0'`.
5. Finally take tempered boundary values to recover Wightman distributions.

The most important discipline consequence is:
- Chapter V is continuation.
- Chapter VI is growth control.
- these must not be blurred.

## 2. Chapter I: What Was Wrong and What Is Being Fixed

OS II states plainly that OS I Lemma 8.8 is wrong. The counterexample
`F(x,y)=exp(-xy)` shows that being a Laplace transform in each variable
separately does not imply being a joint Laplace transform.

This has three direct consequences for formalization:

1. Separate one-variable holomorphicity is not enough.
2. The corrected proof must control the analytic domain explicitly.
3. Many-variable continuation must be built, not guessed.

The paper then offers two repaired Euclidean hypotheses:
- `Ě0`, a strong distribution condition restoring a quick equivalence theorem;
- `E0'`, the linear growth condition, which is closer to applications and is the
  real target of the paper.

## 3. Chapter II: New Test-Function Norms and Distribution Surfaces

OS II introduces the `|.|_p` and `|.|_{p,O}` norms and the space `S(O)` for open
sets `O`, together with a sharpened Whitney-extension statement.

The role of this chapter is not decorative. It feeds directly into:
- the strong condition `Ě0` in Chapter III,
- the comparison between distribution control on `R_+^{4n}` and tempered
  estimates after continuation,
- the constant-tracking needed in Chapter VI.

Two hidden facts matter:

1. Lemma 2.2 is a quantitative extension theorem with constants controlled by
   `gamma(n,p) = [c^2 (p+1)]^{2p+1}`.
2. Lemma 2.3 converts support-control plus `|.|_p` bounds into a distribution on
   the positive cone with explicit constant inflation.

These are part of why OS II can transport estimates carefully rather than only
qualitatively.

## 4. Chapter III: The Strong Equivalence Theorem

The strong condition `Ě0` says, morally, that the difference-variable Schwinger
functions already live on the Fourier-Laplace-friendly test-function side.

The proof structure is simple:
- under `Ě0`, the Fourier-Laplace transform to supported Wightman data is
  immediate;
- the reverse direction from Wightman data to `Ě0` is also straightforward.

This chapter is not the active route for the current Lean frontier, but it
clarifies a conceptual point:
- if one makes the Euclidean input strong enough, the hard continuation problem
  disappears;
- OS II deliberately avoids doing that in the main theorem because it is too
  strong for applications.

So when the Lean development uses a stronger theorem surface than OS II needs,
that should be understood as a convenience detour, not the paper route.

## 5. Chapter IV: The Real Main Theorem

`E0'` says the Euclidean Green's functions satisfy a linear growth estimate

`|S_n(f)| <= sigma_n |f|_{n s}`

with `sigma_n` of factorial growth.

The chapter then states the roadmap:
- Theorem 4.1 `(A_0)`: real analyticity.
- Theorem 4.2 `(A_r)` and `(TE_r)`: inductive continuation and matching bounds
  on larger domains.
- Theorem 4.3: full continuation on the product right half-plane with
  polynomial bounds.

The important strategic point is already visible here:
- continuation and bounds are proved together only at the statement level;
- in the proof, continuation is conceptually Chapter V and bounds are Chapter
  VI.

The end of Chapter IV also explains the extraction of Wightman distributions:
- Theorem 4.3 gives a holomorphic function on `C_+^k` with polynomial growth.
- Standard several-complex-variable Fourier-Laplace theory produces a tempered
  distribution supported in the forward cone.

So the real frontier is never "produce some holomorphic function." It is
"produce the specific OS II holomorphic function with the correct domain and
growth."

## 6. Chapter V Overview: Continuation Without `E0'`

OS II begins Chapter V by stressing that `E0'` is not used here. The inputs are
only:
- temperedness `E0`,
- Euclidean covariance `E1`,
- reflection positivity `E2`.

This means:
- the semigroup continuation mechanism is independent of the later growth
  estimates;
- any proof surface that imports `E0'` into the continuation theorem itself is
  not following the OS II chapter split.

This is especially important for the current repo because some earlier attempts
blurred "analytic continuation" with "boundary-value temperedness" or "growth
    package" statements. OS II does not.

## 7. Chapter V.1: Real Analyticity

### 7.1. Inputs

The paper starts from the Hilbert-space-valued distributions `Ψ_n(x,ξ)` and the
semigroup identity

`e^{-tH} Ψ_n(x,ξ) = Ψ_n(x+t, ξ)`.

Then, for a chosen time variable, a scalar product of `Ψ`-vectors gives a
one-variable analytic continuation, exactly as in OS I.

### 7.1.1. What is fixed and what varies

The continuation theorem in Chapter V.1 is frequently misunderstood because the
paper suppresses the spatial variables after introducing them.

What is fixed:
- the spatial variables `ξ`,
- the real positive-time basepoint `ξ^0`,
- the cone angle `γ`,
- the dual basis vectors `e_μ`.

What varies:
- the nonnegative coefficients `u_i^μ` in the chosen dual directions.

So the theorem is not "joint analyticity in all variables from nothing". It is:
- fix a real positive-time configuration,
- move it in carefully chosen complex directions,
- and prove local analyticity around that fixed real point.

### 7.2. Cone geometry

For a fixed real positive-time configuration `ξ`, choose:
- a cone `R_+^k(γ)` around the positive real axis in the time variables,
- in the 4-dimensional paper, four linearly independent vectors
  `e_1,...,e_4` in the dual cone;
- for the repo's general-`d` implementation, read this as a choice of
  `d + 1` linearly independent dual-cone vectors.

The key use of these directions is:
- for each direction separately, one can run the one-variable semigroup
  continuation;
- these directional continuations are compatible on overlaps because they come
  from the same distributional object.

### 7.2.1. Why the dual cone is used

The vectors `e_μ` are chosen in the dual cone of `R_+^k(γ)` so that:
- adding `u^μ e_μ` with `u^μ >= 0` keeps the imaginary part inside the
  admissible forward region,
- after rotation by the corresponding `A_μ`, the distinguished direction
  becomes the time axis.

This is what makes the OS I one-variable semigroup theorem applicable in each
chosen direction.

So the geometry is serving a very specific analytic purpose:
- it identifies finitely many directions in which the old one-gap theorem is
  valid,
- and it does so uniformly near the chosen real point.

### 7.3. Malgrange-Zerner

This is the first decisive several-complex-variable ingredient.

The paper introduces logarithmic coordinates `r_i^μ = s_i^μ + i t_i^μ` and uses
the directional continuations to build analytic functions on several flat tube
domains. Malgrange-Zerner then says these glue to an analytic function on the
convex envelope.

This proves local analyticity in all time variables around the chosen real
positive-time point.

### 7.3.1. Detailed proof transcript of the glue step

The glue step can be unpacked as:

1. For each pair `(i, μ)`, hold all other variables fixed and continue in the
   one variable `u_i^μ` by the OS I semigroup theorem.
2. Pass to logarithmic coordinates `s_i^μ = log u_i^μ`.
3. In those coordinates, each one-variable continuation becomes an analytic
   function on a flat tube `|Im r_i^μ| < π/2`.
4. All these partially continued functions agree on the common real slice
   because they come from the same original distribution.
5. Malgrange-Zerner then provides a single analytic continuation on the convex
   envelope of the union of these flat tubes.
6. Returning to the original variables gives analyticity in all chosen
   direction variables simultaneously.

So the role of Malgrange-Zerner is very concrete:
- it replaces the false "separately holomorphic implies jointly Laplace" step
  by an actual several-complex-variable continuation theorem on a specific
  family of tube domains.

### 7.4. Quantitative radius

Lemma 5.1 extracts an explicit polydisc of analyticity around each real point:
the radius is controlled by the positive time component divided by the Euclidean
size of the point.

This lemma matters a great deal for formalization:
- it is not just a pleasant side estimate;
- it is the entry point for the VI.1 regularization scale.

If the local analyticity radius is treated as a purely qualitative theorem, the
later VI.1 argument loses its scale.

### 7.4.1. Detailed proof transcript of Lemma 5.1

Lemma 5.1 is a coordinate estimate, not an abstract SCV theorem.

The proof is:

1. Define `γ` by the ratio of time component to Euclidean size, via `(5.10)`.
2. In the 4-dimensional paper, choose explicit dual-cone vectors
   `e_1, ..., e_4` as in `(5.11)`.
3. For the repo's general-`d` implementation, this becomes:
   write the standard basis vectors of `R^(d+1)` as linear combinations of the
   chosen dual-cone basis; this is the role of `(5.11')`.
4. Express the perturbed point `ξ_i + ζ_i` in the `e_μ` basis; this is
   `(5.12)`.
5. Require each resulting coordinate `w_i^μ` to stay in the sector
   `|arg w_i^μ| < π/2`.
6. Reduce this to the concrete inequalities `(5.13)` on the components of `ζ`.
7. Use the relation between `tan γ` and the original real point `(5.10)` to
   turn `(5.13)` into the explicit radius estimate `(5.14)`.

So the analyticity radius comes from a linear-algebra calculation in the chosen
dual basis, not from a generic compactness argument.

## 8. Chapter V.2: The `(A_N)/(P_N)` Ladder

This is the corrected replacement for the bad OS I Lemma 8.8 step.

### 8.1. Statements

`(A_N)`:
- scalar analytic continuation on time domains `C_k^(N)`.

`(P_N)`:
- Hilbert-space-valued vectors `Ψ_n(x,ζ)` on mixed domains `D_n^(N)` whose
  scalar products reproduce the analytically continued Schwinger functions.

### 8.2. Direction of implication

The proof alternates:
- `(P_N)` gives `(A_{N+1})`,
- then `(A_N)` gives `(P_N)`.

The mechanism is:
- scalar continuation is generated from matrix elements of the `Ψ`-vectors;
- once the scalar continuation exists, one reconstructs new `Ψ`-vectors by
  Taylor expansion in Hilbert space.

### 8.3. Hidden sublemma: Hilbert-space Taylor control

The construction of `Ψ_n(x,ζ)` from nearby real points is not formal handwaving.
The paper uses norm convergence of the Taylor series, and the scalar product
identity follows by passing to the limit from the already-continued scalar
functions.

So the induction uses two nontrivial facts:
- local holomorphic expansion with Hilbert-space values,
- compatibility of scalar products with that expansion.

### 8.4. Domain growth

Lemma 5.2 and Corollary 5.3 are the combinatorial/geometric engine:
- the domains `C_k^(N)` strictly enlarge at each stage;
- the union covers all of `C_+^k`.

This is the precise replacement for the false "separate continuation implies
joint continuation" leap.

Formalization lesson:
- one cannot replace this with a generic Hartogs slogan;
- one needs either these domains or a mathematically equivalent alternative
  continuation ladder.

### 8.5. Base step `(A_0) => (P_0)`

The paper is brief here, but the proof contains a real hidden step.

What is known at this point:
- `(A_0)` gives a scalar function `S_k(ζ)` locally analytic near the real
  positive-time domain;
- equation `(5.2)` is already available on the real side, but only in the sense
  of distributions.

What must be shown:
- the scalar-product identity `(5.17)` holds pointwise for the newly continued
  scalar function, not merely after smearing.

The paper's maneuver is:
1. choose approximate identity test functions on the positive-time side;
2. smear both sides of `(5.2)`;
3. use continuity of the locally analytic representative;
4. let the smearing shrink to a delta function.

So `(P_0)` is not a tautological rephrasing of `(5.2)`. It uses:
- compatibility of the local analytic representative with the distribution;
- a delta-sequence passage on the positive cone.

This is a useful Lean warning:
- whenever a theorem upgrades a distributional equality to a pointwise equality
  of an analytic representative, there is a hidden approximate-identity step.

### 8.5.1. Why the delta-sequence step is legitimate

The paper only says "smear with delta-sequences and take the limit", but the
actual justification requires:

1. both sides define continuous functionals on the relevant positive-time test
   space,
2. the locally analytic representative is continuous on the real slice,
3. approximate identities remain inside the positive-time region,
4. the scalar-product formula `(5.2)` is stable under the smearing limit.

So the base step is already using a boundary-regularity principle:
- distribution identity on a real slice
  +
  continuity of the analytic representative
  =>
  pointwise scalar-product identity.

Exact theorem-slot inventory for the base step:

```lean
lemma positive_time_delta_family_exists
    (τ : PositiveTimePoint k) :
    ∃ ρ : ℕ → PositiveTimeTestFamily k,
      approximateIdentityAt τ ρ := by
  -- choose compactly supported positive-time mollifiers centered at `τ`

lemma scalar_distribution_identity_stable_under_smearing
    (hdist : DistributionalEqualityOnPositiveTimeSlice S Ψ) :
    ∀ N,
      smearingPairing (ρ N) S = smearingPairing (ρ N) Ψ := by
  -- this is the smeared form of `(5.2)`

lemma analytic_representative_smearing_tends_to_point_value
    (hcont : ContinuousOn S positiveTimeSlice)
    (hρ : approximateIdentityAt τ ρ) :
    Tendsto (fun N => smearingPairing (ρ N) S) atTop (nhds (S τ)) := by
  -- continuity + approximate identity

lemma semigroup_side_smearing_tends_to_scalar_product
    (hΨcont : ContinuousOn (fun τ => scalarProductSide Ψ τ) positiveTimeSlice)
    (hρ : approximateIdentityAt τ ρ) :
    Tendsto (fun N => smearingPairing (ρ N) (scalarProductSide Ψ)) atTop
      (nhds (scalarProductSide Ψ τ)) := by
  -- same argument on the scalar-product side

theorem base_step_pointwise_scalar_product_identity
    (hA0 : AnalyticRepresentativeNearPositiveSlice S)
    (hdist : DistributionalEqualityOnPositiveTimeSlice S Ψ) :
    ∀ τ ∈ positiveTimeSlice, S τ = scalarProductSide Ψ τ := by
  -- choose `ρ`, compare the smeared expressions termwise,
  -- take the limit on both sides
```

So the later Lean port should see `(A_0) => (P_0)` as a four-stage package:

1. construct positive-time delta families,
2. smear the distribution identity,
3. pass to the limit on the analytic side,
4. pass to the limit on the scalar-product side.

The final pointwise identity is not a one-line "approximate by deltas" slogan.
It is the output of those four explicit lemmas.

There is one more bridge hidden here that should be named explicitly. The OS II
base step is not merely "use OS I semigroup continuation and then smear".
It uses the following three-layer input:

1. OS II Theorem 4.1 provides real analyticity on the ordered positive-time
   slice;
2. OS II Lemma 5.1, via the Malgrange-Zerner theorem, promotes that local
   analyticity to a genuine complex neighborhood / local polydisc continuation;
3. OS I Section 4.1 provides the semigroup scalar-product formula on the real
   positive-time slice.

Only after those three pieces are in place does the delta-family argument turn
distributional equality into the pointwise `(P_0)` scalar-product identity.

So the implementation-level theorem slots should also include:

```lean
lemma local_polydisc_extension_from_A0_and_lemma51
    (hA0 : RealAnalyticOnPositiveSlice S)
    (h51 : LocalTubeNeighborhoodControl S) :
    AnalyticRepresentativeNearPositiveSlice S := by
  -- this is the point where Lemma 5.1 / Malgrange-Zerner enters

lemma real_slice_semigroup_scalar_product_formula
    (hOSI : OSISemigroupPackage Ψ) :
    ∀ τ ∈ positiveTimeSlice, scalarBoundaryValue S τ = scalarProductSide Ψ τ := by
  -- this is the OS I one-gap semigroup theorem on the real slice
```

This matters because otherwise the later Lean port could still say "base step =
OS I semigroup construction", which is too coarse and hides the local SCV input
coming from OS II itself.

### 8.5.2. Exact correspondence between the OS II variable `ζ` and the OS I
semigroup parameter

This is the precise hidden bridge between Chapter V and OS I Section 4.1.

At stage `(A_0)` / `(P_0)`, the variables `ζ_1, ..., ζ_{n-1}` are not new
mathematical objects. They are the complexified versions of the real positive
time gaps already used in OS I.

The correspondence is:

1. on the real slice one has `ζ_i = τ_i` with `τ_i > 0`;
2. each `τ_i` is a positive time difference between consecutive Euclidean
   arguments;
3. OS I Section 4.1 packages such a positive time difference as the parameter
   of the contraction semigroup `e^{-τ_i H}`;
4. OS II Chapter V then allows `τ_i` to move off the positive real axis to a
   complex variable `ζ_i` in the right half-plane.

So the mathematical content of the base step is:

- OS I gives the real-parameter semigroup/scalar-product formula;
- OS II reinterprets the same real parameter as the boundary value of a
  holomorphic variable `ζ_i`;
- `(P_0)` is the statement that the already-continued scalar function agrees
  pointwise with the semigroup/scalar-product formula on that real boundary
  slice.

For later Lean implementation, the bridge must therefore be written with two
separate theorem slots:

1. a real positive-time theorem
   `F(τ) = (Ψ_left, e^{-τH} Ψ_right)` for `τ > 0`;
2. a boundary identification theorem saying that the holomorphic function of
   `ζ` has real boundary values equal to the same scalar-product expression.

Only after those are both present can one honestly say that the OS II
continuation variable `ζ` is "the same parameter" as the OS I semigroup time.

### 8.6. Inductive step `(P_{M-1}) => (A_M)`

This is the easier half of the induction, but it still has a very specific
shape.

Assume `(P_{M-1})`. Then for admissible mixed-domain points
`(x,ζ) in D_n^(M-1)` and `(x',ζ') in D_m^(M-1)` the scalar product

`(Ψ_n(x,ζ), Ψ_m(x',ζ'))`

is already defined and analytic in each block of variables. By `(5.17)` it
agrees on the real slice with `S_{n+m-1}` evaluated on a specific tuple of time
differences, namely

`(-\bar ζ, x+x', ζ')`.

So the paper defines `S_k` first on a union of mixed domains obtained from
those scalar products. The crucial point is:
- this union is not yet the final domain `C_k^(M)`;
- the paper then invokes the *definition* of `C_k^(M)` as the envelope of
  holomorphy of that union.

Therefore the logical structure is:
1. scalar products from `(P_{M-1})` produce analyticity on a concrete union of
   tube-like pieces;
2. the envelope-of-holomorphy construction expands that analyticity to the full
   `C_k^(M)`.

This matters for formalization because the second step is not free:
- either the concrete envelope theorem must be available,
- or the Lean theorem surface must build `C_k^(M)` in a way that already
  packages this extension.

### 8.6.2. Exact variable bookkeeping in `(P_{M-1}) => (A_M)`

For later implementation, the scalar-product continuation should be remembered
with the following bookkeeping:

- if `k = n + m - 1`,
- the left vector contributes `n-1` continued time variables `ζ`,
- the right vector contributes `m-1` continued time variables `ζ'`,
- the middle real variable is `x + x'`,
- the resulting scalar point in `C_k^(M)` is
  `(-\bar ζ, x + x', ζ')`.

So the continuation step is not symmetric in all variables. It is built from
two continued blocks with a real bridge coordinate in the middle. That pattern
must be preserved if one later recreates this step in Lean.

### 8.6.1. Why the scalar-product formula has the right variable pattern

The scalar-product formula uses

`(-\bar ζ, x+x', ζ')`.

This pattern is not arbitrary. It is the same one already present in `(5.17)`:

- the left block enters with reflection and complex conjugation,
- the middle variable is the positive real bridge variable `x + x'`,
- the right block enters unchanged.

So the continuation from `(P_{M-1})` to `(A_M)` preserves the OS positivity
geometry. This is another reason one cannot replace it by a generic SCV
assertion detached from the Hilbert-space scalar product.

For later Lean implementation, the notation `-\bar ζ` must also be translated
into the repo's conjugation conventions explicitly.

Paper notation:
- `ζ` is a block of complexified positive-time parameters;
- `\bar ζ` means coordinatewise complex conjugation;
- the leading minus sign is the reflection of the left block under OS
  positivity.

Repo-side semantic translation:

1. on the Euclidean / Schwinger side, the reflected-conjugated left block is
   represented by `osConjTensorProduct`;
2. on the reconstructed Wightman side, the corresponding reflected-conjugated
   left block is represented by `conjTensorProduct`;
3. the scalar-product pattern `(-\bar ζ, x + x', ζ')` is therefore the
   time-parameter analogue of the same left-reflection/right-identity geometry
   encoded by those two tensor-product constructions.

So the later Lean port should not treat `-\bar ζ` as anonymous notation.
Whenever Chapter V or VI uses that pattern, the implementation notes should
explicitly ask:

1. which side is playing the role of the reflected left block?
2. is the current formula on the Euclidean side (`osConjTensorProduct`) or the
   Wightman side (`conjTensorProduct`)?
3. which real bridge variable is playing the role of `x + x'`?

This notation dictionary matters even if the eventual theorem-3 port avoids the
full general `(P_N)/(A_N)` machinery, because it prevents the common error of
flattening OS reflection/conjugation into an ordinary complex conjugation with
no tensorial meaning.

### 8.7. Inductive step `(A_M) => (P_M)`

This is the subtler half and the part that is easiest to under-document in a
formalization.

Fix `(x,ζ) in D_n^(M)`. The paper first chooses:
- real positive times `ξ_i > 0`,
- radii `r_i > 0`,
such that the polydisc

`P = {(x,ζ) | x = x, |ζ_i - ξ_i| < r_i}`

lies entirely inside `D_n^(M)`.

Then `Ψ_n(x,ζ)` is defined by the strong-Hilbert-space Taylor series

`Σ_α ((ζ-ξ)^α / α!) ∂^α Ψ_n(x,ξ)`.

Two hidden facts are packed into the next sentence of the paper:

1. The derivatives `∂^α Ψ_n(x,ξ)` already make sense as Hilbert-space vectors.
   This comes from the previous stage, because the scalar products of those
   derivatives are read off from derivatives of the already-continued scalar
   functions.

2. The series converges in norm. The proof is the estimate `(5.21)`:
   the squared norm of the remainder is identified with the remainder term in
   the Taylor expansion of the scalar function
   `S_{2n-1}(-\bar ζ, 2x, ζ)` around
   the real point `(ξ,2x,ξ)`.

So the vector-valued analyticity is not postulated. It is reconstructed from
scalar analyticity plus positivity of the scalar-product formula.

This is one of the clearest paper precedents for the current project's
discipline:
- scalar continuation data should be turned into Hilbert-space or kernel data
  only through explicit norm-control and scalar-product identities.

### 8.7.1. Why the remainder norm equals a scalar Taylor remainder

The key estimate `(5.21)` identifies the square of the norm of the vector
Taylor remainder with the scalar Taylor remainder of

`S_{2n-1}(-\bar ζ, 2x, ζ)`.

This works because:

1. scalar products of derivatives of `Ψ_n` can be computed by differentiating
   the scalar-product identity `(5.17)`;
2. the Hilbert norm squared of the remainder is the scalar product of the
   remainder with itself;
3. after expanding that scalar product, one gets exactly the scalar Taylor
   remainder of the continued Schwinger function at the doubled point.

So `(5.21)` is not an analogy. It is a literal equality produced by the
scalar-product formula.

The minus sign on the left block is essential: it is the time-reflection sign
coming from the OS inner product / reflected first block in `(5.17)`. So this
Taylor expansion is a real-analytic expansion of the norm-squared scalar
function built from the OS-reflected argument pattern, not a holomorphic Taylor
expansion of an unrelated `S_{2n-1}(ζ,2x,\bar ζ)` expression.

### 8.7.2. Why the polydisc is chosen around a real point

The paper chooses the center `ξ` of the Taylor expansion on the real positive
slice rather than at the target complex point `ζ`. This is essential:

- derivatives of `Ψ_n` are already known there from the previous stage;
- the scalar-product formula is already available there in a concrete Hilbert
  sense;
- the scalar Taylor remainder can be controlled there by the already-proved
  scalar analyticity.

So the vector-valued continuation is anchored at a real point where the Hilbert
structure is concrete, not at an arbitrary interior complex point.

### 8.7.3. Full theorem-slot inventory for `(A_M) => (P_M)`

For a later Lean port, the previous prose should be read as the following
explicit chain of local obligations.

Fix `(x,ζ) ∈ D_n^(M)`. Choose a real basepoint `ξ` and radii `r_i > 0` such
that the closed polydisc

`P(ξ,r) = {w | ∀ i, ‖w_i - ξ_i‖ < r_i}`

lies in `D_n^(M)`.

The hidden local theorems are then:

```lean
lemma scalar_product_of_vector_derivatives_from_PM
    (hPM : P_M)
    (x : RealSpaceTuple n)
    (ξ : PositiveTimeTuple (n - 1))
    :
    ∀ α β,
      inner
        (vectorDerivativeAt (Ψ_n := Ψ_n) x ξ α)
        (vectorDerivativeAt (Ψ_n := Ψ_n) x ξ β)
      =
      scalarDerivativeAt
        (fun (u,v) => S_(2 * n - 1) (-conj u, 2 * x, v))
        (ξ, ξ) (α, β) := by
  -- differentiate the real-slice pairing identity `(5.17)` in both blocks

lemma vector_taylor_series_defined_on_real_basepoint
    (hPM : P_M)
    (x : RealSpaceTuple n)
    (ξ : PositiveTimeTuple (n - 1))
    :
    FormalMultilinearSeries ℂ (HilbertSpaceField d) := by
  -- package `∂^α Ψ_n(x, ξ)` into the candidate Taylor coefficients

lemma vector_remainder_norm_sq_eq_scalar_remainder
    (hPM : P_M)
    (x : RealSpaceTuple n)
    (ξ : PositiveTimeTuple (n - 1))
    (r : PositiveRadiusTuple (n - 1))
    :
    ∀ N w,
      ‖vectorTaylorRemainder (Ψ_n := Ψ_n) x ξ N w‖^2 =
        scalarTaylorRemainder
          (fun z => S_(2 * n - 1) (-conj z, 2 * x, z))
          ξ N w := by
  -- expand the remainder norm squared and rewrite every scalar product using `(5.17)`

lemma scalar_remainder_tends_to_zero_on_internal_polydisc
    (hAM : A_M)
    (x : RealSpaceTuple n)
    (ξ : PositiveTimeTuple (n - 1))
    (r : PositiveRadiusTuple (n - 1))
    :
    ∀ w ∈ closedPolydisc ξ r,
      Tendsto
        (fun N =>
          scalarTaylorRemainder
            (fun z => S_(2 * n - 1) (-conj z, 2 * x, z))
            ξ N w)
        atTop (nhds 0) := by
  -- ordinary scalar holomorphic Taylor theorem on the polydisc from `A_M`

lemma strong_taylor_series_converges_on_internal_polydisc
    (hAM : A_M) (hPM : P_M)
    (x : RealSpaceTuple n)
    (ξ : PositiveTimeTuple (n - 1))
    (r : PositiveRadiusTuple (n - 1))
    :
    ∀ w ∈ closedPolydisc ξ r,
      Summable (vectorTaylorSeriesTerms (Ψ_n := Ψ_n) x ξ w) := by
  -- use the previous two lemmas and positivity of the Hilbert norm

lemma vector_continuation_from_polydisc_taylor_series
    (hAM : A_M) (hPM : P_M)
    :
    ∃ Φ : D_n^(M) → HilbertSpaceField d,
      (∀ (x,ζ) ∈ realPositiveSlice, Φ (x,ζ) = Ψ_n x ζ) ∧
      HolomorphicOn Φ D_n^(M) := by
  -- define Φ by the convergent local Taylor series and glue overlapping discs

lemma scalar_pairing_formula_extends_from_real_slice
    (hAM : A_M) (hPM : P_M)
    :
    ∀ (x,ζ) ∈ D_n^(M),
      inner (Φ x ζ) (Φ x ζ) =
        S_(2 * n - 1) (-conj ζ, 2 * x, ζ) := by
  -- identity theorem: both sides are holomorphic/real-analytic and agree on the real slice
```

The point of writing the proof this way is to make the dependency direction
unambiguous:

1. `P_M` gives the scalar-product identity on the real slice and therefore
   gives scalar products of derivatives there.
2. `A_M` gives scalar analyticity on the polydisc, hence Taylor convergence for
   the scalar function `S_{2n-1}(-conj z, 2x, z)`.
3. The norm-remainder identity transfers scalar Taylor convergence into
   norm-convergence of the vector Taylor series.
4. Only after that is a genuine vector-valued continuation on `D_n^(M)`
   defined.

So the proof does not assume a Hilbert-valued holomorphic function at the start.
It manufactures one from scalar Taylor control.

### 8.7.4. Detailed micro-proof of the norm estimate `(5.21)`

The paper writes `(5.21)` in a compressed form. The full proof should be read
as follows.

1. Let
   `R_N(ζ) := Ψ_n(x,ζ) - Σ_{|α| ≤ N} ((ζ-ξ)^α / α!) ∂^α Ψ_n(x,ξ)`.
2. Expand `‖R_N(ζ)‖^2 = ⟪R_N(ζ), R_N(ζ)⟫`.
3. Expand both copies of `R_N(ζ)` as finite sums plus the full vector.
4. Rewrite each scalar product of derivatives by differentiating `(5.17)`:
   every term becomes a scalar derivative of
   `S_{2n-1}(-conj z, 2x, z)` at `ξ`.
5. Collect the resulting coefficients. They are exactly the scalar Taylor
   remainder of that scalar function about `ξ`.
6. Conclude
   `‖R_N(ζ)‖^2 = R_N^scalar(ζ)`.
7. Because `R_N^scalar(ζ) → 0` on the polydisc by ordinary holomorphic Taylor
   theory, the vector remainder converges to zero in norm.

The delicate point is step 4. There is no independent vector derivative theory
being invoked. The derivative data are valid only because `(5.17)` already
encodes all scalar products of the would-be derivatives.

### 8.7.5. Exact Lean-style pseudocode for `(A_M) => (P_M)`

```lean
theorem inductive_step_AM_to_PM
    (hAM : A_M) (hPM : P_M) :
    P_{M+1} := by
  intro n x ζ hζ
  obtain ⟨ξ, r, hξ_real, hdisc⟩ :=
    choose_real_basepoint_and_polydisc_inside_DnM hζ
  let coeffs :=
    vector_taylor_series_defined_on_real_basepoint
      (hPM := hPM) (x := x) (ξ := ξ)
  have hrem :
      ∀ N w ∈ closedPolydisc ξ r,
        ‖vectorTaylorRemainder (Ψ_n := Ψ_n) x ξ N w‖^2 =
          scalarTaylorRemainder
            (fun z => S_(2 * n - 1) (-conj z, 2 * x, z))
            ξ N w :=
    vector_remainder_norm_sq_eq_scalar_remainder
      (hPM := hPM) (x := x) (ξ := ξ) (r := r)
  have hscalar :
      ∀ w ∈ closedPolydisc ξ r,
        Tendsto
          (fun N =>
            scalarTaylorRemainder
              (fun z => S_(2 * n - 1) (-conj z, 2 * x, z))
              ξ N w)
          atTop (nhds 0) :=
    scalar_remainder_tends_to_zero_on_internal_polydisc
      (hAM := hAM) (x := x) (ξ := ξ) (r := r)
  have hsum :
      ∀ w ∈ closedPolydisc ξ r,
        Summable (vectorTaylorSeriesTerms (Ψ_n := Ψ_n) x ξ w) :=
    strong_taylor_series_converges_on_internal_polydisc
      (hAM := hAM) (hPM := hPM) (x := x) (ξ := ξ) (r := r)
  let Φ :=
    vectorContinuationFromTaylorSeries
      (Ψ_n := Ψ_n) x ξ r coeffs hsum
  have hpair :
      ∀ w ∈ closedPolydisc ξ r,
        inner (Φ w) (Φ w) =
          S_(2 * n - 1) (-conj w, 2 * x, w) :=
    scalar_pairing_formula_extends_from_real_slice
      (hAM := hAM) (hPM := hPM)
  exact package_local_PM_data_from_vector_continuation Φ hpair
```

This is the level of detail the later Lean port should preserve. Nothing about
the Hilbert-valued continuation should be left as "standard" or "formal."

### 8.8. Proof skeleton of Lemma 5.2

Lemma 5.2 is the real replacement for the false OS I many-variable jump. The
paper proves it by introducing recursively defined numbers, written in the
paper as `ρ(i,N)`, satisfying the recursion encoded in `(5.27)`. In our local
notes we may temporarily write them as `h_i^(N)`, but the important point is
that they are defined recursively from the convex-hull step and *not* by a
standalone closed formula.

`h_i^(N+1) = (i / (2i-1)) * (h_{i-1}^(N) + π/2)`,

with `h_i^(0) = 0`, and then showing that the points

`(0, h_1^(N), ..., h_{s-1}^(N))`

lie in the mixed domains `d_s^(N)`.

There are three structural ideas hidden here:

1. Convexity and sign symmetry of the logarithmic tube bases `c_k^(N)` and
   `d_n^(N)` let the proof work with a single positive orthant representative.
2. The recursive formula is obtained by averaging two extreme points already
   known to lie in the previous-stage convex set.
3. What the paper actually uses later is not a closed form for `ρ(i,N)` but an
   explicit lower bound `(5.28)` strong enough for Corollary 5.3.

Important correction:

- the earlier local note claiming the exact closed form
  `h_i^(N) = (π/2) * (1 - (2i-1)^(-N))`
  was incorrect and should not be used;
- the associated claim that `h_i^(N) -> π/2` for each fixed `i` was therefore
  also incorrect as stated;
- for the formalization, the mathematically relevant output is the paper's
  explicit quantitative lower bound `(5.28)` and the resulting exhaustion
  statement in Corollary 5.3, not the false closed-form shortcut.

So the domain-exhaustion theorem is not qualitative. It is a very explicit
combinatorial induction.

Implementation-level theorem-slot inventory for Lemma 5.2 / Corollary 5.3:

```lean
lemma recursive_angle_parameters_exist
    :
    ∃ ρ : ℕ → ℕ → ℝ,
      (∀ i, ρ i 0 = 0) ∧
      (∀ i N, ρ (i + 1) (N + 1) =
        ((i + 1 : ℝ) / (2 * i + 1)) * (ρ i N + π / 2)) := by
  -- recursive angle parameters from the convex-hull step `(5.27)`

lemma orthant_point_in_mixed_domain_of_recursive_angles
    (ρ : ℕ → ℕ → ℝ)
    (hρ : RecursiveAngleSystem ρ) :
    ∀ s N, (0, ρ 1 N, ..., ρ (s - 1) N) ∈ d_s^(N) := by
  -- this is the actual inductive content of Lemma 5.2(a)

lemma ck_contains_sector_box_of_recursive_angles
    (ρ : ℕ → ℕ → ℝ)
    (hρ : RecursiveAngleSystem ρ) :
    ∀ k N, sectorBoxFromAngles (fun i => ρ i N) ⊆ C_k^(N) := by
  -- this is Lemma 5.2(b)

lemma recursive_angles_admit_quantitative_lower_bound
    :
    ∃ γ : ℕ → ℝ,
      ∀ i N, lowerBoundFromFormula528 γ i N ≤ ρ i N := by
  -- paper's explicit lower bound `(5.28)`, without pretending a false exact formula

lemma choose_stage_from_argument_bounds
    (ζ : CPlusTuple k) :
    ∃ N, ζ ∈ C_k^(N) := by
  -- Corollary 5.3 + the argument comparison used later in VI.2
```

The critical point is that the later Lean port should *not* try to prove a
closed form for `ρ(i,N)` unless the exact paper formula has first been checked
from the source. The formalization only needs:

1. the recursive construction,
2. the domain-membership induction,
3. the quantitative lower bound used in Corollary 5.3,
4. the stage-selection theorem `N = N(ζ)` used in VI.2.

### 8.8.1. Why Lemma 5.2 is enough to reach all of `C_+^k`

The key output of Lemma 5.2 is that for every fixed angle away from the
boundary of the right half-plane, some finite stage `N` already captures that
angle. Corollary 5.3 then quantifies this using the lower bound `(5.28)` in the
form used later by VI.2.

So the union

`⋃_N C_k^(N) = C_+^k`

is not merely topological. It is quantitatively controlled by the recursively
defined angle parameters from `(5.27)` together with the explicit lower bound
`(5.28)` and the derived constants `γ_k`.

## 9. Chapter VI Overview: The Role of `E0'`

Chapter VI starts only after continuation is in place.

Problem:
- a real-analytic or holomorphic continuation need not satisfy polynomial
  bounds.

Goal:
- prove the real-domain estimate `(4.5)`,
- then transport it along the continuation ladder.

The paper is very clear that `E0'` is used here to control the size of
regularized Hilbert-space vectors, not to produce the continuation itself.

## 10. Chapter VI.1: From Distributions to Functions

This is the hardest technical chapter relevant to the current Lean frontier.

### 10.1. Why a naive argument fails

The paper explicitly warns that even if `S_k` is distributionally tempered and
real analytic, it does not follow that the resulting function is polynomially
bounded. The counterexample is a smooth function with huge spikes on tiny
intervals.

So one must not argue:
- "the Schwinger function is a tempered distribution and also a function,
  therefore it has polynomial growth."

OS II rejects exactly that shortcut.

### 10.2. Regularization

Fix a real point `ξ` and the local analyticity radius `ρ(ξ)` from Lemma 5.1.
Construct:
- a bump `h`,
- a regularizing function `g_ρ`,
- a radial kernel `k_ρ`,
- then a regularized object `T_k`.

The mean-value theorem for harmonic functions gives

`S_k(ξ+ζ)` as an average of `T_k` over a small complex neighborhood.

This is the first absolutely decisive proof-shape lesson for the current
formalization:
- VI.1 does not estimate the raw boundary-value function directly;
- it estimates a regularized auxiliary object that still preserves positivity.

More concretely, the paper's definitions are:

- `(6.1)`: the mean-value identity for `S_k(ξ+ζ)` on the local polydisc;
- `(6.2)`: choose a positive `C_0^∞` bump `h` with normalization
  `∫ h(r) r^{2(d+1)-1} dr = 1` and controlled derivatives;
- choose the radial support convention explicitly as `supp h ⊆ [0, 1/8]`,
  since this is what later forces the rescaled kernels to stay inside the
  `ρ/8` and `ρ/4` balls;
- in the 4-dimensional paper this is `∫ h(r) r^7 dr = 1`;
- define `g_ρ(z) = c ρ^{-2(d+1)} h_ρ(|z|)` on `C^(d+1)`, with the scaling
  chosen so that `supp g_ρ ⊆ {|z| < ρ/8}`;
- define `k_ρ = g_ρ * g_ρ`, so `supp k_ρ ⊆ {|z| < ρ/4}` and `∫ k_ρ = 1`;
- define `k_ρ^k` as the product kernel in `k` blocks;
- `(6.5)`: define the regularized object `T_k` by integrating the shifted
  values of `S_k` against `g_ρ` and `k_ρ`.

Then `(6.6)` rewrites the original function as

`S_k(ξ+ζ) = ∬ T_k(ξ+ζ+iy') d y d y'`

over a small region, and `(6.7)` turns this into a supremum bound on `T_k`.

So the regularization package uses:
- mean-value theorem for harmonic functions,
- support bookkeeping for `g_ρ` and `k_ρ`,
- Fubini to rearrange the averaging integrals.

If a later Lean formalization wants VI.1 in a faithful way, those ingredients
need explicit local lemmas. They are not optional cosmetic details.

### 10.2.1. Derivation of `(6.6)` from `(6.1)`-`(6.5)`

The paper compresses several integral manipulations into one displayed formula.
Unpacked, the derivation is:

1. Start from the mean-value theorem `(6.1)` for the holomorphic function
   `S_k(ξ+ζ)`.
2. Replace the sphere average by a radial average using the mollifier `h` from
   `(6.2)`.
3. Normalize the radial average to obtain the compactly supported smooth kernel
   `g_ρ`.
4. Convolve `g_ρ` with itself to form `k_ρ`; this improves support bookkeeping
   and gives a symmetric kernel with total mass `1`.
5. Because the support of `k_ρ` sits inside the analyticity polydisc, inserting
   the convolution does not change the value of the averaged holomorphic
   function.
6. Apply Fubini to rearrange the resulting nested integrals blockwise.
7. Define the inner integral to be `T_k`.
8. The remaining outer integral is exactly `(6.6)`.

So `(6.6)` is not a mysterious formula; it is a reorganized mean-value theorem
after inserting a compactly supported approximate identity that is compatible
with the local analyticity radius.

### 10.2.2. Derivation of `(6.7)`

Once `(6.6)` is written down, `(6.7)` is obtained by:

1. taking absolute values of both sides,
2. using positivity of the regularizing kernels,
3. using that the outer integration region is contained in the support region
   where `|y_i| < ρ/4` and `|y'_i| < ρ/8`,
4. bounding the weighted average by the supremum of `|T_k|` on that region.

So `(6.7)` is the precise point where the argument turns the average formula
into a supremum estimate. This is why all later effort goes into bounding `T_k`
rather than `S_k` directly.

### 10.3. Positivity channeling

`T_k` is then written as a Hilbert-space scalar product of two vectors `Ψ_1` and
`Ψ_2`. Once in that form, the semigroup yields an analytic continuation in one
chosen variable and the uniform bound

`|<Ψ_1, e^{-zH} Ψ_2>| <= ||Ψ_1|| ||Ψ_2||`.

This is the second decisive lesson:
- the growth estimate is obtained by routing through the same positive semigroup
  used for continuation, but only after regularization.

Formulaically, `(6.8)` is the key bridge. After rotating to the preferred
direction `e_μ`, the regularized object at `ξ + u e_μ` is represented as an
integral pairing that has exactly the OS-positivity shape. The paper then reads
that integral as a scalar product

`T_k(ξ + u e_μ) = (Ψ_1, Ψ_2)`.

At that point the semigroup inserts a complex translation in the distinguished
direction and gives the one-variable analytic function

`(Ψ_1, e^{-zH} Ψ_2)`.

This is the exact place where the proof returns to the OS I semigroup mechanism.
Everything before it is packaging; everything after it is norm estimation.

### 10.3.1. The vectors `Ψ_1`, `Ψ_2` from `(6.10)`

The paper's formula `(6.10)` should be read extremely literally. The vectors
`Ψ_1` and `Ψ_2` are obtained by feeding specific Euclidean test data into the
same OS Hilbert-space map constructed earlier:

- the first vector uses the first `n-1` difference variables together with the
  mollifier `g_ρ` in the distinguished block;
- the second vector uses the remaining `k-n` difference variables together with
  the kernel `k_ρ` and the shifted real point.

The conceptual point is:
- `T_k` is not an abstract scalar product representation theorem;
- the vectors are written down explicitly from the regularization kernels.

So a faithful later formalization should not merely prove existence of two
vectors. It should define the vectors and then prove the scalar-product
identity.

### 10.3.2. The one-variable semigroup insertion `(6.11)`

Once `T_k(ξ+u e_μ)` is rewritten as `(Ψ_1, Ψ_2)`, the paper inserts the
semigroup exactly as in OS I:

1. vary the chosen directional parameter `u_{nμ}`;
2. interpret that variation as a positive-time shift in the distinguished OS
   variable;
3. obtain an analytic continuation by sandwiching `e^{-wH}` between `Ψ_1` and
   `Ψ_2`;
4. use contractivity to bound the resulting analytic function uniformly in the
   auxiliary parameters `y`, `y'`.

The important detail is the phrase "uniformly in `y`, `y'`". This means the
semigroup bound is not merely pointwise in the regularization parameters; it is
stable across the whole support region of the regularizing kernels. That
uniformity is what later allows the supremum estimate in `(6.7)` to be
effective.

### 10.3.3. Relationship between `T_k` in OS II and the repo's `bvt_F`

This is exactly where the current project must avoid conflating two different
analytic objects.

In the paper:

- `S_k` is the Schwinger function already continued to an interior domain;
- `T_k` is a *regularized* auxiliary function obtained by averaging `S_k`
  against the kernels `g_ρ` and `k_ρ`;
- the semigroup estimate is proved for `T_k`, not directly for `S_k`.

In the repo:

- `bvt_F` is the unregularized common holomorphic tube object coming from the
  BHW / boundary-value construction;
- the positive-real theorem-3 shell compares special evaluations or pairings of
  `bvt_F`, `OS.S`, and `bvt_W`;
- there is not yet a separate production object named `T_k` playing the exact
  role of OS II's mollified auxiliary kernel.

So the honest correspondence is:

1. `bvt_F` is analogous to the *pre-regularization* common holomorphic object;
2. `T_k` is analogous to a local average or mollified slice built from that
   object when one needs VI.1-style bounds;
3. therefore one must never write "`T_k = bvt_F`" in the documentation;
4. if a future Lean step needs the full VI.1 estimate mechanism, it must define
   and analyze an explicit regularized kernel on top of `bvt_F`, not pretend
   that the unregularized object already has the same quantitative properties.

For theorem 3 specifically, this means:

- the current route may still work without introducing a full `T_k` analogue if
  the one-variable boundary-value identity is obtained through the existing K2
  uniqueness/transport machinery;
- but any later attempt to imitate VI.1 for estimates must introduce a genuine
  regularized object and prove its relation to `bvt_F` first.

### 10.4. Where `E0'` enters

The norms `||Ψ_1||`, `||Ψ_2||` are controlled using the linear growth condition.
The linear dependence of the Schwartz order on the number of variables is what
makes the constant bookkeeping manageable.

So in formalization terms:
- `E0'` feeds the bound on regularized Hilbert vectors;
- it is not a replacement for the semigroup or the continuation domains.

The paper's displayed inequality `(6.9)` is already part of this bookkeeping:
it controls how the rotated/shifted configuration grows in terms of the local
radius `ρ(ξ)` and the added directional parameter `u`.

That estimate matters because it is what lets the eventual `E0'` seminorm bound
see only polynomial growth in `ξ`. In other words:
- geometric control of the shifted points comes first,
- seminorm control is applied second.

### 10.4.1. How `(6.12)` is proved from `(6.17)`-`(6.19)`

The paper defers the proof of the norm estimate `(6.12)` and then gives it at
the end of VI.1. Since this is exactly the sort of hidden step that causes
later confusion, it should be unpacked in full.

The proof of `(6.12)` is:

1. Start from the scalar-product formula `(5.2)` for the OS Hilbert norm and
   insert the explicit vectors `(6.10)`.
2. This yields the long integral expression `(6.17)` for `‖Ψ_1‖^2`.
3. Apply the linear growth condition `E0'` to the resulting test function.
   This is where the sequence `σ_{2n-1}` appears.
4. Estimate the support of the regularizing kernels:
   - `|x_n - λ_n| < ρ/8`,
   - `|x_i - x_{i+1} - λ_i| < ρ/4`,
   and similarly for the `y`-variables.
5. Deduce the polynomial control `(6.18)` on the full tuple
   `1 + Σ x_i^2 + Σ y_i^2` in terms of the shifted geometric variables `λ_i`.
6. Estimate derivatives of the regularizers using `(6.2)` and `(6.3)`.
7. Feed those support and derivative bounds into the `E0'` seminorm estimate.
8. Conclude `(6.12)` for `‖Ψ_1‖`, and analogously for `‖Ψ_2‖`.

So the order of dependence is:
- kernel support bounds,
- then Schwartz seminorm bounds on the regularizers,
- then `E0'`,
- then the Hilbert norm estimate.

### 10.4.2. Why `(6.9)` and `(6.18)` are separate

The paper uses two different geometric inequalities:

- `(6.9)` controls the rotated/shifted point appearing in the analytic
  continuation step;
- `(6.18)` controls the actual variables in the regularizer norm estimate.

They serve different purposes:
- `(6.9)` feeds the bound on the analytically continued function;
- `(6.18)` feeds the bound on the `E0'` seminorm of the explicit vectors.

This distinction is easy to miss because both are "polynomial growth"
inequalities, but they live in different parts of the argument.

### 10.5. Four-direction continuation again

The paper repeats the directional continuation idea from Chapter V, but now on
the regularized object `T_k`. Each direction yields a bound on a flat tube, and
Malgrange-Zerner plus the maximum principle propagate the bound to the whole
local analytic neighborhood.

This is a characteristic OS II pattern:
- continue in finitely many geometrically chosen directions,
- glue to the convex envelope,
- then use a maximum principle to transport estimates.

### 10.6. Hidden constant tracking

The inequalities `(6.9)`-`(6.16)` are not cosmetic:
- they show exactly how the local radius `ρ(ξ)` and the Euclidean size `|ξ|`
  control the bound;
- they are what eventually produce the concrete polynomial estimate `(4.5)`.

A Lean route that skips explicit dependence on the analyticity radius is not yet
following VI.1 faithfully.

### 10.6.1. The chain `(6.13)` -> `(6.14)` -> `(6.15)` -> `(6.16)`

The displayed inequalities here are the real analytic heart of VI.1.

1. `(6.13)` combines:
   - the semigroup bound `(6.11)`,
   - the Hilbert norm estimate `(6.12)`,
   - the geometric control `(6.9)`.

   The output is a uniform bound on the directional continuation
   `T_k(ξ + u e_μ)`.

2. Introduce logarithmic coordinates `r = log w`. This converts the wedge-type
   domain in `w` into a flat tube domain in `r`.

3. `(6.14)` rewrites the previous bound in the logarithmic variables.

4. Since all the directional continuations coincide on the common real slice,
   Malgrange-Zerner gives a single analytic continuation on the convex envelope
   of the union of the flat tubes.

5. `(6.15)` uses the envelope-of-holomorphy / maximum-principle argument: the
   supremum on the convex envelope equals the supremum on the original union of
   flat tubes.

6. Return from `r` to `w`, then from `w` to `ζ`, to obtain the local bound on
   `T_k`.

7. Finally combine this with `(6.7)` and the coordinate decomposition `(5.12)`
   to obtain `(6.16)`, which is exactly the desired real-domain estimate
   `(4.5)`.

So the proof is not "apply maximum principle to the original `S_k`". It is:
- regularize,
- continue directionally,
- pass to log coordinates,
- glue,
- maximize,
- unroll coordinates,
- then unregularize.

### 10.6.2. Why logarithmic coordinates are essential

The passage `w -> r = log w` is not a change of notation. It changes the domain
from:
- a product of wedge-type multiplicative regions in the `w`-variables

to
- a union of flat additive tube domains in the `r`-variables.

That transformation is exactly what allows Malgrange-Zerner to apply in the
form the paper uses. Without it, one does not have the right convexity theorem
available on the original multiplicative domain.

So if later Lean work ever tries to bypass the logarithmic-coordinate step, it
must replace it with a theorem of comparable strength on the original wedge
domain; otherwise it is not following the paper proof.

### 10.7. Step-by-step proof skeleton of VI.1

To make later implementation straightforward, it is useful to isolate the exact
flow of VI.1 as a sequence of proof obligations.

For fixed `k` and real positive-time point `ξ`:

1. Use Lemma 5.1 to choose a radius `ρ(ξ)` on which `S_k` is holomorphic.
2. Choose the auxiliary cutoff data `h`, `g_ρ`, `k_ρ` with the support and
   normalization properties listed in the paper.
3. Define the regularized object `T_k` by convolving / averaging the analytic
   continuation against those kernels.
4. Prove the mean-value identity expressing `S_k(ξ+ζ)` as an average of `T_k`
   over a smaller complex neighborhood.
5. Rewrite `T_k` as an OS Hilbert-space scalar product
   `<Ψ_1, Ψ_2>`.
6. Insert the semigroup in one chosen direction and obtain
   `<Ψ_1, e^{-zH} Ψ_2>`.
7. Use contractivity of `e^{-zH}` in the right half-plane to bound the scalar
   product by `||Ψ_1|| ||Ψ_2||`.
8. Use `E0'` to estimate `||Ψ_1||` and `||Ψ_2||` in terms of the local scale
   `ρ(ξ)` and the Euclidean size of `ξ`.
9. Transfer the directional estimates to the full local neighborhood by the
   multi-direction continuation argument.
10. Convert the local bound into the global polynomial estimate `(4.5)`.

Every later formalization of VI.1 should be auditable against those ten steps.
If a proposed proof does not exhibit all of them, it is suppressing an
analytic input.

### 10.8. What VI.1 does *not* allow

Because the paper is so explicit here, we can safely rule out several tempting
shortcuts:

- It does not permit concluding polynomial bounds directly from real
  analyticity.
- It does not permit a proof that never introduces a regularized auxiliary
  object.
- It does not permit replacing the Hilbert-space norm estimate by a bare
  distributional uniqueness argument.
- It does not permit sliding between boundary values and interior evaluations
  without first establishing the correct local continuation object.

Those prohibitions are especially relevant to the current theorem-3 frontier.

### 10.9. Minimal local lemma inventory suggested by VI.1

If VI.1 ever has to be formalized more completely in Lean, the paper suggests a
very specific local lemma inventory:

1. quantitative local analyticity radius,
2. normalized radial bump with derivative bounds,
3. support and normalization properties of the convolution kernel,
4. mean-value identity for holomorphic functions on a polydisc,
5. Fubini-safe regularization identity,
6. positivity/scalar-product representation of the regularized kernel,
7. semigroup bound on that scalar product,
8. polynomial comparison between the shifted geometric point and the original
   real point,
9. maximum-principle propagation from directional bounds to full local bounds.

Writing those down now is useful even before formalization, because it prevents
future proof attempts from silently collapsing several genuinely different
analytic steps into one slogan.

## 11. Chapter VI.2: Continuing the Estimates

Once `(4.5)` holds on the real domain, the paper packages the continued
functions as taking values in Banach spaces of spatial-variable functions with
polynomial weights.

Then it repeats the induction:
- define `S_{k,ε}` with a compensating denominator;
- use the `(P_N)` scalar-product representation and previously obtained bounds
  to prove estimates on the boundary of the next domain;
- apply the maximum principle to extend those estimates to the entire enlarged
  domain.

This is conceptually cleaner than VI.1:
- no new analyticity theorem is proved here;
- only the bounds are propagated along the Chapter V continuation ladder.

That distinction should be maintained in the repo's proof decomposition.

### 11.1. Exact proof chain of VI.2

The paper's proof of VI.2 can be decomposed into the following explicit steps.

1. Define the Banach spaces `B_{k,t}` by the weighted sup norm `(6.19)` in the
   spatial variables.
2. Regard `S_k(ζ^0 | ·)` as a function of the time variables with values in
   that Banach space.
3. Record the real-domain estimate `(6.20)` coming from VI.1.
4. For `ε > 0`, define the renormalized family `S_{k,ε}` by dividing by a
   compensating factor as in `(6.21)`.
5. Use `(P_N)` and Cauchy-Schwarz to obtain the Banach-valued scalar-product
   estimate `(6.22)` on mixed domains.
6. Convert `(6.22)` into the renormalized estimate `(6.23)`.
7. Verify the purely algebraic inequalities `(6.24)`-`(6.27)` needed in that
   conversion.
8. Apply the induction hypothesis to the lower-order factors on the right-hand
   side of `(6.23)`, obtaining `(6.29)`.
9. Use the maximum principle on the envelope-of-holomorphy domain to propagate
   the estimate from the generating region to all of `C_k^(M+1)`.
10. Eliminate the dependence on `N` using Corollary 5.3 and the choice rule
    `(6.30)`.
11. Undo the renormalization to reach `(6.31)`, i.e. the final estimate
    `(4.6)`.

This is a fully closed induction. There is no hidden new analyticity theorem in
VI.2; only a carefully normalized maximum-principle argument.

### 11.1.1. Detailed derivation of `(6.22)` and `(6.23)`

The estimate `(6.22)` comes directly from `(P_N)` and the Banach-space norm:

1. `(P_N)` writes `S_k(\bar ζ, 2x, ζ')` as the scalar product
   `(Ψ_n(x,ζ), Ψ_m(x,ζ'))`.
2. Apply Cauchy-Schwarz in the Hilbert space.
3. Interpret the result as a pointwise bound in the spatial variables.
4. Take the weighted supremum over the spatial variables to obtain a bound in
   the Banach norm `‖·‖_p`.

Then `(6.23)` is obtained by inserting the renormalization factor from
`S_{k,ε}`. The only extra work is to verify that the denominator splits in a
way compatible with the decomposition `k = n + m - 1`. That is exactly the role
of `(6.24)` and `(6.25)`.

So the structure is:
- `(P_N)` gives a Hilbert-space factorization,
- the renormalization turns that factorization into a multiplicative Banach
  estimate.

### 11.1.2. Detailed role of `(6.29)`

The estimate `(6.29)` is the actual induction-closing inequality. It is
obtained by:

1. applying the induction hypothesis separately to the lower-order factors
   `S_{2n-1,ε}` and `S_{2m-1,ε}`,
2. multiplying the resulting bounds,
3. simplifying the exponents using the normalization identities already
   established.

This is the point where the lower-order information is lifted to the
next-stage domain. Everything after `(6.29)` is propagation by the maximum
principle; everything before it is algebraic preparation.

### 11.2. Why the renormalized family `S_{k,ε}` is necessary

The denominator in `(6.21)` is not a technical nuisance. It is what makes the
induction compatible with the convexity estimates `(6.24)`-`(6.27)`.

Its role is:
- compensate for the growth in the real parts of the time variables,
- make the boundary estimates multiplicative under the `(P_N)` scalar-product
  decomposition,
- and allow the lower-order induction hypothesis to close.

So if one later formalizes VI.2, the renormalized family should be treated as a
central object, not as a convenience wrapper.

### 11.3. The algebraic heart: `(6.24)`-`(6.27)`

The inequalities `(6.24)`-`(6.27)` are where the normalization is proved to be
compatible with the decomposition `k = n + m - 1`.

The paper reduces both required inequalities to the convexity of the function
`x ↦ ln x`. Concretely:

- `(6.24)` is a weighted geometric-arithmetic mean type estimate for the real
  parts of the time variables;
- `(6.25)` is the corresponding estimate for the epsilon-regularization factor;
- `(6.27)` is the common convexity template from which both follow.

Thus the later Lean proof should isolate these as explicit analytic inequalities
on positive reals, not bury them in ring/algebra manipulations inside the main
induction theorem.

### 11.4. Eliminating `N` via Corollary 5.3

The last step of VI.2 is often under-emphasized. The induction gives an
estimate on `C_k^(N)` that still visibly depends on `N`. To get the final
statement, the paper:

1. fixes a target point `ζ ∈ C_+^k`,
2. chooses an index `s` so that `|arg ζ_r| ≤ |arg ζ_s|` for all `r`,
3. chooses `N = N(ζ)` so that Corollary 5.3 guarantees `ζ ∈ C_k^(N)`,
4. inserts that choice into `(6.28)`,
5. uses the explicit bound on `γ_k` from `(5.28)`,
6. then undoes the Banach norm and the `ε`-shift.

So the final estimate `(6.31)` is not an abstract consequence of the induction.
It depends quantitatively on the explicit domain-growth control from Chapter V.

### 11.4.1. Exact recovery chain from the normalized family back to the
original distributions

The phrase "undo the renormalization" hides a real theorem package. A later
Lean port should expose the following exact recovery chain:

```lean
lemma normalized_family_agrees_with_original_on_stage
    (ζ : CkN N) (ε : ℝ) (hε : 0 < ε) :
    S_{k,ε} ζ = renormFactor k ε ζ * S_k (stageShift ε ζ)

lemma normalized_family_estimate_imported_from_VI1
    (ζ : CkN N) :
    ‖S_{k,ε} ζ‖ ≤ stageBound k N ζ

lemma stage_selection_for_target_configuration
    (ζ : CPlus k) :
    ∃ N, ζ ∈ CkN N

lemma estimate_descends_from_selected_stage
    (ζ : CPlus k) :
    ‖S_{k,ε} ζ‖ ≤ selectedStageBound k ζ

lemma epsilon_limit_exists_for_normalized_family
    (ζ : CPlus k) :
    Tendsto (fun ε : ℝ => S_{k,ε} ζ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (boundaryCandidate k ζ))

lemma epsilon_limit_matches_original_distribution
    (ζ : CPlus k) :
    Tendsto (fun ε : ℝ => renormFactor k ε ζ * S_k (stageShift ε ζ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (boundaryCandidate k ζ))

lemma recovered_boundary_value_is_tempered
    (k : ℕ) :
    TemperedDistributionBoundaryValue (boundaryCandidate k)

theorem vi2_temperedness_and_boundary_recovery
    (k : ℕ) :
    FinalChapterVI2Conclusion k
```

The roles are:

1. algebraic comparison with the original family,
2. import the fixed-stage estimate,
3. choose a stage using Corollary 5.3,
4. remove the visible `N`-dependence,
5. take the `ε -> 0` boundary limit,
6. identify the limit with the original distributions,
7. package the result as tempered boundary-value recovery.

Without those items, VI.2 is still only a proof sketch. With them, the later
Lean file can be organized as an explicit recovery package.

### 11.5. Why VI.2 is still tied to Chapter V

VI.2 may look like a pure estimate-propagation theorem, but it still depends on
Chapter V in two essential ways:

1. the domain `C_k^(N)` is defined through the Chapter V induction;
2. Corollary 5.3 supplies the quantitative exhaustion of the full right
   half-plane by those domains.

So the papers do not prove continuation first and then forget the continuation
domains. The estimates are literally propagated along the same domains that
were created in the continuation proof.

## 12. Appendix: `E0'' => E0'`

The appendix proves the stronger pointwise/distribution condition `E0''`
implies the linear growth condition `E0'` by Hermite expansion.

This is mostly auxiliary for the current frontier, but it reveals a useful
pattern:
- when one has strong pointwise control, Hermite coefficients convert it into
  Schwartz seminorm bounds with explicit order growth.

So if a future Lean route temporarily obtains an `E0''`-style theorem, the
appendix explains how to reconnect it to the official `E0'` surface.

### 12.1. Exact proof chain of the appendix

The appendix proves:
- pointwise/derivative control `E0''` on Schwartz test functions implies
  the linear-growth seminorm estimate `E0'`.

The proof is:

1. Expand the distribution `T` in the Hermite basis:
   `T = Σ T_i H_i`.
2. Express `T(g)` as `Σ T_i γ_i`, where `γ_i = ∫ H_i g`.
3. Apply Cauchy-Schwarz, obtaining `(A3)`.
4. Bound the Hermite coefficients `T_i` using the assumed `E0''` estimate and
   Sobolev control on Hermite functions; this yields `(A5)`.
5. Bound the coefficients `γ_i` by repeated action of the harmonic-oscillator
   operator `(1 + x^2 - d^2/dx^2)` on `g`; this yields `(A6)`.
6. Choose the exponent `s = r + 1` so that the weighted Hermite series in
   `(A3)` converges uniformly.
7. Combine the bounds to obtain `(A2)`, i.e. `E0'`.

So the appendix is really a spectral estimate for the harmonic oscillator in
disguise.

### 12.1.1. Detailed derivation of `(A3)`-`(A6)`

The appendix proof is short, but it contains three separate estimates.

First estimate: `(A3)` by Cauchy-Schwarz
1. Expand `T(g)` in the Hermite basis.
2. Insert the weights `(1+i)^s` and `(1+i)^{-s}`.
3. Apply Cauchy-Schwarz.
4. This produces two factors:
   - the coefficient factor involving `T_i`,
   - the test-function factor involving `γ_i`.

Second estimate: `(A5)` for `T_i`
1. Express `H_i` in terms of creation/annihilation operators.
2. Use Sobolev inequality to control the supremum norm of derivatives of
   Hermite functions.
3. Apply the `E0''` hypothesis `(A1)` to those derivatives.
4. Conclude a polynomial bound in the Hermite index `i`.

Third estimate: `(A6)` for `γ_i`
1. Apply the harmonic-oscillator operator repeatedly to `g`.
2. Use the fact that `H_i` is an eigenfunction of that operator.
3. Shift the powers of `(1+i)` from the Hermite basis onto derivatives of `g`.
4. Bound the result by a Schwartz seminorm `|g|_{n,t}`.

The final step is to choose `s = r+1` so that the weighted Hermite-coefficient
series converges uniformly. Then multiplying `(A5)` and `(A6)` inside `(A3)`
gives the desired estimate `(A2)`.

So the appendix really has the same pattern as VI.1:
- isolate coefficients,
- estimate one factor by structural spectral information,
- estimate the other by Schwartz seminorm control,
- then reassemble.

### 12.2. Why the appendix matters for formalization

The point of the appendix is not merely historical. It gives a robust template:

- strong pointwise/derivative control,
- orthogonal expansion,
- coefficient decay,
- then recovery of Schwartz seminorm bounds.

This pattern is exactly the kind of route one might later use in Lean if a
stronger theorem surface appears first and must be converted back to the
official `E0'` format.

## 13. What This Imposes on the Current Lean Frontier

### 13.1. Theorem-shape discipline

The live `E -> R` development should prefer the following theorem shapes:

1. one-gap semigroup matrix-element theorem with parameters,
2. local analyticity / domain-enlargement theorem,
3. VI.1 regularization-and-bound theorem,
4. boundary-value extraction theorem.

It should avoid:
- direct many-gap continuation from separate one-gap facts,
- same-test-function Euclidean/Wightman identities,
- operator-theoretic shortcuts that bypass the semigroup-to-boundary-value
  object,
- reductions that change the seam without making it more honest.

### 13.2. Meaning for the current `k = 2` / theorem-3 lane

For `k = 2`, there is only one true time-difference variable. The OS II reading
therefore suggests:
- the correct scalar object is already one-variable,
- all remaining complications are parameter packaging and matching of shell
  representatives,
- the missing theorem should look like an Input-A / fixed-time extension /
  difference-variable bridge, not like a generic many-variable continuation
  theorem.

This is exactly why the current project's `K2VI1` and route-1 language is not
off-paper. It is a Lean implementation of the OS "treat all other variables as
parameters" philosophy.

### 13.3. Meaning for theorem 3 in `OSToWightmanBoundaryValues`

The current theorem-3 seam should be read as a local version of:
- identify the correct one-variable scalar continuation object,
- prove the corresponding fixed-time common/probe or common/explicit shell
  comparison,
- then transport positivity through the already-built reduction chain.

What OS II does not support is:
- repeated abstract reductions with no closure,
- proving positivity by comparing unrelated Euclidean and Minkowski pairings on
  the same literal test function,
- using continuity/uniqueness on too large a domain without first proving the
  correct local analyticity and extension package.

### 13.4. Current theorem-3 state after the latest scratch corrections

The most current scratch state in the repo is more modest than some recent
`agents_chat` optimism suggested.

What is genuinely proved in `test/proofideas_bvt_route1_semigroup_strip.lean`:
- the explicit descended `bvt_F` kernel matches the theorem-3 semigroup shell
  on the positive strip;
- this lifts to integral identities for positive-support tests;
- the strengthened common fixed-time kernel and common zero-center section have
  the same positive-support pairings as that explicit descended kernel.

What is *not* currently proved there:
- a pointwise equality theorem on the whole positive-time strip.

Why the stronger claim was removed:
- the attempted pointwise upgrade incorrectly treated the descended absolute
  forward-tube input as if it were already defined and continuous on a domain
  larger than the reduced forward tube.

So the documentation-standard current reading is:
- the functional-level bridge is real progress;
- the pointwise strip equality is not yet part of the trusted scratch state;
- any future port-to-production plan must begin by repairing that domain issue,
  not by assuming the pointwise theorem already exists.

### 13.5. Exact theorem shape still missing for theorem 3

Combining OS II with the current repo state, the missing theorem should be read
as follows.

Input:
- a one-variable common kernel supplied by the strengthened `K2VI1` /
  `InputA*` package;
- the explicit descended `bvt_F` kernel already identified with the semigroup
  shell on positive-support pairings.

Goal:
- prove the two kernels agree on the exact local positive-time domain where the
  boundary-value reduction needs them.

Acceptable proof shapes:
1. a fixed-time / partial-boundary-value extension theorem on the common kernel,
2. a uniqueness theorem on the correct one-variable domain, once continuity and
   common pairing identities are fully established there,
3. a direct instantiation of the existing `InputAHeadBlockTransport` style
   machinery if it produces the same identification.

Unacceptable proof shapes:
- generic contour-shift slogans with unchanged test function,
- direct operator equalities `e^{-tH} = e^{itH}` or similar circular rewrites,
- further reduction lemmas that merely rename the same missing bridge.

## 14. Recommended Operational Use

Before changing a live `E -> R` theorem surface, ask:

1. Is this a Chapter V continuation statement or a Chapter VI estimate
   statement?
2. If it is Chapter V, where is the one distinguished continuation variable and
   where are the packaged parameters?
3. If it is Chapter VI, where is the regularized object and where is the
   Hilbert-space norm estimate?
4. If neither answer is clear, stop and document the missing paper theorem slot
   before proceeding.

## 15. Bottom Line

OS II is not merely a correction of one bad lemma. It is a disciplined proof
architecture.

The main architectural rules are:
- one-variable continuation first,
- parameters fixed throughout,
- many-variable continuation only through the induction ladder,
- growth only after regularization,
- boundary values only after growth.

Those rules should be treated as binding route guidance for the Lean
formalization until a fully proved alternative theorem surface exists in the
repository.

For the implementation dependency graph extracted from these theorem-slot
inventories, see `docs/general_k_continuation_blueprint.md`.

## Appendix A. Lean-Pseudocode Skeletons for OS II

This appendix is deliberately implementation-shaped. The statements below are
not intended to compile as-is, but they are meant to be close enough to the
actual mathematical proof that later Lean porting becomes straightforward.

They should be read as theorem-slot inventories, not as optional sketches. Each
slot corresponds to a mathematically real proof obligation in the paper.

### A.1. Local analyticity radius from Chapter V.1

Mathematical content:
- fix a real positive-time point `ξ`;
- choose the cone angle `γ` and dual vectors `e_μ`;
- obtain an explicit polydisc `Γ(ξ)` from Lemma 5.1.

Lean pseudocode:

```lean
/-- OS II Lemma 5.1: quantitative local polydisc of analyticity. -/
theorem local_polydisc_of_real_positive_time
    (ξ : TimeDiffConfig k)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    ∃ ρ > 0,
      IsHolomorphicOn
        (fun ζ => S_k (ξ + ζ))
        (polydisc (0 : TimeDiffConfig k) ρ) := by
  -- 1. choose γ from the ratio min ξ_i^0 / |ξ_i|
  -- 2. in the paper, build e_1,...,e_4 in the dual cone;
  --    for the repo's general-`d` implementation, use d+1 dual-cone vectors
  -- 3. use directional one-variable continuation in each e_μ direction
  -- 4. glue by Malgrange-Zerner
  -- 5. extract the explicit radius from the coordinate inequalities
```

Local sublemmas later Lean will need:
- `cone_angle_from_positive_time`,
- `dual_cone_basis_exists`,
- `directional_semigroup_continuation`,
- `malgrange_zerner_glue_flat_tubes`,
- `explicit_radius_from_coordinate_estimates`.

More explicit theorem-slot inventory for A.1:

```lean
lemma cone_angle_from_positive_time
    (ξ : TimeDiffConfig k)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    ∃ γ > 0, admissibleConeAngle ξ γ := by
  -- choose `γ` so that each positive real time component of `ξ` dominates the
  -- allowed angular variation

lemma dual_cone_basis_exists
    (hγ : admissibleConeAngle ξ γ) :
    ∃ e : Fin (d + 1) → TimeDiffConfig k,
      dualConeBasisFor hγ e := by
  -- this is the finite-direction geometry behind `(5.10)`-`(5.14)`

lemma directional_semigroup_continuation
    (hξ : ξ ∈ positiveRealTimeRegion)
    (he : dualConeDirection ξ γ eμ) :
    IsHolomorphicOn
      (fun u : ℂ => S_k (ξ + u • eμ))
      rightHalfPlane := by
  -- apply the OS I one-gap semigroup theorem in the chosen direction

lemma malgrange_zerner_glue_directional_pieces
    (hdir : ∀ μ, directionalContinuationData μ) :
    ∃ F, IsHolomorphicOn F (localTubeDomain ξ γ) := by
  -- glue the flat-tube continuations on overlaps by Malgrange-Zerner

lemma explicit_radius_from_coordinate_estimates
    (hF : IsHolomorphicOn F (localTubeDomain ξ γ)) :
    ∃ ρ > 0, polydisc (0 : TimeDiffConfig k) ρ ⊆ localTubeDomain ξ γ := by
  -- extract the quantitative radius from the coordinate inequalities in Lemma
  -- 5.1
```

These five theorem slots are the exact proof skeleton of Lemma 5.1. The
general A.1 theorem should be regarded as a thin wrapper around them.

### A.2. The `(A_N) -> (P_N)` vector reconstruction step

Mathematical content:
- choose a real basepoint `ξ` and a polydisc inside `D_n^(N)`;
- define the vector-valued Taylor series;
- prove norm convergence via scalar-product remainders.

Lean pseudocode:

```lean
/-- OS II `(A_N) -> (P_N)`: reconstruct a Hilbert-valued analytic vector
from scalar analyticity on a mixed domain. -/
theorem hilbert_vector_from_scalar_taylor
    (hA : ScalarContinuationOn DnN)
    (x : ℝ)
    (ζ : TimeVector (n - 1))
    (hxζ : (x, ζ) ∈ DnN) :
    ∃ Ψ : HilbertSpaceVector,
      HasStrongTaylorExpansionAt
        (fun w => PsiField n x w)
        Ψ ζ := by
  -- 1. choose a real point ξ and radii r_i with closed polydisc ⊆ DnN
  -- 2. define the formal Taylor series in Hilbert space
  -- 3. compute the squared norm of the remainder via scalar products
  -- 4. identify that scalar remainder with a scalar Taylor remainder
  -- 5. use scalar analyticity to conclude norm convergence
```

The key hidden theorem to formalize is the remainder identity:

```lean
lemma hilbert_remainder_norm_sq_eq_scalar_remainder
    (ξ : TimeVector (n - 1))
    (r : MultiRadius (n - 1))
    (hpolydisc : closedPolydisc ξ r ⊆ DnN)
    (N : ℕ) :
    ‖vectorTaylorRemainder (Ψn := Ψ_n) ξ r N‖^2 =
      scalarTaylorRemainder
        (fun z => S_(2 * n - 1) (-conj z, 2 * x, z)) ξ r N := by
  -- expand the squared norm as an inner product of remainder vectors,
  -- replace all scalar products by `(5.17)`,
  -- observe that the resulting double sum is exactly the scalar Taylor
  -- remainder of `S_{2n-1}(-\bar ζ, 2x, ζ)`
```

Without that lemma, `(A_N) -> (P_N)` is not a proof, only a slogan.

Additional theorem-slot inventory for A.2:

```lean
lemma real_polydisc_inside_mixed_domain
    (hxζ : (x, ζ) ∈ DnN) :
    ∃ ξ r, closedPolydisc ξ r ⊆ DnN := by
  -- choose the real basepoint and coordinate radii used in the paper

lemma scalar_derivatives_control_hilbert_derivatives
    (hA : ScalarContinuationOn DnN)
    (hpolydisc : closedPolydisc ξ r ⊆ DnN) :
    ∀ α, derivativeScalarProductFormula α := by
  -- differentiate `(5.17)` at the real basepoint

lemma vector_taylor_series_norm_converges
    (hA : ScalarContinuationOn DnN)
    (hrem :
      ∀ N, ‖vectorTaylorRemainder (Ψn := Ψ_n) ξ r N‖^2 =
        scalarTaylorRemainder (fun z => S_(2 * n - 1) (-conj z, 2 * x, z)) ξ r N) :
    ∃ Ψ, HasStrongTaylorExpansionAt (fun w => PsiField n x w) Ψ ζ := by
  -- use scalar analyticity of `S_{2n-1}` to make the scalar remainder tend to
  -- zero, hence the vector remainder tends to zero in norm
```

This is the exact mathematical content of `(A_N) -> (P_N)`: one geometric
polydisc lemma, one differentiated scalar-product identity, and one norm
convergence theorem.

### A.3. The `(P_N) -> (A_{N+1})` scalar-product continuation step

Mathematical content:
- form scalar products of the already-continued `Ψ`-vectors;
- read them as values of `S_k` on a union of tube-like sets;
- extend to the envelope of holomorphy, using the SCV/tube-domain input
  hidden in the paper's definition of `Ck^(N+1)`.

Lean pseudocode:

```lean
/-- OS II `(P_N) -> (A_{N+1})`: scalar continuation from Hilbert vectors. -/
theorem scalar_continuation_from_hilbert_vectors
    (hP : VectorContinuationOn DnN)
    (k : ℕ) :
    ScalarContinuationOn (Ck (N + 1)) := by
  -- 1. define the scalar candidate by
  --    `(Ψ_n(x, ζ), Ψ_m(x', ζ'))` on the mixed domain with `k = n + m - 1`
  -- 2. show agreement with the old real slice
  -- 3. obtain analyticity on the generating union of mixed domains
  -- 4. extend to the envelope of holomorphy using the tube-domain envelope
  --    theorem packaged into the domain definition
```

Explicit theorem-slot inventory for A.3:

```lean
lemma scalar_candidate_from_vector_pairing
    (hP : VectorContinuationOn DnN)
    (hnm : k = n + m - 1) :
    ∃ Fnm,
      ∀ (x ζ x' ζ'),
        Fnm (x, ζ, x', ζ') = inner (Ψ_n x ζ) (Ψ_m x' ζ') := by
  -- define the scalar candidate on the mixed-domain generators

lemma scalar_candidate_agrees_on_real_slice
    (hP : VectorContinuationOn DnN)
    (hFnm : scalarCandidateData Fnm) :
    Fnm.restrictToRealSlice = oldSchwingerData := by
  -- this is the real-slice content of `(5.17)`

lemma scalar_candidate_holomorphic_on_generating_union
    (hP : VectorContinuationOn DnN)
    (hFnm : scalarCandidateData Fnm) :
    IsHolomorphicOn Fnm (generatingMixedUnion (N := N) (k := k)) := by
  -- holomorphy in each vector block gives holomorphy on the generating union

lemma scalar_candidate_extends_to_envelope
    (hFnm_holo : IsHolomorphicOn Fnm (generatingMixedUnion (N := N) (k := k))) :
    ∃ Fk, IsHolomorphicOn Fk (Ck (N + 1)) := by
  -- use the tube-domain / logarithmic-tube envelope theorem behind the
  -- definition of `Ck^(N+1)`

lemma generating_union_has_required_envelope
    :
    EnvelopeOfHolomorphy (generatingMixedUnion (N := N) (k := k)) (Ck (N + 1)) := by
  -- this is the SCV input hidden in the paper's domain definition
```

This is the exact proof structure of `(P_N) -> (A_{N+1})`: define the scalar
candidate, identify its real slice, prove holomorphy on the generating union,
then invoke the envelope definition.

The important point is that this is not a free abstract SCV step. The domains
here are tube / logarithmic-tube type domains, so the later Lean port should
either import the corresponding Bochner-style envelope theorem or package the
domains so that the envelope extension is already part of their definition.

### A.4. Chapter VI.1 regularization package

Mathematical content:
- construct `g_ρ`, `k_ρ`, and `T_k`;
- bound `S_k` by a supremum of `T_k`;
- rewrite `T_k` as a scalar product.

Lean pseudocode:

```lean
/-- Complexified Euclidean spacetime in general dimension `d+1`. -/
abbrev ComplexSpacetime (d : ℕ) := Fin (d + 1) → ℂ

/-- `k` complexified spacetime blocks. -/
abbrev ComplexSpacetimeBlocks (d k : ℕ) := Fin k → Fin (d + 1) → ℂ

/-- Auxiliary radial mollifier used in OS II VI.1. -/
def radialMollifier (ρ : ℝ) : ComplexSpacetime d → ℝ :=
  -- `g_ρ(z) = c ρ^{-2(d+1)} h_ρ(|z|)` where the radial scaling is fixed so
  -- that:
  -- 1. `supp g_ρ ⊆ {|z| < ρ/8}`,
  -- 2. the convolution kernel `k_ρ = g_ρ * g_ρ` satisfies
  --    `supp k_ρ ⊆ {|z| < ρ/4}`,
  -- 3. the normalization from `(6.2)` holds in complex dimension `d+1`
  scaledRadialBump ρ

/-- Convolution kernel `k_ρ = g_ρ * g_ρ`. -/
def regularizingKernel (ρ : ℝ) : ComplexSpacetime d → ℝ :=
  convolutionKernelFrom radialMollifier ρ

/-- The regularized analytic object `T_k`. -/
def regularizedSchwinger
    (ρ : ℝ) (ξ : TimeDiffConfig k) : ComplexSpacetimeBlocks d k → ℂ :=
  -- the `T_k` of `(6.5)`: integrate the shifted Schwinger function against the
  -- product kernel built from `g_ρ` and `k_ρ`
  regularizedSchwingerIntegral ρ ξ

theorem schwinger_eq_average_of_regularized
    (hρ : 0 < ρ)
    (hζ : ζ ∈ smallPolydisc ρ) :
    S_k (ξ + ζ) =
      ∬ regularizedSchwinger ρ ξ (ζ + i * y')
          ∂μ := by
  -- mean-value theorem + support of the kernels + Fubini

theorem abs_schwinger_le_sup_regularized
    (hρ : 0 < ρ)
    (hζ : ζ ∈ smallPolydisc ρ) :
    ‖S_k (ξ + ζ)‖ ≤
      supOn (smallImaginaryBox ρ) (fun y => ‖regularizedSchwinger ρ ξ (i * y)‖) := by
  -- rewrite `S_k` as the double average from `(6.6)`,
  -- take absolute values,
  -- dominate the average by the supremum of the regularized kernel on the
  -- support box from `(6.7)`

theorem regularized_eq_hilbert_pairing
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion)
    (hdir : μ ∈ Fin 4) :
    regularizedSchwinger ρ ξ (u • e_μ) =
      inner Ψ₁ Ψ₂ := by
  -- choose the vectors `Ψ₁`, `Ψ₂` exactly as in `(6.10)`,
  -- use Euclidean covariance to rewrite the regularized integral,
  -- identify the resulting expression with the OS Hilbert-space scalar product
```

Explicit theorem-slot inventory for A.4:

```lean
lemma radial_bump_exists_with_osii_normalization :
    ∃ h : ℝ → ℝ,
      radialBumpData h := by
  -- this is the input behind `(6.2)`

lemma regularizingKernel_support_and_mass
    (hρ : 0 < ρ) :
    supportAndMassData (regularizingKernel (d := d) ρ) := by
  -- compact support and total mass 1 of `k_ρ`

lemma schwinger_mean_value_identity
    (hρ : 0 < ρ)
    (hζ : ζ ∈ smallPolydisc ρ) :
    S_k (ξ + ζ) =
      doubleAverageOfRegularizedKernel (regularizedSchwinger (d := d) ρ ξ) ζ := by
  -- this is `(6.6)` after the mean-value and Fubini manipulations

lemma regularized_pairing_vectors_exist
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion)
    (hdir : μ ∈ Fin 4) :
    ∃ Ψ₁ Ψ₂,
      regularizedSchwinger (d := d) ρ ξ (u • e_μ) = inner Ψ₁ Ψ₂ := by
  -- explicit OS Hilbert-space vectors from `(6.10)`
```

So A.4 really has four independent proof packages:
1. build the radial bump,
2. prove the support/mass bookkeeping,
3. derive the mean-value / average identity,
4. convert the regularized kernel to an OS Hilbert pairing.

### A.5. Chapter VI.1 norm estimate and propagation

Mathematical content:
- estimate the Hilbert vectors via `E0'`;
- continue in finitely many directions;
- propagate bounds by maximum principle.

Lean pseudocode:

```lean
theorem regularized_hilbert_norm_bound
    (hE0' : LinearGrowthCondition)
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    ‖Ψ₁‖ * ‖Ψ₂‖ ≤
      C k * (1 + euclideanSize ξ)^M * ρ^(-M') := by
  -- geometric estimate (6.9) + `E0'`

theorem directional_bound_for_regularized
    (hE0' : LinearGrowthCondition)
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    ∀ u ≥ 0, ‖regularizedSchwinger ρ ξ (u • e_μ)‖ ≤ bound ξ ρ := by
  -- semigroup matrix-element bound

theorem local_polydisc_bound_from_directional_bounds
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion)
    (hdir : ∀ μ, directionalBound μ) :
    ∀ ζ ∈ smallPolydisc ρ, ‖regularizedSchwinger ρ ξ ζ‖ ≤ bound ξ ρ := by
  -- continue in each of the four dual-cone directions,
  -- glue the directional functions by Malgrange-Zerner,
  -- transfer the directional bounds to the full polydisc by the maximum
  -- principle on the envelope of holomorphy

theorem real_domain_temperedness_estimate
    (hE0' : LinearGrowthCondition) :
    ∃ C M, ∀ ξ ∈ positiveRealTimeRegion,
      ‖S_k ξ‖ ≤ C k * (1 + euclideanSize ξ)^M := by
  -- combine `(6.6)`-`(6.7)` with the bound on the regularized kernel,
  -- then rewrite the resulting estimate into the polynomial-growth format
  -- `(4.5)`
```

Explicit theorem-slot inventory for A.5:

```lean
lemma regularizer_support_bounds
    (hρ : 0 < ρ) :
    supportBoundsForRegularizingVectors ρ := by
  -- this is the geometric content of `(6.17)` and `(6.18)`

lemma regularizer_derivative_bounds
    (hρ : 0 < ρ) :
    derivativeBoundsForRegularizers ρ := by
  -- this is the `C_0^∞` control from `(6.2)` and `(6.3)`

lemma e0prime_norm_bound_for_regularized_vectors
    (hE0' : LinearGrowthCondition)
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    regularizedVectorNormBound ρ ξ := by
  -- apply `E0'` to the explicit test functions appearing in `(6.17)`

lemma directional_regularized_bound
    (hE0' : LinearGrowthCondition)
    (hρ : 0 < ρ)
    (hξ : ξ ∈ positiveRealTimeRegion) :
    ∀ μ, directionalBoundForRegularizedKernel μ := by
  -- combine the semigroup matrix-element estimate with the norm bounds

lemma local_bound_from_directional_bounds
    (hdir : ∀ μ, directionalBoundForRegularizedKernel μ) :
    localRegularizedKernelBound := by
  -- this is `(6.13)`-`(6.15)` plus the logarithmic-coordinate / maximum
  -- principle step

lemma real_domain_estimate_from_local_bound
    (hlocal : localRegularizedKernelBound) :
    realDomainTemperedEstimate := by
  -- this is `(6.7)` plus the coordinate unrolling yielding `(6.16)`
```

This is the exact structure of VI.1:
1. support bounds,
2. derivative bounds,
3. `E0'` norm estimate,
4. directional regularized bounds,
5. glued local bound,
6. real-domain estimate.

### A.5.1. Exact dependency chain for `(6.12)`-`(6.18)`

The later Lean port should treat the displayed VI.1 inequalities as a genuine
dependency chain rather than as one large estimate:

```lean
lemma support_bound_implies_test_function_localization
lemma localization_implies_E0prime_applicable
lemma E0prime_applied_to_regularized_test_functions
lemma regularized_vector_norm_bound_from_E0prime
lemma scalar_pairing_bound_from_vector_norms
lemma directional_bound_from_scalar_pairing_bound
lemma local_polydisc_bound_from_directional_maximum_principle
lemma real_domain_bound_from_mean_value_identity
```

The mathematical order is:

1. `(6.17)`-`(6.18)` localize the explicit test functions;
2. localization allows the `E0'` seminorm estimate;
3. `E0'` bounds `‖Ψ₁‖` and `‖Ψ₂‖`;
4. Cauchy-Schwarz bounds the scalar pairing `T_k`;
5. directional bounds feed the maximum-principle step;
6. the mean-value identity converts the regularized bound into the raw bound.

If a later Lean proof skips any one of those arrows, the docs should be
updated first rather than letting the hidden step reappear inside a large proof
term.

### A.6. The current theorem-3 lesson extracted from OS II

For the repo's current `k = 2` frontier, the paper suggests the following
implementation-shaped target:

```lean
/-- Domain used by the current theorem-3 pairing theorems. -/
def positiveTimeRegion : Set (Spacetime d) := {ξ | 0 < ξ 0}

/-- Desired theorem shape for the remaining theorem-3 bridge. -/
theorem k2_fixed_time_boundary_value_bridge
    (commonKernel explicitKernel : Spacetime d → ℂ)
    (hcommon_cont : ContinuousOn commonKernel positiveTimeRegion)
    (hexplicit_cont : ContinuousOn explicitKernel positiveTimeRegion)
    (hpair :
      ∀ h : SchwartzSpacetime d,
        HasCompactSupport (h : Spacetime d → ℂ) →
        tsupport (h : Spacetime d → ℂ) ⊆ positiveTimeRegion →
          ∫ ξ, commonKernel ξ * h ξ =
          ∫ ξ, explicitKernel ξ * h ξ) :
    EqOn commonKernel explicitKernel positiveTimeRegion := by
  -- apply
  -- `eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local`
  -- on the open set `{ξ | 0 < ξ 0}` after proving:
  -- 1. both kernels are restrictions of genuinely defined strip kernels,
  -- 2. both are continuous there,
  -- 3. the pairing theorem quantifies over all compactly supported tests in
  --    `{ξ | 0 < ξ 0}` and not merely over one shell family
```

The note above is intentionally conditional. At the time of writing, the repo
does not yet have all those hypotheses in trusted form for the current common
kernel / descended-`bvt_F` comparison. That is exactly the remaining theorem-3
work.
