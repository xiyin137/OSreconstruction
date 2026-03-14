# OS Reconstruction Reading Notes

These notes summarize the parts of Osterwalder-Schrader I and II that are
actually relevant to the current Lean development, with emphasis on the
`E -> R` direction and the current blocker surface.

Primary local references:

- `references/Reconstruction theorem I.pdf`
- `references/reconstruction theorem II.pdf`

This note is intentionally theorem-focused. It is not a full paper summary.

## 1. High-level picture

The OS reconstruction papers do not proceed by solving the two-point case and
then inferring all `k`-point functions by a formal induction on `k`.

Instead, the core analytic mechanism is:

1. pass to difference-variable Schwinger functions,
2. construct a Hilbert space and a positive self-adjoint semigroup from OS
   positivity,
3. continue in one time variable at a time using semigroup matrix elements,
4. treat all remaining variables as parameters,
5. then iterate this one-variable continuation mechanism.

That is the key conceptual bridge from the current `k = 2` work to the general
base-step theorem.

## 1.1. Paper notation dictionary

The papers use several notation layers that are easy to blur together. The
following dictionary is the one we actually need in Lean work.

- `𝒮_n`
  Euclidean `n`-point Green's functions in the original point variables
  `(x₁, ..., x_n)`.

- `S_n`
  difference-variable Euclidean Green's functions. These are obtained from
  translation invariance by passing from point variables to successive
  differences. In current Lean language, this is the natural world of
  admissible time-ordered / difference-variable shells.

- `W_n`
  difference-variable Wightman distributions, obtained after Fourier-Laplace
  continuation and support control.

- `Ψ_n(x, ξ)`
  Hilbert-space-valued distributions built from the OS form. These are the
  bridge between Schwinger functions and the semigroup.

- `T_t = e^{-tH}`
  the self-adjoint contraction semigroup on the OS Hilbert space.

- `T_τ`
  the holomorphic extension of the semigroup for `Re τ > 0`.

- `S^(m)(t,s | h_m)`
  the key parameterized one-gap continuation object in OS I. The point is:
  the variable being analytically continued is isolated, while all other
  variables are packaged into the parameter `h_m`.

- `C_+^k`
  product right half-plane in the time variables. OS II emphasizes that this
  full domain is reached only after an inductive continuation procedure, not
  from a naive one-shot argument.

## 1.2. Growth assumptions in OS II

OS II distinguishes three levels of distribution/growth control, and this
distinction matters for how the proof is organized.

- `E0`
  the original temperedness assumption from OS I. This is enough to build the
  semigroup and to obtain one-variable analytic continuation.

- `E0'`
  the linear-growth condition. Roughly, the Euclidean Green's functions are not
  merely tempered distributions, but their order is controlled linearly in the
  number of variables by seminorms of the form `|f|_{ns}` up to a factorially
  growing sequence.

- `E0"`
  a stronger pointwise/distributional growth condition. OS II remarks several
  times that if one were willing to assume `E0"` instead of `E0'`, the later
  temperedness arguments would become much shorter.

The important strategic point is:

- OS II does **not** use `E0'` to produce the analytic continuation itself;
- it uses `E0'` later to prove the polynomial growth / temperedness estimates
  needed for boundary values.

So there is a conceptual split:

- Chapter V:
  continuation, using `E0`, `E1`, `E2`;
- Chapter VI:
  temperedness estimates, using `E0'`.

This is exactly the right mental model for our file split:

- `OSToWightmanSemigroup.lean` and the core continuation side are about the
  analogue of Chapter V;
- `OSToWightmanBoundaryValues.lean` and later growth control are about the
  analogue of Chapter VI.

## 2. OS I: the original `E -> R` mechanism

In OS I, the `E -> R` proof is described in Section 4.

The essential steps are:

1. Construct the pre-Hilbert space from the OS form.
2. Build a one-parameter semigroup `T_t = e^{-tH}` of self-adjoint
   contractions.
3. Extend it to a holomorphic semigroup `T_τ` for `Re τ >= 0`.
4. Use matrix elements of `T_τ` to analytically continue Schwinger functions.
5. Show the continued functions are Fourier-Laplace transforms of
   distributions with the correct support.

This is the origin of the current Lean split:

- `WickRotation/OSToWightmanSemigroup.lean`
- `WickRotation/OSToWightman.lean`
- `WickRotation/OSToWightmanBoundaryValues.lean`

### 2.1. Difference variables come first

OS I does not construct Wightman distributions directly from the raw
point-variable Schwinger functions. The first step is to pass to
difference-variable Schwinger functions `S_n`; see their `(4.1)`.

This matters for us because many of the current Lean difficulties are exactly
about representing the correct difference-variable shell, not about the raw
point-variable objects.

In project terms:

- the current center/difference infrastructure is not accidental extra
  scaffolding;
- it is the Lean reflection of the paper’s decision to do the analytic work in
  difference variables.

### 2.2. The OS Hilbert space and semigroup

The core Hilbert-space construction in OS I is organized around:

- the OS sesquilinear form `(4.3)`,
- the quotient / completion `(4.4)`,
- spatial translation operators `(4.5)`,
- the time-translation semigroup `(4.6)`,
- and the bounds `(4.7)`-`(4.9)` showing this gives a positive symmetric
  contraction semigroup.

The important conceptual point is:

- positivity gives the Hilbert space,
- Euclidean invariance gives the semigroup,
- and the semigroup is the real source of analytic continuation.

This is exactly why `OSToWightmanSemigroup.lean` is the right upstream file for
the whole `E -> R` lane.

### 2.3. One-variable continuation via semigroup matrix elements

OS I then uses matrix elements of the holomorphic semigroup to continue one
time variable. The crucial formulas are `(4.10)` and `(4.11)`.

The structure is:

1. take two positive-time test families `f_m`, `g_n`,
2. form the matrix element
   `⟨ v(f_m), T_{t+is} v(g_n) ⟩`,
3. identify it with a distributional continuation of a Schwinger function,
4. then repackage the remaining variables into the parameter `h_m`.

This is the exact ancestor of the semigroup matrix-element theorems in our
current `OSToWightman*` files.

### The key OS I formula

OS I writes the continuation in one chosen time variable as a semigroup matrix
element. In the text around formula `(4.11)`, they then package the remaining
variables into a parameter `h_m` and define a distribution

- `S^(m)(t, s | h_m)`

for `t > 0`.

For fixed `h_m`, this object:

- is a distribution in the time variables,
- satisfies the Cauchy-Riemann equations,
- and hence is the Fourier-Laplace transform of a distribution in the dual
  cone variable.

This is the part of OS I that most closely matches the current Lean target.

The strongest practical reading of this for our code is:

- the correct target is not just “some holomorphic continuation”;
- it is a continuation produced from a semigroup matrix element after the other
  variables have been packaged as parameters.

That is why our present `k = 2` work is converging toward a factorization
statement rather than yet another shell-specific identity.

### 2.4. The technical lemmas actually used in OS I

The semigroup-to-Fourier-Laplace chain in OS I is mediated by the technical
lemmas in Section 8, and these are worth keeping in mind because they explain
what the proof is *really* using.

- Lemma 8.5:
  a distribution in `(t, s)` satisfying the Cauchy-Riemann equations on
  `t > 0` comes from a holomorphic function `G(τ)` on `Re τ > 0`.

- Lemma 8.6:
  a holomorphic function on `Re τ > 0` with a polynomial bound of the form
  `|G(τ)| ≤ M (1 + |τ|^α) / (Re τ)^β`
  is the Fourier-Laplace transform of a distribution supported in `[0, ∞)`.

- Lemma 8.7:
  combines the previous two statements: a CR distribution on the half-plane is
  already the Fourier-Laplace transform of some positive-support distribution.

- Lemma 8.8:
  this is the problematic multi-variable extension step in OS I. It tries to
  deduce the full many-variable Fourier-Laplace structure from separate
  one-variable statements.

This makes the OS I proof skeleton much more concrete:

1. construct a semigroup matrix element,
2. verify CR equations in one chosen time variable,
3. invoke the one-variable Fourier-Laplace theorem,
4. try to bootstrap to many variables.

The first three steps are robust. The fourth is where OS I overreached.

### 2.5. What exactly went wrong in OS I

The issue is not with the semigroup matrix element itself, nor with the
one-variable holomorphic extension. The issue is that OS I tried to infer the
existence of a joint continuation on the full product half-plane from separate
continuations in each variable.

So when reading OS I operationally, the safe takeaway is:

- one-gap continuation:
  trustworthy;
- joint many-gap continuation from that alone:
  not trustworthy without the extra OS II machinery.

### Important caveat: the famous OS I gap

OS II explicitly states that OS I incorrectly used Lemma 8.8 to continue
simultaneously in all time variables to the full product of right half-planes.

That means the safe reading of OS I is:

- one-variable continuation from semigroup matrix elements is sound,
- simultaneous all-variable continuation requires extra work.

This is why our current base-step should be thought of as a one-gap /
one-variable theorem first, not a full many-variable continuation all at once.

This is the single most important historical warning for current development:

- if a proof sketch seems to jump from one semigroup variable to a full
  `C_+^k` continuation in one move, it is probably recapitulating the old OS I
  gap.

## 3. OS II: the corrected continuation strategy

OS II revisits the `E -> R` direction in Chapters IV and V.

The most important correction is conceptual and explicit:

- continue only in the time variables,
- treat the spatial variables as parameters,
- and build the analytic continuation inductively.

OS II states this very clearly in Chapter V:

- `S_k(ξ) = S_k(ξ^0 | ξ_)`
- the time variables are the analytic variables,
- the spatial variables play the role of parameters.

This is the part of the papers we should be pattern-matching in Lean.

### Theorems 4.1, 4.2, 4.3 in OS II

OS II organizes the continuation into a ladder:

- Theorem 4.1 `(A0)`: real analyticity in a complex neighborhood of real time
  variables, plus temperedness estimates.
- Theorem 4.2 `(A_r)`: continuation to larger open subsets `C_k^(r)` of the
  time-variable domain.
- Theorem 4.3: full continuation on the product right half-plane `C_+^k`,
  still with spatial variables treated parametrically.

Then standard Fourier-Laplace arguments produce the Wightman distributions.

The practical lesson for us is:

- the genuine engine is a one-variable continuation theorem with parameters,
- not an ad hoc many-variable identity theorem on the whole shell.

### 3.1. The inductive structure in OS II

OS II is explicit that the continuation is built inductively.

Their sequence is:

- Theorem 4.1 `(A0)`:
  establish real analyticity near the real domain, together with a temperedness
  estimate.
- Theorem 4.2 `(A_r)`:
  continue to larger open subsets `C_k^(r)`.
- Theorem 4.3:
  obtain analytic continuation on the whole product right half-plane in the
  time variables.

So the actual architecture is:

- local analyticity / one-variable continuation,
- inductive domain enlargement,
- then global Fourier-Laplace extraction.

That should be the default sanity check for our own file structure.

### 3.2. The corrected semigroup formula in OS II

Chapter V of OS II restates the semigroup part in a corrected notation. The
key formulas are `(5.2)`-`(5.4)`.

The conceptual content is:

- `Ψ_n(x, ξ)` packages the parameter variables,
- `e^{-tH}` shifts one time variable,
- the semigroup matrix element defines analytic continuation in the `n`-th
  time variable,
- but only one variable at a time.

The paper then says explicitly that OS I went wrong when it tried to continue
all time variables simultaneously at that stage.

This is very close to the current role of:

- `OSToWightmanSemigroup.lean` for the semigroup matrix element,
- `OSToWightmanTwoPoint.lean` for the first nontrivial parameterized shell
  where we are trying to identify the correct descended parameter object.

### 3.3. How OS II proves real analyticity in practice

OS II, Chapter V, is more concrete than the theorem ladder alone might suggest.
The proof of `(A0)` has several technical ingredients:

1. Rewrite the Green's functions in difference variables and preserve the OS
   positivity form.
2. Build Hilbert-space-valued distributions `Ψ_n(x, ξ)` so that the scalar
   product identity `(5.2)` holds.
3. Use the self-adjoint contraction semigroup `e^{-tH}` to shift one time
   variable, giving `(5.3)`.
4. Use the matrix element formula `(5.4)` to continue in a single time
   variable while keeping all remaining variables distributional/parametric.
5. Use Euclidean covariance plus carefully chosen cones to convert these
   one-variable continuations into genuine local analyticity in all time
   variables near the real domain.

The geometric part is the key refinement over the naive OS I picture.

#### 3.3.1. Cone geometry and rotated continuation

OS II chooses cones `R_+^k(y)` and dual-cone vectors `e_1, ..., e_4` so that:

- the original real configuration lies in a cone stable under small rotations,
- the chosen `e_μ` point into directions compatible with one-variable semigroup
  continuation,
- and the analytically continued function can be parameterized by variables
  `u_i^μ ≥ 0` in the directions `e_μ`.

Then the argument proceeds by taking logs `s_i^μ = ln u_i^μ`, getting separate
flat tubes in the `s`-variables, and applying the Malgrange-Zerner / tube
theorem to pass from separate flat-tube analyticity to analyticity on the
convex envelope of the union.

This is one of the most important proof ideas in OS II:

- separate one-variable semigroup analyticity
  `+`
- Euclidean covariance / cone geometry
  `+`
- a tube theorem
  `=`
- genuine local analyticity in several time variables.

#### 3.3.2. Why Lemma 5.1 matters

Lemma 5.1 is not just a convenience estimate. It gives an explicit polydisc of
analyticity around each real point `ξ`, with radius controlled by

- the size of the time coordinates,
- and the ratio `ξ_i^0 / |ξ_i|`.

This is exactly the kind of local quantitative analyticity one later needs in
Chapter VI when turning distributional information into polynomial estimates on
the resulting analytic functions.

#### 3.3.3. What `(AN)` and `(PN)` are really doing

The induction in Chapter V alternates between two statements:

- `(AN)`:
  scalar-valued analytic continuation on larger time domains `C_k^(N)`;
- `(PN)`:
  Hilbert-space-valued vectors `Ψ_n(x, ζ)` on larger mixed domains `D_n^(N)`
  whose scalar products reproduce the analytically continued Green's functions.

This alternation is structurally important.

`(PN)` gives the semigroup/Hilbert-space control needed to define the next
analytic continuation step, and `(AN)` packages the outcome as a scalar
analytic function on a larger domain. Then the process repeats.

So the real engine is not just “analyticity by semigroup.” It is:

- vector-valued semigroup control
  `->`
- scalar analytic continuation
  `->`
- bigger vector-valued domain
  `->`
- bigger scalar domain.

That is a useful model for our own general one-gap theorem design.

#### 3.3.4. Lemma 5.2 and Corollary 5.3

Lemma 5.2 is the combinatorial/domain-growth heart of the OS II induction.
It shows that the recursively defined domains `D_n^(N)` and `C_k^(N)` contain
explicit regions whose opening increases with `N`.

Corollary 5.3 then gives a quantitative lower bound on how much of the time
domain is covered at stage `N`. This is what ultimately lets OS II conclude
that the union of all `C_k^(N)` is the whole product right half-plane `C_+^k`.

So there are two distinct technical burdens in OS II:

- Chapter V:
  prove the continuation exists on bigger and bigger domains;
- Chapter VI:
  prove the resulting functions satisfy usable polynomial bounds on those
  domains.

## 4. Method A vs Method B in OS II

OS II distinguishes two ways to handle spatial variables.

### Method A

Treat spatial variables distributionally throughout.

Pros:

- simpler,
- closer to the semigroup formulas.

Cons:

- needs a stronger growth assumption, roughly the stronger `E0"`-type input.

### Method B

Use Euclidean invariance and a Glaser-type geometric argument to show the
relevant functions are honest continuous / analytic functions of spatial
variables, not merely distributions in them.

Pros:

- works under the weaker corrected OS growth assumption.

Cons:

- much more geometric,
- more technically demanding.

For our current Lean state, the semigroup-side two-point work is closer to
Method A in flavor, while the eventual `boundary_values_tempered` and some of
the Euclidean analyticity work are closer to Method B.

An important practical reading of this split:

- if we are trying to close the immediate `schwinger_continuation_base_step`
  blocker, Method A style semigroup/parameter work is probably the right local
  target;
- if we are trying to close the full growth / temperedness / boundary-value
  chain, then Method B style analyticity and geometry will inevitably come
  back.

### 4.1. Exactly where the linear growth condition is used

OS II is explicit on this point: the linear growth condition `E0'` is used for
the **temperedness estimates**, not for the bare existence of analytic
continuation.

The proof logic is:

- Chapter V:
  construct `S_k(ζ)` and `S_k(ζ^0 | ξ)` using semigroup continuation and
  Euclidean covariance, with only `E0`, `E1`, `E2`;
- Chapter VI:
  use `E0'` to derive the bounds `(4.5)` and `(4.6)` that make the
  Fourier-Laplace/boundary-value step rigorous in the tempered category.

That is why OS II says the linear growth condition is only needed at “this
stage,” namely the temperedness-estimate stage.

### 4.2. Chapter VI.1: from distributions to actual functions

This is one of the most technical parts of OS II, and it is worth summarizing
carefully because it explains what “linear growth” is really buying them.

The problem is:

- even if `S_k(ξ)` is known to be real analytic,
- and even if it arises from a distribution satisfying `E0'`,
- it does **not** follow formally that the resulting analytic function is
  polynomially bounded.

OS II therefore does not estimate `S_k` directly. Instead it:

1. uses the local analyticity radius from Lemma 5.1,
2. performs a carefully chosen regularization of `S_k` in complex directions,
3. obtains a smoother auxiliary object `T_k`,
4. estimates `T_k`,
5. then recovers bounds on `S_k` via a mean-value / maximum-principle argument.

#### 4.2.1. The regularization step

OS II chooses:

- a compactly supported radial mollifier in complex directions,
- a kernel `k_ρ`,
- and a compactly supported bump `g_ρ`.

Using the local polydisc analyticity from Lemma 5.1 and the mean-value theorem
for harmonic functions, they rewrite `S_k(ξ + ζ)` as an average of a regularized
object `T_k` over a small complex neighborhood.

The key lesson is:

- they do not estimate the raw analytic function head-on;
- they first move to a regularized object that still remembers positivity.

#### 4.2.2. Why positivity matters for the estimate

The regularized `T_k` still satisfies a positivity structure inherited from the
OS form. This allows OS II to write `T_k` as a scalar product of two vectors in
the OS Hilbert space.

That is the bridge back to semigroup methods:

- once `T_k` is a scalar product `(Ψ_1, Ψ_2)`,
- the shifted quantity `(Ψ_1, e^{-zH} Ψ_2)` gives analytic continuation in one
  complex variable,
- and its absolute value is bounded by `||Ψ_1|| * ||Ψ_2||`.

So the linear growth estimate is *channeled through Hilbert-space norms*.
That is a very useful structural point.

#### 4.2.3. Where `E0'` actually enters

The hard analytic estimate in VI.1 is the bound on the norms of those vectors,
schematically of the form

- `||Ψ_1|| ≤ σ_n * (...)^s`,
- `||Ψ_2|| ≤ σ_{k-n+1} * (...)^s`,

with factorial-growth sequences and polynomial dependence on the parameters.

This is precisely where the linear growth condition is used.

In other words:

- `E0'` is not used to show the semigroup exists;
- `E0'` is not used to show one-variable continuation exists;
- `E0'` is used to control the **size** of the vectors that arise after
  regularization, so the semigroup matrix elements satisfy quantitative
  polynomial bounds.

#### 4.2.4. Why four directions appear

OS II analytically continues the regularized object in `4k` linearly
independent directions. This is a specifically Euclidean four-dimensional
feature of the proof as written: they choose four independent vectors `e_μ`
coming from the cone geometry and continue in each associated direction.

Then they use the Malgrange-Zerner theorem on the union of the corresponding
tubes and the maximum principle to control the analytic continuation on the
full local complex neighborhood.

So the logic is:

- directional semigroup continuation in enough independent directions
  `+`
- envelope of holomorphy / tube theorem
  `+`
- maximum principle
  `=`
- polynomial bound on the full local analytic function.

#### 4.2.5. Output of VI.1

The output is the real-domain temperedness estimate `(4.5)`.

This is already a significant strengthening over mere analyticity: it says the
real-analytic functions `S_k(ξ)` satisfy a polynomial bound of the exact type
needed to later treat them as tempered boundary values after further analytic
continuation.

### 4.3. Chapter VI.2: continuing the estimates

Once `(4.5)` is proved on the real domain, OS II carries those estimates through
the inductive analytic continuation domains `C_k^(N)`.

The key move is to regard `S_k(ζ^0 | ·)` as taking values in a Banach space of
continuous functions of the spatial variables with polynomial weights. Then:

- the real-domain bound gives a Banach-space norm estimate,
- the Chapter V induction gives analyticity on larger domains,
- the maximum principle transports the estimate from one stage to the next,
- and Corollary 5.3 provides quantitative control that eventually covers all of
  `C_+^k`.

So Chapter VI.2 is not re-proving analyticity. It is transporting the **bounds**
along the analytic continuation ladder already built in Chapter V.

### 4.4. Why this matters for our Lean plan

The distinction between Chapters V and VI suggests a very concrete division of
labor for our `E -> R` development:

- first prove the OS-style one-gap semigroup continuation/factorization
  theorem;
- only after that, attack the growth estimates needed for
  `boundary_values_tempered`.

If we blur those two stages, we risk mixing the Chapter V and Chapter VI
burdens and making both harder.

## 5. Exact correspondence with the current Lean files

### `OSToWightmanSemigroup.lean`

This file corresponds to the clean semigroup/Hilbert-space part of OS I and OS
II:

- construction and use of the holomorphic semigroup,
- spectral/Laplace bridge,
- one-variable holomorphic matrix elements.

This is the Lean home of the semigroup object itself.

Paper correspondence:

- OS I `(4.6)`-`(4.11)`
- OS II `(5.3)`-`(5.4)`

### `OSToWightman.lean`

This file is the base-step analytic continuation core.

Its main remaining blocker

- `schwinger_continuation_base_step`

is the Lean version of: turn the semigroup continuation mechanism into the
actual Schwinger-shell continuation statement needed by reconstruction.

This file should remain the place where the general one-gap continuation
machinery lives, not the place where all specialized shell reductions get
accumulated.

### `OSToWightmanTwoPoint.lean`

This file is not a separate OS theorem in the papers. It is our controlled
model case for the first genuinely nontrivial continuation mechanism.

Its role is:

- isolate the center/difference-variable issue,
- expose the semigroup-side product-shell vs admissible-shell mismatch,
- reduce the missing input to a precise factorization / annihilation statement.

So this file is a Lean-specific staging ground for the OS one-gap mechanism.

Its real value is diagnostic:

- if we can make the semigroup scalar depend only on the descended
  difference-variable parameter here,
- then we have identified the theorem shape the general OS-style parameter
  theorem must satisfy.

### `OSToWightmanBoundaryValues.lean`

This file corresponds to the downstream Fourier-Laplace / boundary-value stage:

- temperedness of boundary values,
- transfer of the continued objects to Wightman distributions,
- support/growth transport.

This is downstream of the current blocker, not upstream of it.

## 6. What the current `k = 2` work means in OS language

Our current two-point descent infrastructure does the following.

On center/difference coordinates `(u, ξ)`:

- `twoPointCenterDescent` integrates out the center block `u`,
- `twoPointCenterShearDescent` produces the descended difference-variable test
  from the semigroup/product shell,
- `twoPointCenterShearResidual` is the kernel element measuring the mismatch
  between the product shell `χ(u) g(u + ξ)` and its canonical admissible
  representative `χ(u) h(ξ)`.

Recent progress:

- the residual has zero descent,
- the descent operator is now covariant under right translations on the
  product shell.

Translated into OS language, this means:

- we are trying to prove that the relevant semigroup matrix element depends
  only on the descended difference-variable parameter,
- i.e. that the semigroup continuation factors through the correct one-gap
  parameter object.

That is exactly the kind of statement OS encode by fixing `h_m` and running the
semigroup/Laplace argument only in one time variable.

### 6.1. Why the current descent language is not alien to OS

The papers do not literally define our `twoPointCenterDescent`, but conceptually
it is doing the same job as OS’s parameter packaging:

- remove the dummy center variable,
- isolate the true difference-variable content,
- and force the scalar continuation problem to depend only on that content.

So the descent language is a Lean-specific implementation of an OS-style
parameterization step, not a deviation from the paper’s method.

### 6.2. Production realization of the center-integration step

The current production files now contain a fairly clean realization of the
“integrate out the dummy center variable” step.

At the block-integration level:

- `integrateHeadBlock_tensorProduct`
  in [BlockIntegral.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/BlockIntegral.lean)
  says that integrating out the head block of a tensor-product Schwartz test
  gives exactly “integral of the head factor” times the tail factor.

- `integrateHeadBlock_translateSchwartz_tail`
  and
  `integrateHeadBlock_translateSchwartz_head`
  say that block integration is compatible with translating the surviving block
  and invariant under translating the block that gets integrated out.

At the two-point descent level:

- `twoPointCenterDescent_twoPointDifferenceLift_eq_integral_smul`
  in [TwoPointDescent.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/TwoPointDescent.lean)
  is the exact admissible-shell formula:
  `twoPointCenterDescent (twoPointDifferenceLift χ h) = (∫ χ) • h`.

- `twoPointCenterDescent_twoPointProductLift_eq_differenceRepresentative`
  says that the semigroup/product shell and its canonical admissible
  representative have the same descent.

- `twoPointCenterDescent_twoPointCenterShearResidual_eq_zero`
  isolates the kernel element measuring the mismatch between those two shells
  and proves that its descent is zero.

- `twoPointCenterShearDescent_translate_right`
  shows the descended parameter behaves covariantly under right translation of
  the product-shell test.

This is already quite close to what the OS papers need conceptually:

- identify the dummy center variable,
- integrate it out,
- get a parameter object in the true difference variable,
- and prove the analytic continuation depends only on that parameter object.

So the current production descent package should be read as the Lean
implementation of the OS parameter-packaging step, not as accidental
two-point-specific auxiliary code.

### 6.3. Direct `k = 2` semigroup specialization

For `k = 2`, the semigroup/spectral picture becomes much simpler than the
general multi-gap story.

There is only one genuine time-difference variable, so we do **not** need any
joint spectral-measure story. The relevant scalar is already an ordinary
two-vector semigroup matrix element.

The key current production statements are:

- `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
  in [OSToWightmanSemigroup.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean),
  which identifies the holomorphic semigroup matrix element with the spectral
  Laplace off-diagonal form.

- `selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift`
  in [OSToWightmanTwoPoint.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTwoPoint.lean),
  which identifies that spectral object with the explicit `ξ`-shift Euclidean
  integral for one-point test pairs.

- `twoPointDifferenceLift_timeShift_holomorphicValue_semigroupMatrix_centerShear_centerValue`
  in [OSToWightmanTwoPoint.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTwoPoint.lean),
  which packages the two-point continuation directly in terms of the semigroup
  matrix element after the center-shear reduction.

This is the precise OS-style reading of the current two-point file:

- the live issue is not a missing spectral theorem,
- and not a missing holomorphic-extension theorem in abstract form,
- but the mismatch between two shells that should produce the same descended
  parameter object.

That is why the two-point gap is now naturally a factorization-through-descent
problem.

## 7. The current `E -> R` blocker in OS terms

The current blocker is not:

- “find some holomorphic function.”

It is:

- construct the correct one-gap parameterized semigroup object on the
  admissible shell,
- or prove that the current semigroup/witness scalar functional factors through
  the relevant descent operator.

In the two-point file this currently appears as the need to replace a residual
annihilation hypothesis by a genuine factorization theorem.

That is the correct OS-style next step.

### 7.1. What a truly OS-shaped missing theorem would look like

The missing theorem should have this flavor:

- input:
  an admissible one-gap shell together with its descended parameter object;
- claim:
  the semigroup matrix element depends only on that descended parameter;
- output:
  the resulting scalar function is the correct holomorphic continuation in the
  chosen time variable.

In other words, the theorem should eliminate the shell mismatch by proving
factorization through the parameter object, not by postulating an accidental
equality of two unrelated shells.

### 7.2. The precise factorization route suggested by the current code

The current code suggests a very concrete theorem chain for `k = 2`.

Fix a normalized cutoff `χ₀` with `∫ χ₀ = 1`, and let

- `g`
  be the product-shell one-point test,
- `twoPointCenterShearDescent χ₀ g`
  be the canonical descended admissible representative,
- `twoPointCenterShearResidual χ₀ g`
  be the difference between the original product shell and its canonical
  descended representative.

We already know:

- `twoPointCenterDescent (twoPointCenterShearResidual χ₀ g) = 0`.

The missing theorem should say something like:

- if `L` is the relevant semigroup/witness scalar functional on two-point
  center/difference Schwartz space,
- and `L` is invariant under center translation,
- then `L` factors through `twoPointCenterDescent`.

Formally, the desired pattern is:

- `L (translate_in_center a F) = L(F)` for all center translations `a`,
- therefore there exists `L'` on difference-variable Schwartz space such that
  `L = L' ∘ twoPointCenterDescent`.

Once such a factorization theorem is available, the residual is killed for the
right structural reason:

- `twoPointCenterDescent residual = 0`,
- so `L(residual) = L'(0) = 0`.

Then the remaining chain is immediate:

1. product shell and canonical admissible shell have equal scalar pairings,
2. the semigroup/spectral object already computes the product-shell pairing,
3. therefore the same semigroup/spectral object computes the admissible shell,
4. hence the admissible shell has the required holomorphic continuation.

This is exactly the content currently isolated in
`twoPointDifferenceLift_timeShift_holomorphicValue_semigroupMatrix_canonicalCenterShear_of_residual_annihilation`
in [OSToWightmanTwoPoint.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTwoPoint.lean):
the theorem is already telling us that once the residual is annihilated, the
rest of the two-point continuation mechanism is done.

So the remaining mathematical gap is very small in statement size but deep in
content:

- not another shell identity,
- but a continuity + center-translation-invariance
  `=> factorization through center descent`
  theorem for the semigroup/witness scalar functional.

### 7.3. Why this is the right OS-shaped next theorem

This factorization route matches the papers better than trying to guess a
direct equality between the product shell `χ(u) g(u + ξ)` and the admissible
shell `χ(u) h(ξ)`.

OS do not proceed by proving accidental shell identities. They:

- package the non-analytic variables into a parameter object,
- show the analytic continuation depends on that parameter,
- and then study the resulting one-variable function.

Our descent/factorization route is the Lean equivalent of exactly that move.

So, from the perspective of the papers, the right next theorem is:

- not “a better shell-comparison lemma,”
- but “the semigroup scalar depends only on the descended parameter.”

## 8. Path from `k = 2` to general `k`

The papers suggest the following route.

1. Solve one-gap continuation with all other variables treated as parameters.
2. Package the parameter space in a Schwartz-compatible way.
3. Show the resulting continued object satisfies the needed growth estimates.
4. Iterate this one-gap mechanism across the ordered time differences.

So the role of the current two-point development is not to serve as a final
base case for induction on `k`.

Its role is to identify, in the simplest nontrivial case, the exact theorem
shape the general parameterized continuation must satisfy.

### 8.1. The real generalization step

The real jump from `k = 2` to general `k` is therefore:

- not “do the same proof with bigger indices,”
- but “replace the two-point descended difference-variable test by the general
  parameter object `h_m`.”

Once that parameterized theorem exists, the rest of the OS chain is the same in
spirit:

- semigroup matrix element,
- one-gap continuation,
- inductive enlargement of the analytic domain,
- Fourier-Laplace extraction,
- boundary values.

## 9. Practical takeaway for future Lean work

When deciding whether a new theorem is on the right path, the best test is:

- does it move us toward a one-gap semigroup continuation theorem with the
  remaining variables as parameters?

Good signs:

- factorization through a descent operator,
- explicit semigroup matrix-element formulas,
- parameterized one-variable holomorphic continuation,
- Fourier-Laplace packaging with support/growth control.
- proofs that a semigroup/witness scalar functional factors through
  `integrateHeadBlock` / `twoPointCenterDescent`.

Bad signs:

- adding more shell-specific wrapper theorems with no new factorization content,
- treating `k = 2` as if it were itself the whole OS method,
- trying to continue all time variables simultaneously before the one-gap
  parameter mechanism is settled.
- treating the residual-annihilation criterion as a final theorem rather than
  as a signal that a deeper factorization theorem is still missing.

## 10. Concrete current reading of the project

The current file split is consistent with the papers if we interpret it as:

- `OSToWightmanSemigroup.lean`
  = OS semigroup and one-variable matrix-element engine;
- `OSToWightman.lean`
  = intended home of the general one-gap continuation theorem;
- `OSToWightmanTwoPoint.lean`
  = first nontrivial laboratory for identifying the right parameter object;
- `OSToWightmanBoundaryValues.lean`
  = downstream Fourier-Laplace / growth / boundary-value layer.

The current risk is not mathematical unsoundness in the two-point ladder.
It is theorem-surface drift:

- if we keep adding shell-specific criteria, the file may grow while the real
  missing factorization theorem stays untouched.

Conversely, the current opportunity is good:

- the descent package in
  [BlockIntegral.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/BlockIntegral.lean)
  and
  [TwoPointDescent.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/TwoPointDescent.lean)
  has already exposed the kernel element and the correct covariance properties;
- the remaining step is now a conceptually clean theorem about the scalar
  functional itself.

Finally, some older local Bernstein-Widder / center-shear scratch notes are now
partly superseded by the production descent infrastructure. They may still be
useful for ideas, but they should no longer be treated as the current theorem
surface. The current production surface is the descent/factorization one.
The risk is staying too long in the laboratory file and never extracting the
general parameter theorem that OS II actually wants.

So the main remaining conceptual jump is:

- replace the current specialized two-point residual-annihilation criterion by
  an actual factorization theorem through center/difference descent,
- then generalize that theorem from the two-point model to the general
  one-gap parameterized continuation mechanism.
