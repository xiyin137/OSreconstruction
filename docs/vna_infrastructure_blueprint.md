# vNA Infrastructure Blueprint

Purpose: this note is the implementation blueprint for the remaining
von-Neumann-algebra / unbounded-operator infrastructure in `OSReconstruction/vNA`.

This area is not on the critical `E -> R` path, but it is part of the longer
operator-algebra formalization surface and should have an honest theorem-by-
theorem plan.

## 1. Live open areas

The current open/sorry-backed files include:

1. `vNA/MeasureTheory/CaratheodoryExtension.lean`,
2. `vNA/ModularTheory.lean`,
3. `vNA/ModularAutomorphism.lean`,
4. `vNA/KMS.lean`,
5. `vNA/Predual.lean`,
6. `vNA/Unbounded/StoneTheorem.lean`.

Other files such as `vNA/Bochner/CfcInfrastructure.lean` are already largely
proved and should be treated as infrastructure, not frontiers.

## 2. Package A: Measure-theoretic base

`CaratheodoryExtension.lean` is the foundational measure-theory package. Later
modular/spectral proofs should not proceed until its core extension theorems
are honest.

Documentation-standard theorem slots:

```lean
lemma outerMeasure_of_premeasure
lemma measurable_sets_form_sigmaAlgebra
lemma caratheodory_extension_exists
lemma caratheodory_extension_unique
theorem sesqForm_measure_construction
```

The later port should isolate the pure extension theorem before any Hilbert-
space-valued measure constructions.

### 2.1. Exact proof transcript for Carathéodory extension

The later Lean proof should be split into the standard sequence:

1. define the outer measure from the premeasure by infimum over countable
   covers,
2. prove the Carathéodory-measurable sets form a sigma-algebra,
3. prove every set in the starting algebra is measurable for that outer
   measure,
4. restrict the outer measure to the measurable sigma-algebra,
5. prove agreement with the original premeasure on the starting algebra,
6. prove uniqueness on the generated sigma-algebra.

So the theorem slots should really be understood as:

```lean
def premeasureOuterMeasure
lemma outerMeasure_of_premeasure
lemma caratheodory_measurable_sigmaAlgebra
lemma generating_algebra_subsets_are_measurable
lemma outerMeasure_restrict_agrees_on_prealgebra
lemma caratheodory_extension_exists
lemma caratheodory_extension_unique
theorem sesqForm_measure_construction
```

This keeps the later measure-valued operator theory from hiding foundational
measure-extension work.

## 3. Package B: Stone / unbounded spectral base

`Unbounded/StoneTheorem.lean` and `Unbounded/Spectral.lean` supply the operator
theory under modular theory.

The documentation should now distinguish:

1. the spectral differentiation package, which is already proved in
   `SpectralPowers.lean`,
2. the genuinely remaining Stone-side frontier, which sits in the final
   generator/time-evolution assembly.

So the theorem package should be documented as:

```lean
lemma unitaryGroup_hasDerivAt_dom
lemma unitaryGroup_preserves_domain
lemma unitaryGroup_commutes_with_generator
lemma unitaryGroup_generator_domain_eq
lemma generator_from_stronglyContinuous_unitaryGroup
lemma spectral_measure_recovers_generator
theorem stone_theorem_unbounded
```

This package should remain separate from Tomita-Takesaki. Modular theory should
consume Stone/spectral inputs, not rebuild them.

### 3.1. Exact proof route for the spectral differentiation package

The later docs should say explicitly that the spectral derivative package is a
direct spectral-measure proof:

1. prove the Parseval identity
   `‖U(h)x - x‖² = ∫ |e^{ihλ} - 1|² dμ_x(λ)`,
2. prove the domain characterization
   `x ∈ dom(T) ↔ ∫ λ² dμ_x < ∞`,
3. use dominated convergence with
   `|(e^{ihλ} - 1)/h| ≤ |λ|` to prove `unitaryGroup_hasDerivAt_dom`,
4. use invariance of the spectral measure under `U(t)` to prove
   `unitaryGroup_preserves_domain`,
5. use functional-calculus commutativity to prove
   `unitaryGroup_commutes_with_generator`,
6. use Fatou's lemma to prove `unitaryGroup_generator_domain_eq`.

So the proof pattern here is fully concrete:

1. spectral measure,
2. Parseval/integral identities,
3. DCT / Fatou,
4. functional calculus commutativity.

### 3.2. Honest remaining Stone-side frontier

The live remaining Stone-side theorem should be documented more honestly as the
final generator/time-evolution package:

```lean
lemma unique_from_generator_via_domain_ode
lemma timeEvolution_generator_sign_normalized
theorem timeEvolution_generator
```

Its proof route should be:

1. use `unitaryGroup_hasDerivAt_dom` to identify the derivative on `dom(T)`,
2. combine it with the generator integral formula,
3. prove uniqueness of the unitary group from the generator by the domain-ODE
   cancellation argument,
4. extend from the dense domain to all of `H`,
5. fix the sign convention once and state the final generator theorem.

This is much more implementation-ready than leaving Package B as
"prove Stone's theorem somehow."

## 4. Package C: Modular theory

`ModularTheory.lean` contains the Tomita / modular operator / modular
conjugation base.

The later implementation should split it into:

```lean
lemma tomita_operator_closable
lemma modular_operator_positive
lemma modular_operator_selfAdjoint
lemma modular_conjugation_exists
lemma modular_conjugation_antiunitary
theorem tomita_fundamental
```

The docs should keep the route:

1. Tomita operator,
2. closure,
3. modular operator,
4. modular conjugation,
5. fundamental theorem,

instead of mixing all five in one large proof file.

### 4.1. Exact proof transcript for modular theory

The later Lean implementation should proceed in the following literal order:

1. define the Tomita operator on the algebraic domain `xΩ ↦ x*Ω`,
2. prove the graph is closable by the standard adjoint-pairing argument,
3. form the closed operator and its polar decomposition,
4. identify the positive part as the modular operator,
5. identify the partial isometry as the modular conjugation,
6. prove positivity/selfadjointness/antiunitarity properties,
7. package the Tomita fundamental theorem.

So the theorem slots should be refined as:

```lean
def tomita_preOperator
lemma tomita_operator_closable
def closedTomitaOperator
lemma closedTomita_polarDecomposition
lemma modular_operator_positive
lemma modular_operator_selfAdjoint
lemma modular_conjugation_exists
lemma modular_conjugation_antiunitary
theorem tomita_fundamental
```

The later file should not try to prove modular automorphism statements before
this polar-decomposition package is honest.

## 5. Package D: Modular automorphism group and KMS

`ModularAutomorphism.lean` and `KMS.lean` are later consumers of Package C.

Documentation-standard theorem slots:

```lean
lemma modularAutomorphismGroup_exists
lemma modularAutomorphismGroup_is_oneParameter
lemma modularAutomorphism_preserves_algebra
theorem tomita_takesaki_modular_automorphism

lemma kmsAnalyticStrip_function
lemma kmsBoundaryValues
theorem kms_condition_of_modular_group
```

These theorems should be implemented only after the core modular objects are
honest.

### 5.1. Exact proof transcript for modular automorphisms and KMS

The later Lean proof should be written in two visibly separate stages.

Modular automorphism stage:

1. define `σ_t(x) := Δ^{it} x Δ^{-it}`,
2. prove well-definedness and the one-parameter group law,
3. prove `σ_t` preserves the von Neumann algebra,
4. prove Tomita-Takesaki invariance.

KMS stage:

1. define the strip function
   `F_{x,y}(z) := ⟪Ω, σ_z(x) y Ω⟫`,
2. prove holomorphy on the interior strip,
3. prove the two boundary-value formulas,
4. conclude the KMS condition.

So the theorem slots should be read as:

```lean
lemma modularAutomorphismGroup_exists
lemma modularAutomorphismGroup_is_oneParameter
lemma modularAutomorphism_preserves_algebra
theorem tomita_takesaki_modular_automorphism

lemma kmsAnalyticStrip_function
lemma kmsBoundaryValues
theorem kms_condition_of_modular_group
```

## 6. Package E: Predual

`Predual.lean` should be treated as its own package, not as fallout from the
modular theory files.

Documentation-standard theorem slots:

```lean
lemma vector_functionals_generate_sigmaWeak
lemma predual_exists
lemma predual_is_unique
theorem vonNeumannAlgebra_hasPredual
```

This package is conceptually downstream of the operator-topology foundations
and should not be used to justify them.

### 6.1. Exact proof transcript for the predual package

The later Lean implementation should make the standard route explicit:

1. define vector functionals `ω_{ξ,η}(x) = ⟪ξ, x η⟫`,
2. prove they separate points and generate the sigma-weak topology,
3. package their norm-closure as the predual candidate,
4. prove the dual of that Banach space identifies with the original von
   Neumann algebra,
5. prove uniqueness of the predual.

So the theorem slots should be read as:

```lean
def vectorFunctional
lemma vector_functionals_generate_sigmaWeak
def predualCandidate
lemma predual_exists
lemma predual_is_unique
theorem vonNeumannAlgebra_hasPredual
```

## 7. Exact dependency order

The later Lean implementation should proceed in this order:

1. Carathéodory / measure-theory base,
2. Stone/unbounded spectral base,
3. core modular theory,
4. modular automorphism group,
5. KMS package,
6. predual package.

## 8. Do not do this

1. Do not start with KMS before modular automorphisms are honest.
2. Do not start with modular theory before the Stone/spectral base is honest.
3. Do not let measure-extension sorries leak into later operator-theory files.
4. Do not treat the largely proved CFC infrastructure as if it were still a
   live blocker.

## 9. What counts as implementation-ready

This blueprint should be considered ready only when:

1. the six open areas above are separated into packages,
2. the dependency order is explicit,
3. the already-proved CFC/spectral infrastructure is treated as closed input,
4. no later operator-theory proof is allowed to hide its foundational
   dependency.

## 10. Recommended implementation size

Rough expected size:

1. Carathéodory extension base:
   `180-280` lines,
2. Stone/unbounded spectral endgame:
   `120-220` lines beyond the already-proved spectral differentiation package,
3. modular theory core:
   `220-360` lines,
4. modular automorphism + KMS:
   `140-240` lines,
5. predual package:
   `120-200` lines.

This blueprint is implementation-ready once those five packages are treated as
the literal operator-theory work units and not as a single diffuse `vNA`
backlog.
