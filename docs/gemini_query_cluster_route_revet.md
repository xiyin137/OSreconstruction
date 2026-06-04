# Gemini deep-think query (v2): the cluster sorry is a limit–integral interchange — settle integrability + the IBP route

You are vetting the proof strategy for ONE remaining `sorry` in a Lean 4
formalization of Osterwalder–Schrader reconstruction. A prior deep-think pass
answered a larger question (build analytic Hilbert states / unbounded operators /
Araki–Hepp–Ruelle curvature lemma). Reading the actual Lean code shows the sorry
is much narrower than that, so I need you to answer the narrow question precisely.

**Do NOT re-derive the cluster theorem from scratch, and do NOT re-litigate
"Tflat dual pairing vs GNS–Bochner Hilbert states."** Two things are already in
hand in the formalization and are NOT in question:
- The **pointwise** cluster decay (Araki–Hepp–Ruelle): for fixed Euclidean
  configurations it is supplied as a hypothesis `hRuelle.pointwise`.
- A **proved**, conditional cobounded spatial-decay lemma
  (`gns_orthogonal_spatial_cobounded_decay_of` → `spectral_riemann_lebesgue`),
  valid given an absolutely-continuous spatial spectral marginal.
I want a verdict on the **limit–integral interchange** and the **integrability**
question below, and on whether **integration by parts in the time differences**
closes it. Reason carefully and adversarially; flag anything that breaks.

## Exact setup (matches the Lean statement)

- Euclidean configs: `x : Fin k → Fin (d+1) → ℝ`; coordinate `0` is Euclidean
  time. `wick(x)` sends a real config to the imaginary-time complex config
  `z_j = (i·x_j0, x_j1,…,x_jd)` used inside the analytic function.
- `W_analytic_BHW Wfn N` is the analytic N-point Schwinger/Wightman function,
  holomorphic on the (permuted, extended) tube; its boundary values are the
  real-time Wightman distributions.
- `f : Schwartz(ℝ^{n(d+1)})`, `g : Schwartz(ℝ^{m(d+1)})`, both supported in the
  open "ordered positive time region" OPTR (strictly increasing, strictly
  positive Euclidean times).
- `a` is a purely spatial translation (`a_0 = 0`).

The Lean goal (after two PROVED reduction steps — a measure-preserving change of
variables and a Fubini factorization) is the **limit–integral interchange**:
```
∫_{ℝ^{n(d+1)}×ℝ^{m(d+1)}} W_analytic_BHW(n+m)( wick(x), wick(y)+(0,a) ) · f(x) · g(y)  dx dy
   ⟶   ( ∫ W_analytic_BHW(n)(wick x)·f(x) dx ) · ( ∫ W_analytic_BHW(m)(wick y)·g(y) dy )  =: L_n·L_m
```
as `|⃗a| → ∞`. The integrand converges **pointwise** (proved) to the factorized
limit `W_analytic(wick x)·W_analytic(wick y)·f(x)·g(y)`. The ONLY missing step is
passing the limit through the integral.

## The available bound (a-uniform, within-block regulators only)

The hypothesis package gives, for `z₁ ∈ ForwardTube(n)`, `z₂ ∈ ForwardTube(m)`,
joint config in the tube:
```
‖W_analytic_BHW(n+m)(append z₁ (z₂ + spatial a))‖
   ≤ C·(1+‖z₁‖+‖z₂‖)^N · (1 + d₁(z₁)⁻¹)^M · (1 + d₂(z₂)⁻¹)^M
```
where `d(z)` = min over successive imaginary-time differences of the distance of
`Im(z_k − z_{k-1})` to the boundary of the forward cone. Crucially:
- the RHS does **not** depend on `a` (uniform in the spatial translation);
- the two regulators are **within-block** (`z₁` only, `z₂` only); there is **no
  junction (f-block↔g-block) regulator**, because the cluster blocks are
  spacelike-separated.

So the natural dominator
`G(x,y) = C(1+‖wick x‖+‖wick y‖)^N (1+d(wick x)⁻¹)^M (1+d(wick y)⁻¹)^M |f(x)||g(y)|`
is `a`-uniform; its ONLY non-integrability is the within-block factor
`(1+d⁻¹)^M`. Note `d(wick x)` = min over consecutive Euclidean-time gaps
`x_{k+1,0} − x_{k,0}`, which → 0 on the codim-1 coincidence set
`{x_{k+1,0} = x_{k,0}}` — over which we are integrating. For `M ≥ 1`,
`∫_0^1 δ^{-M} dδ` diverges, so `G ∉ L¹` and naive dominated convergence fails.

## The questions (answer each, decisively)

**Q1 — Integrability / correct object.** Is the single-block integrand
`W_analytic_BHW(n)(wick x)·f(x)` genuinely **absolutely Lebesgue-integrable**
over all `x` (so `L_n` is an ordinary `∫`), or is the `(1+d(wick x)⁻¹)^M`
behaviour a real non-integrable boundary singularity so that `L_n` is only
well-defined as a **tempered-distribution pairing** `⟨W_n^{bv}, f⟩`? Be precise:
the bound is an upper estimate — does the true Euclidean Schwinger function (e.g.
free field, `W₂(x,y) ~ ((x−y)²+m²)^{-(d-1)/2}` continued) actually have a locally
integrable boundary value against Schwartz `f`, even though the crude regulator
bound is not integrable? Distinguish "the bound is not L¹" from "the function is
not L¹."

**Q2 — Restatement.** If `L_n, L_m, J(a)` are really **distributional pairings**,
then writing them as Lebesgue integrals in Lean is the wrong formalization, and
the right move is to restate the theorem with distribution–Schwartz pairings —
in which case `L_n = ⟨W_n^{bv}, f⟩` is finite by continuity for free, and the
interchange becomes **distributional continuity + the already-available pointwise
/ cobounded decay**, with no integrability obstruction at all. Is that the
correct reframing? If yes, what is the minimal distributional infrastructure
needed (tempered distribution = boundary value of the holomorphic function;
continuity of the pairing; a dominated/uniform-boundedness principle for the
`a`-family of pairings) and does it dodge the regulator entirely?

**Q3 — IBP route.** If instead the Lebesgue-integral formulation is to be kept,
does **integration by parts in the Euclidean time differences** close the
interchange? Concretely: write the within-block kernel using the holomorphicity
of `W_analytic` on the tube interior; integrate by parts `M` times in the
relative time variables `τ_{k+1}−τ_k`, transferring derivatives onto the Schwartz
`f,g` (which remain Schwartz), reducing `(1+d⁻¹)^M` to an integrable singularity;
then apply ordinary dominated convergence with the new integrable dominator.
Give the explicit IBP scheme: which variables, the exact boundary terms, and a
proof sketch that the boundary terms vanish (OPTR support ⇒ no contribution at
`τ=0`; decay at `τ→∞`). State precisely what it needs beyond Schwartz `f,g` and
interior holomorphicity of `W_analytic`.

**Q4 — Adversarial.** What could break the IBP route? In particular: is the
within-block boundary singularity a genuine **pole/meromorphic** structure that
IBP integrates against, or does it have **branch cuts / non-integer power /
oscillatory** behaviour that IBP cannot tame? Does the spatial `a`-translation
interfere with the time-IBP (it shouldn't — `a` is spatial — but confirm)? Is
there a hidden requirement that `M` IBPs need `f,g` to vanish to order `M` on the
time-coincidence diagonal (they don't, generically) — and if so, does that
reintroduce boundary terms? Could the codim-1 singularity actually be
**absolutely integrable already** for the relevant `M` and `d` (so the whole
worry is moot)?

## Available Lean infrastructure (use, don't rebuild)

- Relaxed `bv_implies_fourier_support` (compact-subset Vladimirov `H(T^C)`),
  `fl_representation_from_bv`, and `fourierLaplaceExtMultiDim_vladimirov_growth`
  (proved) — give a dual-cone tempered distribution `Tflat` with `W = FL(Tflat)`
  on a tube, and the regulated Vladimirov growth bound.
- `gns_orthogonal_spatial_cobounded_decay_of` (proved, conditional on an
  AC-spatial-marginal `L2SpectralData`) and `spectral_riemann_lebesgue` (proved).
- `hRuelle.pointwise` (hypothesis): the pointwise cluster decay.

## Output I want

A decisive recommendation: (i) state whether the correct object is an `L¹`
integral or a distributional pairing; (ii) if distributional, give the restated
theorem skeleton; (iii) if `L¹`/IBP, give the concrete IBP scheme with boundary
terms; (iv) call out any place my reading is mathematically wrong, and any hidden
vacuity/circularity. Keep it focused on the interchange/integrability — not on
re-proving cluster decay or choosing Tflat vs GNS.
