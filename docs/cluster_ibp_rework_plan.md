# IBP / Schwartz-pairing rework plan for the cluster-proof dominator step

> ## ⚠️ SCRATCH-ONLY / UNAPPROVED EXPLORATORY PLAN
>
> **Per PR-#88 review (Xi, 2026-05-21): this plan is *not* an approved
> implementation route.** It documents an architectural exploration of
> how the cluster-proof sorry *might* be closed via a GNS-Bochner
> shortcut, including stub axioms (`analytic_state`,
> `analytic_state_inner`, continuity/norm stubs) and a "Path C"
> promotion strategy where those stubs would be shipped as vetted
> production axioms if backfill stalls.
>
> **None of those routes have been approved.** Any production-axiom
> adoption derived from this plan requires:
> 1. Fresh, explicit approval from the maintainer (Xi) on the specific
>    axiom statement(s) being proposed.
> 2. Independent vetting (e.g., Gemini deep-think on the axiom's typing,
>    strength, and vacuity — see `docs/cluster_axiom_vetting.md` for the
>    project's established certification cadence).
> 3. Demonstration that the axiom doesn't conflict with the project's
>    "no QFT-specific production axioms" discipline established by the
>    PR-#86 review.
>
> **Status update (2026-05-15 retrospective)**: the GNS-Bochner route
> sketched below was vetted *and rejected* by Gemini deep-think after a
> brief attempt — the proposed OS-reflected analytic state family was
> shown contradictory (Cauchy-Schwarz forces ‖Φ_OS(τ)‖ = ∞ since
> `Φ_OS(τ) = e^{+τH}φ(0)Ω` is unbounded on the Wightman GNS Hilbert
> space). Details in `docs/gemini_query_OS_reflected_stubs.md` and
> `docs/cluster_axiom_vetting.md` (2026-05-10 entry).
>
> The cluster sorry has subsequently been closed via a different,
> narrowly-scoped Path-C-like axiom
> (`ruelle_cluster_integral_DC_step`) on the separate branch
> `r2e/cluster-ibp-rework`. That axiom and its Gemini vetting are tracked
> separately. **Adoption of that axiom upstream still requires Xi's
> explicit approval** — it has not been requested as of this writing.
>
> The rest of this document below is preserved for the architectural
> record (why Tflat doesn't work; what the GNS-Bochner shortcut was
> attempting; what tripped it up) but should be read as historical
> exploration, not as a forward plan.

---

**Branch**: `r2e/ruelle-poly-bound-chain` (likely fork into `r2e/cluster-ibp-rework` for implementation).
**Target**: close the production `sorry` at `OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean:718` in the body of `W_analytic_cluster_integral_via_ruelle`.
**Vetting status**: DRAFT (Rev. 3, 2026-05-10). **Original Tflat-based plan ruled out** by Gemini-deep-think vetting; pivoted to GNS-Bochner shortcut after project + sister-repo probe.
**Author**: Michael Douglas (Claude Code), 2026-05-10.

---

## What's being closed

`W_analytic_cluster_integral_via_ruelle` (henceforth WCIVR) is the OS-side cluster theorem for the Wick-rotated boundary integral. Statement (paraphrased):

> For OPTR-supported `f : SchwartzNPoint d n` and `g : SchwartzNPoint d m`, given `RuelleAnalyticClusterHypotheses Wfn n m`, the joint Wick-rotated integral
> ```
> J(a) := ∫ F_ext_on_translatedPET_total Wfn (wick(x_n, x_m + (0,a))) · (f ⊗ g_a)(x) dx
> ```
> converges to the product of single-block integrals `L_n · L_m` as `|⃗a| → ∞`.

Current `sorry` is at the dominator-integrability step. After the post-vacuity-fix `RACH.bound` regulator, the naive pointwise dominator carries `(1 + Δ⁻¹)^M` — a codim-1 diagonal singularity not locally integrable for `M ≥ 1`. The pointwise + DC route is therefore structurally impossible.

The textbook resolution (Streater-Wightman §3.4 / Ruelle 1962 / AHR 1962) is the **Schwartz dual pairing** with a tempered distribution, replacing the dominator argument with a CLM-continuity argument on Schwartz space.

---

## ⚠️ Why the original Tflat plan doesn't work

**Gemini deep-think vetting (2026-05-10)** identified a fatal flaw:

For Wick-rotated points `z_k = wick(x_k) = (i τ_k, x_k)`, the FL kernel `exp(i ξ_k · z_k) = exp(− E_k · Δτ_k − i p_k · Δx_k)` requires **all** `Δτ_k > 0` for boundedness against a Tflat with dual-cone support (`E_k ≥ 0`).

For OPTR-supported `f, g` independently, within-block differences are positive but the **junction** `Δτ_{n+1, n} = τ_{n+1} − τ_n` (last time of f vs first of g) is unconstrained — generic junction inversion makes the FL kernel exponentially blow up, violating Schwartz seminorm hypotheses needed for `schwartz_clm_fubini_exchange`. A single Tflat representation works only on the literal forward tube, not on PET in general.

Conclusion: ruled out. Pivot to the GNS-Bochner shortcut.

---

## The GNS-Bochner shortcut (pivoted plan)

Use the Wightman reconstruction identity directly, working in the GNS Hilbert space. For `(z_1, ..., z_{n+m})` in PET:
- Define analytic Hilbert states `Φ(u)`, `Φ(v)` ∈ `GNSHilbertSpace Wfn` for `u := (z̄_n,...,z̄_1)` and `v := (z_{n+1},...,z_{n+m})`.
- Both `u, v` are independently in `ForwardTube` (positive successive Im differences within each block — the OPTR ordering of `f, g` makes this work).
- **Inner product**: `⟨Φ(u), Φ(v)⟩ = W_analytic(joint)`. Well-defined regardless of junction ordering (no junction constraint at the Hilbert level).
- Bochner-integrate: `Ψ_f := ∫ Φ(u(x)) f(x) dx`, `Ψ_g := ∫ Φ(v(x)) g(x) dx`.
- `J(a) = ⟨Ψ_f, U(a) Ψ_g⟩`.
- Apply existing `gns_orthogonal_spatial_cobounded_decay_of` (PR #86) for cluster decay → `J(a) → L_n · L_m`.

This route bypasses Tflat, FL kernels, and Schwartz-Fubini in dual space. It's correct (Gemini-vetted) and uses the project's existing GNS infrastructure.

---

## Two-layer decomposition

The work splits cleanly into **two layers**, with one factorable into a sister repo:

### Layer 1: operator-algebraic core (factor-out candidate)

**Content**: PVM-derived bounded contraction semigroup.

```
Given:  H Hilbert,  U : ℝ^{d+1} → U(H) strongly-continuous unitary group,
        joint spectrum of generators ⊆ V̄+ (forward light cone).

Construct:  S : V̄+ → BoundedOp(H),  S(y) := ∫ exp(-y·p) dE(p)
            where E is the joint PVM from SNAG.

Properties:  ‖S(y)‖ ≤ 1,  S(0) = id,  S(y₁ + y₂) = S(y₁) ∘ S(y₂),
             strongly continuous in y, self-adjoint when y real.
```

This is **standard operator-theoretic infrastructure** (Reed-Simon I §VII, Conway IX), with two missing pieces:

| Component | Status |
|-----------|--------|
| `ProjectionValuedMeasureOn α H` type + `snag_theorem` axiom | ✅ in `OSReconstruction/GeneralResults/SNAGTheorem.lean` |
| Mathlib Borel functional calculus on PVMs (operator-valued integration) | ❌ not in Mathlib |
| hille-yosida sister repo's PVM functional calc | ❌ not present (hille-yosida is scalar PD/BCR only currently) |

#### Where layer 1 belongs

**Recommendation: extend `hille-yosida` (sister repo)** with new modules:

```
HilleYosida/PVMFunctionalCalculus.lean    — operator-valued ∫ f dE
HilleYosida/ConeSemigroup.lean             — S(y) := ∫ exp(-y·p) dE(p) for y in dual cone
HilleYosida/AnalyticContinuation.lean      — y ↦ S(y) holomorphic on dual cone interior
```

**Rationale**:
- hille-yosida's scope is already "C₀-semigroups, generators, resolvents, Hille-Yosida bound, BCR Theorem 4.1.13" — i.e., **spectral / semigroup theory used in OS-style reconstructions**.
- The repo's own README explicitly motivates with OS reconstruction's Euclidean-time contraction semigroups extending to unitary groups via spectral positivity.
- Adding PVM functional calc + cone-direction operator semigroup extends the repo's mission cleanly.
- The repo is yours (per its copyright), so internal coordination only.

**Reusability** (downstream beneficiaries):
- Future Haag-Kastler / modular theory formalizations (Tomita-Takesaki `Δ^z` analytic family is a special case).
- OS reconstruction in d ≠ 4.
- JLW-style 2D N=2 Wess-Zumino rigorous analytic-vector machinery.
- Bisognano-Wichmann boost-modular identifications.
- Connes-style entire cyclic cohomology with analytic-continuation traces.

**Estimated effort for layer 1**: 3–5 days project-internal, +2–4 days if extracting to hille-yosida cleanly.

#### ⚠️ Layer 1 critical implementation note: avoid operator-valued integrals

**Per Gemini Lean-formalization review (2026-05-10)**: Mathlib's `MeasureTheory` infrastructure is built for *vector-valued* (Bochner) integration of strongly measurable functions. Projection-valued measures are only **strongly countably additive** in the operator topology, not strongly measurable as Banach-valued functions. Trying to define `S(y) := ∫ exp(-y·p) dE(p)` directly as an operator-valued Bochner-style integral against a PVM is a **multi-week Lean tarpit** — every basic measure-theoretic lemma will fight back.

**The fix — scalarization trick** (textbook spectral theory):

1. From the PVM `E`, build scalar complex measures `μ_{ϕ,ψ}(A) := ⟨ϕ, E(A) ψ⟩`. Mathlib handles scalar measures flawlessly.
2. Define a **sesquilinear form**:
   ```
   B_y(ϕ, ψ) := ∫ exp(-y·p) dμ_{ϕ,ψ}(p)
   ```
   This is a scalar integral against a complex measure — no operator-valued machinery.
3. **Boundedness** (because `|exp(-y·p)| ≤ 1` on the cone-restricted support):
   ```
   |B_y(ϕ, ψ)| ≤ ‖ϕ‖ · ‖ψ‖
   ```
4. **Lift to operator** via the Mathlib representation theorem for bounded sesquilinear forms (`InnerProductSpace.toDual` / `ContinuousLinearMap.adjoint` infrastructure):
   ```
   S(y) ∈ B(H)  with  ⟨ϕ, S(y) ψ⟩ = B_y(ϕ, ψ)
   ```

This route turns the multi-week construction into a 2–3 day mechanical exercise. **Do not implement layer 1 via direct operator-valued integration**; route through scalar sesquilinear forms.

**Build location**: `OSReconstruction/GeneralResults/PVMConeSemigroup.lean` (project-internal first; refactor to hille-yosida later when API stabilizes — extraction is mechanical because the construction has no Wightman / OS dependencies beyond the SNAG axiom and ProjectionValuedMeasureOn type, both already in `OSReconstruction.GeneralResults`).

### Layer 2: Wightman-specific analytic states

**Content**: analytic Hilbert states for the GNS Hilbert space.

```
Given Wfn : WightmanFunctions d, with all GNS infrastructure.

Construct:  Φ : ForwardTube d n → GNSHilbertSpace Wfn

Properties:
  - Φ(z) ∈ GNSHilbertSpace Wfn (well-defined as a Hilbert vector).
  - ⟨Φ(u), Φ(v)⟩ = W_analytic(joint(z_1,...,z_{n+m}))  for u = (z̄_n,...,z̄_1), v = (z_{n+1},...,z_{n+m}).
  - Holomorphic in each z_k (Hilbert-vector-valued analyticity).
  - Boundary value as Im(z_k) → 0+ recovers the smeared real-time state.
```

This is **Wightman-specific** — stays in OSReconstruction.

#### ⚠️ Layer 2 critical implementation note: avoid pointwise field at zero

**Per Gemini Lean-formalization review (2026-05-10)**: an earlier draft of this layer wrote
```
φ(z) := S(Im(z)) U(Re(z)) φ(0) U(Re(z))⁻¹ S(Im(z))⁻¹
Φ(z_1, ..., z_n) := φ(z_1) φ(z_2) ... φ(z_n) Ω
```

**Do not attempt this construction directly.** In rigorous Wightman theory, `φ(0)` is **not** an operator on the Hilbert space — the field is only an operator-valued distribution: `φ(f)` exists for Schwartz `f`, but `φ(x)` at a point does not. Multiplying iterated `φ(z_k)` and interleaving with `S(y)` is an inescapable tarpit of dense-domain tracking, type-coercion failures, and ad-hoc operator products.

**The proposed (NOT-APPROVED) top-down execution**: stub the analytic-state map and its inner-product identity as axioms first, build layers 3 and 4 against the stubs to close the cluster sorry structurally, then return to layer 2 (or fall back to Path C) at the end. Specifically:

```lean
-- ⚠️ EXPLORATORY STUBS — NOT APPROVED AS PRODUCTION AXIOMS.
-- 2026-05-15 retrospective: this stub family was vetted and rejected;
-- the OS-reflected variant required to close the cluster identity is
-- mathematically contradictory (corresponds to e^{+τH}, unbounded).
-- Do NOT introduce these stubs without fresh maintainer approval.
axiom analytic_state {n : ℕ} (u : Fin n → Fin (d + 1) → ℂ) (hu : u ∈ ForwardTube d n) :
    GNSHilbertSpace Wfn

axiom analytic_state_inner {n m : ℕ}
    (u : Fin n → Fin (d + 1) → ℂ) (hu : u ∈ ForwardTube d n)
    (v : Fin m → Fin (d + 1) → ℂ) (hv : v ∈ ForwardTube d m) :
    @inner ℂ _ _ (analytic_state u hu) (analytic_state v hv) =
      (W_analytic_BHW Wfn (n + m)).val (...joint(u^*, v) form...)
```
Plus stubs for holomorphy and boundary recovery.

**Why this was thought to work** (theoretical, has not been validated):
- Layers 3 (Bochner integration) and 4 (cluster-glue) would consume the stubs as black boxes.
- Closing `RuelleClusterBound.lean:718` would become immediately tractable structurally — we'd get a Lean-typechecking proof that uses the stubs.
- Returning to layer 2 to discharge the stubs with real definitions is independent work.

**What actually happened**: the stubs alone are insufficient — the cluster identity requires an OS-reflected variant on the left of the inner product, which Gemini deep-think showed cannot exist as a bounded `GNSHilbertSpace` vector (positive-energy spectrum makes `e^{+τH}` unbounded). The line of stubs is therefore architecturally blocked, not merely incomplete.

**Layer 2 backfill strategy** (when ready to actually construct `Φ`):
- The right approach is via the **GNS representation of the analytically continued Borchers algebra**, NOT via pointwise field at zero.
- Define `Φ(z_1, ..., z_n)` as the equivalence class of a Borchers sequence whose `n`-th block evaluates the analytic continuation of `φ(f_1) ... φ(f_n) Ω` smeared with appropriate analytic test functions parameterized by `z`.
- The bounded `S(y)` from layer 1 acts on the resulting GNS class without ever invoking pointwise fields.
- This is non-trivial Lean engineering but at least does not collide with the operator-valued-distribution domain wall.
- Reference: Streater-Wightman §3.3 (the reconstruction-side construction), Reed-Simon II §IX.8.

**Soft 2-week budget (HISTORICAL — NOT AN APPROVED ESCAPE HATCH)**: if layer 2 backfill stalls, the original plan was to promote the layer-2 stubs to "vetted Path C axioms" added to the trust audit. **Per PR-#88 review (Xi, 2026-05-21), this is not an approved cadence**: any production-axiom adoption requires (a) explicit Xi approval on the specific axiom statement, (b) independent vetting per the project's established certification, (c) consistency with the "no QFT-specific production axioms" PR-#86 discipline. The historical Path-C-promotion of `analytic_state` / `analytic_state_inner` is no longer on the table (those stubs are mathematically contradictory in the OS-reflected variant needed; see retrospective at top of this doc).

#### Sub-pieces

- **L2.1**: define `Φ(z)` using layer 1's `S(y)` interleaved with smeared field operators. Care with operator domains (φ(0) is operator-valued distribution; multiplications need vectors in domain, etc.).
- **L2.2**: prove `Φ(z)` is well-defined as a GNS-Hilbert vector for `z ∈ ForwardTube`.
- **L2.3**: prove `⟨Φ(u), Φ(v)⟩ = W_analytic(joint)` identity. Direct computation via field-operator algebra + analytic continuation of multi-time correlation functions.
- **L2.4**: holomorphy of `z ↦ Φ(z)` and boundary recovery.

**Estimated effort for layer 2**: 1–1.5 weeks.

**File location**: `OSReconstruction/Wightman/Reconstruction/AnalyticHilbertStates.lean` (new).

### Layer 3: Bochner integration of Schwartz-tame Φ-families

**Content**: smear analytic states against Schwartz tests via Bochner integration.

```
For f : SchwartzNPoint d n with OPTR support,
  Ψ_f := ∫ Φ(wick(x)) · f(x) dx ∈ GNSHilbertSpace Wfn
```

Pure Mathlib (`MeasureTheory.Integral.Bochner.Basic`). Need:
- Strong measurability of `x ↦ Φ(wick(x))`.
- Norm bound `‖Φ(wick(x))‖ ≤ K(x)` with `K(x) · |f(x)|` integrable (Schwartz fall-off).

**Estimated effort**: 1–2 days.

### Layer 4: glue + cluster theorem closure

**L4.1**: prove `J(a) = ⟨Ψ_f, U(a) Ψ_g⟩` via Schwartz-Fubini for Hilbert-valued integrals + L2.3 identity.

**L4.2**: split off `Ω`-projections: `Ψ_f = ⟨Ω, Ψ_f⟩·Ω + Ψ_f^⊥` (similarly for `Ψ_g`). Apply `gns_orthogonal_spatial_cobounded_decay_of` (PR #86) to the orthogonal-to-vacuum part. Disconnected limit `⟨Ψ_f, Ω⟩ ⟨Ω, Ψ_g⟩`.

**L4.3**: identify `⟨Ψ_f, Ω⟩` with `L_n` (single-block boundary integral) and `⟨Ω, Ψ_g⟩` with `L_m`.

**L4.4**: replace `RuelleClusterBound.lean:718` `sorry` body with the assembled argument.

**Estimated effort**: 5–8 days.

---

## Total effort estimate

| Layer | Where | Effort |
|-------|-------|--------|
| 1 — PVM functional calc + cone semigroup | hille-yosida (recommended) | 5–10 days |
| 2 — Analytic Hilbert states | OSReconstruction (project-internal) | 1–1.5 weeks |
| 3 — Bochner-smeared states | OSReconstruction (uses Mathlib) | 1–2 days |
| 4 — Glue + closure | OSReconstruction | 5–8 days |
| **Total** | | **3–4 weeks** |

If layer 1 is built project-internal instead (faster but less reusable): subtract ~5 days, total **2.5–3.5 weeks**.

---

## Risks

1. **Layer 1 scope creep**: PVM functional calculus is non-trivial. Operator-valued integration against PVMs requires careful domain analysis. Mathlib doesn't have it; we'd be building it from scratch in hille-yosida.

2. **Layer 2 — analytic-state construction subtleties**: Field operators are operator-valued distributions, not bounded operators. Constructing `φ(z) := S(y) φ(0) S(y)⁻¹` requires interleaving distributional smearing with bounded operator action; domain considerations are technical. Reed-Simon II §IX.8 has the textbook treatment but Lean formalization is unprecedented in the project.

3. **Layer 4 — `⟨Ω, Ψ_f⟩ = L_n` identification**: needs careful handling of the boundary recovery for `Φ(wick(x))` as Im → 0+, plus the Wightman boundary-value clause from `Wfn.spectrum_condition`. Mostly mechanical but multiple Schwartz / Bochner / boundary lemmas to thread.

4. **Strong measurability of `x ↦ Φ(wick(x))`** (layer 3): Schwartz functions are continuous, so this should follow from continuity of the construction in `x`, but pinning down "continuity in `x`" of the Hilbert-vector valued state requires care — analytic vector machinery.

**Risk mitigation**: each layer is independently testable. After layer 1 is shipped (potentially merged into hille-yosida main), layer 2 builds on a stable foundation. After layer 2, layers 3–4 are mechanical.

---

## Strategic decisions (Gemini-vetted, 2026-05-10)

1. **Layer 1 home**: build **project-internal first** in `OSReconstruction/GeneralResults/PVMConeSemigroup.lean`. Refactor to hille-yosida after OS4 cluster closes — extraction is mechanical because layer 1 has no Wightman dependencies (only SNAG axiom + ProjectionValuedMeasureOn type, both already in `GeneralResults/`).

2. **Branch strategy**: fork `r2e/cluster-ibp-rework` from current `r2e/ruelle-poly-bound-chain` head **today**. Clean isolation between the chain-repair work (functional-analytic / FL hygiene) and the Hilbert-space rewrite (operator-algebraic).

3. **Coordination with Xi**: ping **immediately** with a short summary of the pivot. He may have unpushed local WIP for analytic states or strong opinions on operator domains. Recommended message:
   > Heads up — I'm pivoting the cluster-proof closure away from the dominator/IBP plan. The boundary regulator introduces a non-integrable codim-1 singularity, breaking the pointwise dominator. The Euclidean FL representation also blows up due to the unconstrained junction time difference between f's and g's OPTR supports. New plan: route through the Wightman reconstruction identity and Bochner integration in the GNS Hilbert space (Streater-Wightman §3.3 / Reed-Simon II §IX.8). Ping me if you have unpushed analytic-state machinery — `Φ(z) ∈ GNSHilbertSpace` for `z ∈ ForwardTube` — or strong opinions on operator domains for the construction. Plan doc: `docs/cluster_ibp_rework_plan.md` on `r2e/ruelle-poly-bound-chain`.

4. **Chain-repair PR**: open today against `xiyin137/main` with the three commits `ebd007f`, `050449b`, `973617a`. They are mathematically sound, independently useful relaxations; merging them prevents bit-rot while we tackle the Hilbert-space rewrite.

5. **2-week timebox (HISTORICAL)**: the original plan budgeted 1–2 weeks on layers 1+2 combined, with a "ripcord" path promoting the layer-2 stubs to "vetted Path C axioms." Per PR-#88 review (Xi, 2026-05-21), this ripcord is **not an approved escape hatch** — production-axiom adoption requires explicit per-axiom approval. Moreover, the underlying mathematical issue with the OS-reflected variant of these stubs (see top-of-doc retrospective) makes the ripcord obsolete regardless. The historical text below is preserved for the architectural record but should not be treated as an authorized fallback.

### What's still open

- **Pace of layer 4 cluster-glue against stubs**: even with stubs unblocking layers 3–4 immediately, there's nontrivial work in routing the `Ω`-projection split through the existing `gns_orthogonal_spatial_cobounded_decay_of`. Tracking estimate: 5–8 days.

- **Whether the chain-repair PR should go to xiyin137/main or stage on mrdouglasny/OSreconstruction first**: per CLAUDE.md "shared repo" policy, mrdouglasny first → PR to xiyin137 unless the change is small and self-contained. The chain-repair changes the `bv_implies_fourier_support` axiom signature; that's an interface change, so PR-against-xiyin137 path applies. Direct PR to xiyin137/main is the right move.

---

## Appendix: Layer-4 sketch against stubs (verification)

**Purpose**: verify the stub interface is sufficient for layer 4's cluster glue, before committing to the full GNS-Bochner pivot.

### Precise stub interface required

```lean
-- Core: existence of analytic states.
axiom analytic_state {n : ℕ} (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d n) :
    GNSHilbertSpace Wfn

-- Core: inner product = W_analytic on joint PET configs.
-- Note convention: u corresponds to z̄_n,...,z̄_1; v to z_{n+1},...,z_{n+m}.
axiom analytic_state_inner {n m : ℕ}
    (u : Fin n → Fin (d + 1) → ℂ) (hu : u ∈ ForwardTube d n)
    (v : Fin m → Fin (d + 1) → ℂ) (hv : v ∈ ForwardTube d m)
    (hPET : (Fin.append (fun k => starRingEnd ℂ ∘ u (Fin.rev k)) v) ∈
       PermutedExtendedTube d (n + m)) :
    @inner ℂ _ _ (analytic_state u hu) (analytic_state v hv) =
      (W_analytic_BHW Wfn (n + m)).val
        (Fin.append (fun k => starRingEnd ℂ ∘ u (Fin.rev k)) v)

-- Auxiliary: continuity needed for Bochner integrability.
axiom analytic_state_continuous {n : ℕ} :
    ContinuousOn (fun z : Fin n → Fin (d + 1) → ℂ =>
      ∃ hz : z ∈ ForwardTube d n, analytic_state z hz)
      (ForwardTube d n)
-- (Lifted appropriately to handle the dependent type.)

-- Auxiliary: norm bound (follows from ‖S(y)‖ ≤ 1 in the actual construction).
axiom analytic_state_norm_bound {n : ℕ} (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d n) :
    ‖analytic_state z hz‖ ≤ K_n  -- some constant depending on n; could even be 1.

-- Boundary recovery (needed to identify L_n with ⟨Ω, Ψ_f⟩):
-- For OPTR-supported f, the smeared single-block analytic state has
-- ⟨Ω, Φ(wick(x))⟩ = W_analytic(wick(x))  [single-config form of analytic_state_inner].
-- This is implied by analytic_state_inner with empty u side.
```

### Layer-4 proof sketch

```lean
-- Given:
--   f : SchwartzNPoint d n, OPTR-supported
--   g : SchwartzNPoint d m, OPTR-supported
--   ε > 0
-- Goal: ∃ R, ∀ a (a 0 = 0, |⃗a| > R), ‖J(a) - L_n · L_m‖ < ε

-- (1) Define Bochner-integrated states (layer 3).
let Ψ_f : GNSHilbertSpace Wfn :=
  ∫ x : NPointDomain d n, f.toFun x • analytic_state (wick(x)) (...)
  -- requires: continuity + norm bound from stubs + Schwartz integrability.
let Ψ_g : GNSHilbertSpace Wfn :=
  ∫ x : NPointDomain d m, g.toFun x • analytic_state (wick(x)) (...)

-- (2) J(a) = ⟨Ψ_f, U(a) Ψ_g⟩.
-- Schwartz-Fubini for Hilbert-valued integrals + analytic_state_inner identity:
have h_J_eq : ∀ a, J(a) = @inner ℂ _ _ Ψ_f
    (poincareActGNS Wfn (PoincareGroup.translation' a) Ψ_g) := by
  intro a
  -- Schwartz-Fubini: ⟨∫ Φ_x f(x) dx, U(a) ∫ Φ_y g(y) dy⟩
  --   = ∫∫ ⟨Φ_x, U(a) Φ_y⟩ f(x) g(y) dx dy
  --   = ∫∫ analytic_state_inner(...wick(x), wick(y)+(0,a)...) f(x) g(y) dx dy
  --   = ∫∫ W_analytic(...) f(x) g(y) dx dy
  --   = J(a)
  sorry  -- mechanical via Schwartz-Fubini + stubs

-- (3) Split off Ω-projections.
let cf : ℂ := @inner ℂ _ _ (gnsVacuum Wfn) Ψ_f  -- "L_n" candidate (modulo conjugation)
let cg : ℂ := @inner ℂ _ _ (gnsVacuum Wfn) Ψ_g
let Ψ_f_perp : GNSHilbertSpace Wfn := Ψ_f - (starRingEnd ℂ cf) • gnsVacuum Wfn
let Ψ_g_perp : GNSHilbertSpace Wfn := Ψ_g - cg • gnsVacuum Wfn
-- Both Ψ_f_perp, Ψ_g_perp are orthogonal to gnsVacuum.

-- (4) Apply cluster decay to (Ψ_f_perp, Ψ_g_perp).
-- ⚠️  GAP: gns_orthogonal_spatial_cobounded_decay_of REQUIRES
--     L2SpectralData Wfn Ψ_f_perp Ψ_g_perp.
--     This is NOT automatic — need to construct or supply.
--
-- Three options:
--   (a) Construct L2SpectralData from SNAG + polarization + AC marginal claim
--       for OUR specific Bochner-derived states. Real work.
--   (b) Add another stub axiom: bochner_state_l2_data.
--       Path-C-style; expands trust surface.
--   (c) Use gns_cluster_completion (ray decay only, on PreHilbertSpace).
--       Bochner states are in completion, not necessarily PreHilbert.
--       Need lift PreHilbert ray decay → completion cobounded decay.

-- Assuming (a) or (b):
have hL2 : L2SpectralData Wfn Ψ_f_perp Ψ_g_perp := <stub or constructed>

have h_perp_decay :
    Tendsto (fun a : SpacetimeDim d =>
      @inner ℂ _ _ Ψ_f_perp
        (poincareActGNS Wfn (PoincareGroup.translation' a) Ψ_g_perp))
      (Filter.principal {a | a 0 = 0} ⊓ Bornology.cobounded _) (𝓝 0) :=
  gns_orthogonal_spatial_cobounded_decay_of Wfn Ψ_f_perp Ψ_g_perp hL2

-- (5) Decompose ⟨Ψ_f, U(a) Ψ_g⟩ via the projection split.
-- ⟨Ψ_f, U(a) Ψ_g⟩
--   = ⟨cf·Ω + Ψ_f_perp, U(a) (cg·Ω + Ψ_g_perp)⟩
--   = ⟨cf·Ω, cg · U(a) Ω⟩ + ⟨cf·Ω, U(a) Ψ_g_perp⟩
--     + ⟨Ψ_f_perp, cg · U(a) Ω⟩ + ⟨Ψ_f_perp, U(a) Ψ_g_perp⟩
--   = (starRingEnd cf · cg · ⟨Ω, U(a) Ω⟩)
--     + cg · ⟨cf·Ω, U(a) Ω⟩  -- wait: U(a) Ψ_g_perp not Ω
-- Need to use vacuum_invariant: U(a) Ω = Ω.
--   ⟨Ψ_f_perp, U(a) Ω⟩ = ⟨Ψ_f_perp, Ω⟩ = 0 (since Ψ_f_perp ⊥ Ω).
--   ⟨Ω, U(a) Ψ_g_perp⟩ = ⟨U(a)* Ω, Ψ_g_perp⟩ = ⟨Ω, Ψ_g_perp⟩ = 0.
-- So:
--   ⟨Ψ_f, U(a) Ψ_g⟩ = starRingEnd cf · cg + ⟨Ψ_f_perp, U(a) Ψ_g_perp⟩

have h_split : ∀ a, @inner ℂ _ _ Ψ_f
    (poincareActGNS Wfn (PoincareGroup.translation' a) Ψ_g) =
    starRingEnd ℂ cf * cg +
    @inner ℂ _ _ Ψ_f_perp
      (poincareActGNS Wfn (PoincareGroup.translation' a) Ψ_g_perp) := by
  intro a
  -- Vacuum invariance: U(a) Ω = Ω.
  -- ⟨Ψ_f_perp, Ω⟩ = 0 (by construction of Ψ_f_perp).
  -- Linearity of inner product, expand the four-term sum.
  sorry  -- mechanical

-- (6) Combine: J(a) → starRingEnd cf · cg as |⃗a| → ∞.
have h_J_decay :
    Tendsto (fun a => J(a))
      (Filter.principal {a | a 0 = 0} ⊓ Bornology.cobounded _)
      (𝓝 (starRingEnd ℂ cf * cg)) := by
  rw [show (starRingEnd ℂ cf * cg : ℂ) = starRingEnd ℂ cf * cg + 0 by ring]
  exact (h_J_eq ▸ h_split ▸ (Tendsto.add tendsto_const_nhds h_perp_decay))

-- (7) Identify the limit with L_n · L_m.
-- L_n = ∫ W_analytic_BHW (wick x) f(x) dx = ∫ ⟨Ω, Φ(wick x)⟩ f(x) dx
--     = ⟨Ω, ∫ Φ(wick x) f(x) dx⟩ = ⟨Ω, Ψ_f⟩ = cf.
-- (Linearity of inner product over Bochner integral; uses analytic_state_inner with empty v.)
have h_L_n_eq : L_n = cf := sorry
have h_L_m_eq : L_m = cg := sorry  -- analogous; depends on convention.

-- (8) Convert Tendsto to ε-R form.
-- Standard cobounded → ε-R extraction (already done in PR #86 patterns).
sorry
```

### Stub-interface findings

**Sufficient (with caveats)**:
- `analytic_state` + `analytic_state_inner` — needed for J(a) = ⟨Ψ_f, U(a) Ψ_g⟩ identity.
- `analytic_state_continuous` — needed for Bochner integrability (strong measurability via continuity).
- `analytic_state_norm_bound` — needed for Bochner integrability (norm-bound × Schwartz fall-off ⇒ integrable).

**Identified gap**:
- ⚠️ **`gns_orthogonal_spatial_cobounded_decay_of` requires `L2SpectralData` per pair of states.** For our Bochner-derived `Ψ_f_perp, Ψ_g_perp`, this isn't free. Either:
  - Construct L2SpectralData via SNAG + polarization + AC marginal for these specific states. **Real work** — uses analytic-state machinery to identify Bochner-integrated states with smeared field-operator states, then SNAG joint PVM gives the spectral measure.
  - Add a stub axiom `bochner_state_l2_data` for these states (Path-C-style).
  - Use `gns_cluster_completion` (older theorem, ray decay on `PreHilbertSpace`) and lift to cobounded — needs Bochner states to be in PreHilbert (might not be) and ray-to-cobounded lift work.

This adds **~3–5 days** to layer 4 (option a) or **a new vetted axiom** (option b) or **lift work** (option c).

### Verification verdict

The GNS-Bochner pivot IS Lean-feasible against the proposed stubs, modulo the L2SpectralData supply for the Bochner-derived states. The math is sound; the Lean engineering has identified obstacles but they're navigable.

**Updated risk assessment**:
- Layer 1 (scalarization): low risk, ~3 days.
- Layer 2 (stubs deferred): low risk, ~1 day to define stubs.
- Layer 3 (Bochner integration): low-medium risk, ~2 days, dependent on stub continuity property.
- Layer 4 (cluster glue): **medium-high risk** — the L2SpectralData supply is the load-bearing piece. Original 5–8 day estimate likely needs 7–10 days with the additional sub-task.

**Updated total**: 3–4 weeks, with the L2SpectralData construction being the highest-risk sub-piece.

**Mitigation (HISTORICAL)**: the original plan listed promotion to a stub axiom as the fallback if option (a) stalled. Per PR-#88 review, that promotion is not pre-authorized; would require explicit approval as discussed at top of doc.

---

## Pre-reqs already in place

- ✅ `Wfn.spectrum_condition_compact_subset` (`973617a`) — satisfiable form for new code paths.
- ✅ `bv_implies_fourier_support` relaxed (`ebd007f`) — though not used by GNS-Bochner route.
- ✅ `gns_cluster_completion`, `gns_orthogonal_spatial_cobounded_decay_of` (PR #86).
- ✅ `poincareActGNS` Poincaré rep on GNS.
- ✅ `WightmanInnerProduct` Borchers-sequence pairing.
- ✅ SNAG axiom + `ProjectionValuedMeasureOn α H` type.
- ✅ Wightman field operator `φ` infrastructure on GNS (smeared form).
- ❌ Layer 1 — PVM functional calculus + bounded `e^{-yP}` semigroup.
- ❌ Layer 2 — analytic Hilbert states `Φ(z)`.

---

## Why this matters beyond OS4

Once layer 1 is in hille-yosida and layer 2 in OSReconstruction:

- **Future modular theory work** (Tomita-Takesaki for vacuum states, Bisognano-Wichmann) inherits layer 1 directly. The modular operator `Δ^z` is exactly a PVM-derived bounded family on a strip.
- **Future Haag-Kastler formalizations** can build analytic-state machinery on local algebras using the same layer 1 (Borchers' theorem on positive-spectrum analyticity is a direct application).
- **JLW-style rigorous QFT models** (2D N=2 Wess-Zumino on cylinder, etc.) need analytic Hilbert states for index-theorem pairings; layer 2's framework adapts model-by-model.
- **Connes-style entire cyclic cohomology** uses analytic-vector traces with similar bounded `Δ^z` structures.

The 3–4 weeks is a real cost, but the infrastructure pays off for any future analytic-vector / spectral-decomposition work. For projects beyond OS4 cluster, layer 1 + layer 2 is a foundational layer.

**Pragmatic alternative (HISTORICAL)**: the original plan listed "drop to Path C (axiomatize the joint-integral cluster directly)" as a 3-5 day fallback. **Per PR-#88 review (Xi, 2026-05-21), Path-C-style production-axiom adoption is not pre-authorized**; it requires explicit per-axiom approval and independent vetting (see top-of-doc retrospective). Do not interpret this paragraph as license to ship a new QFT-specific axiom without that approval cadence.
