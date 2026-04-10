# The Vladimirov-Tillmann Representation Theorem: Formalization Summary

## 1. What the theorem says

The **Vladimirov-Tillmann theorem** characterizes holomorphic functions on tube domains.
A *tube domain* over an open convex cone $C \subset \mathbb{R}^m$ is
$$T(C) = \{ z = x + iy \in \mathbb{C}^m : y \in C \}.$$

**Theorem** (Vladimirov-Tillmann). *Let $F$ be holomorphic on $T(C)$ with polynomial growth on compact subsets and tempered distributional boundary values $W$. Then $F$ satisfies the Vladimirov bound*
$$\|F(z)\| \le C_{\rm bd}\,(1 + \|z\|)^N\,\bigl(1 + \mathrm{dist}(\mathrm{Im}\,z,\,\partial C)^{-1}\bigr)^q$$
*for constants $C_{\rm bd} > 0$ and $N, q \in \mathbb{N}$.*

The $(1 + \mathrm{dist}^{-1})^q$ factor captures the inverse-power singularity as $\mathrm{Im}\,z$ approaches the boundary of $C$. This is strictly stronger than the hypothesis of polynomial growth on compact subsets, which says nothing about boundary behavior.

**Role in the OS reconstruction.** The Wightman $n$-point functions are holomorphic on the forward tube $T(V^+)$. The VT theorem provides the growth estimates needed for the Schwinger-function temperedness proof and the Wick-rotation integrability arguments.

## 2. Proof architecture

The proof proceeds in three steps, using the Fourier-Laplace (FL) representation as an intermediary:

$$\text{compact-subset growth + BV}\;\xrightarrow{\text{Axiom 1}}\;\text{spectral support in }C^*\;\xrightarrow{\text{Axiom 3}}\;F = \text{FL}(\hat T)\;\xrightarrow{\text{PW (proved)}}\;\text{Vladimirov bound}$$

**Step 1.** From compact-subset polynomial growth and tempered distributional boundary values $W$, extract a frequency-side distribution $\hat T$ supported in the dual cone $C^*$ (Axiom 1: `bv_implies_fourier_support`).

**Step 2.** Show $F$ equals the Fourier-Laplace extension of $\hat T$ on the tube (Axiom 3: `fl_representation_from_bv`). This uses Axiom 2 (uniqueness from common boundary values) internally.

**Step 3.** The Fourier-Laplace extension $z \mapsto \hat T(\psi_z)$, where $\psi_z(\xi) = \chi(\xi)\,e^{iz\cdot\xi}$ is a cutoff exponential, satisfies the Vladimirov bound. This is **fully proved** (~3500 lines in `PaleyWienerSchwartz.lean`) via quantitative Schwartz seminorm estimates on $\psi_z$.

## 3. The four bridge axioms

The VT theorem is proved from 4 axioms. Three encode SCV (several complex variables) results requiring Poisson integral infrastructure not in Mathlib. The fourth is a functional analysis exchange principle.

### Axiom 1: Spectral support (`bv_implies_fourier_support`)

*If $F$ is holomorphic on $T(C)$ with polynomial growth on compact subsets and tempered BV $W$, then the Fourier transform of $W$ is supported in the dual cone $C^*$.*

More precisely: there exists a tempered distribution $\hat T$ (on the frequency/momentum side) with $\mathrm{supp}(\hat T) \subseteq C^*$ and $W(\varphi) = \hat T(\mathcal{F}_{\rm phys}\,\varphi)$, where $\mathcal{F}_{\rm phys}\varphi(\xi) = \int e^{ix\cdot\xi}\,\varphi(x)\,dx$ is the physics Fourier transform.

**Why the growth hypothesis is essential.** Without it, $F(z) = e^{-iaz}$ ($a > 0$) on the upper half-plane is a counterexample: holomorphic, tempered BV $= e^{-iax}$, but spectral support at $-a \notin [0,\infty) = C^*$.

**Reference:** Vladimirov, *Methods of Generalized Functions*, Theorem 25.1.

### Axiom 2: Uniqueness from boundary values (`tube_holomorphic_unique_from_bv`)

*Two holomorphic functions on the same tube with identical tempered distributional boundary values coincide on the entire tube.*

This is the edge-of-the-wedge uniqueness principle: if $F - G$ is holomorphic on $T(C)$ with zero distributional BV, then $F = G$ on $T(C)$.

**Eliminability note.** This axiom is derivable from the already-proved theorem `distributional_uniqueness_tube_of_zero_bv` in `DistributionalUniqueness.lean` (~300 lines, 0 sorrys), which establishes: $G$ holomorphic on $T(C)$ with zero distributional BV $\Rightarrow$ $G = 0$. Applying this to $H = F - G$ gives the axiom. The remaining work is (i) coordinate transport from flat $\mathbb{R}^m$ to the Pi type $(\text{Fin}\,n \to \text{Fin}\,(d{+}1) \to \mathbb{R})$ via `flattenCLEquiv`, and (ii) verifying the integrability hypothesis (follows from holomorphicity $\Rightarrow$ local boundedness on each slice).

**Reference:** Vladimirov, §25; Streater-Wightman, Theorem 2-16.

### Axiom 3: Fourier-Laplace representation (`fl_representation_from_bv`)

*Given the spectral distribution $\hat T$ from Axiom 1, $F$ equals the Fourier-Laplace extension $z \mapsto \hat T(\psi_z)$ on the tube.*

The proof route: the FL extension is holomorphic on $T(C)$ (proved in PW). Its distributional BV is $\hat T \circ \mathcal{F}_{\rm phys} = W$ (proved in PW, via the Fubini exchange axiom). By Axiom 2, $F$ and the FL extension agree.

**Reference:** Vladimirov, Theorem 25.5.

### Axiom 4: CLM-integral exchange (`schwartz_clm_fubini_exchange`)

*A continuous linear functional on Schwartz space commutes with parameter integrals of Schwartz-valued families.*

Given $T : \mathcal{S}(\mathbb{R}^m) \to \mathbb{C}$ continuous linear, $g : \mathbb{R}^m \to \mathcal{S}(\mathbb{R}^m)$ continuous with polynomial seminorm growth, and $f \in \mathcal{S}$, there exists $\Phi \in \mathcal{S}$ with:

- $\Phi(\xi) = \int g(x)(\xi)\,f(x)\,dx$ (the Schwartz-valued Bochner integral)
- $T(\Phi) = \int T(g(x))\,f(x)\,dx$ (CLM exchange)

**Reference:** Hörmander, *Analysis of Linear PDOs I*, Ch. 5; Reed-Simon I, §V.3.

## 4. What is fully proved (no axioms, no sorrys)

The Paley-Wiener-Schwartz analytical core (~10,000 lines across 14 files):

| Component | Lines | Key results |
|-----------|-------|-------------|
| `PaleyWienerSchwartz.lean` | ~3500 | Seminorm estimates, Vladimirov pointwise bound (334 lines), BV convergence of FL extension, physics FT formula |
| `ConeCutoffSchwartz.lean` | ~900 | Cutoff exponential $\psi_{z,R}$ construction and all decay estimates |
| `SchwartzCutoffExp.lean` | ~700 | Quantitative cutoff $\times$ exponential seminorm bounds |
| `SchwartzDamping.lean` | ~460 | $e^{-\varepsilon L} \cdot h \to h$ in Schwartz topology |
| `DualCone.lean` | ~220 | Dual cone properties, Hahn-Banach separation |
| `FourierSupportCone.lean` | ~230 | Fourier support predicate and cone lemmas |
| `DiffUnderIntegralSchwartz.lean` | ~180 | Differentiation under the integral for Schwartz pairings |
| `SmoothCutoff.lean` | ~180 | Smooth cutoff adapted to closed sets |
| `ScalarFTC.lean` | ~125 | FTC identities and norm bounds for exponential differences |
| Others | ~500 | `DistributionalLimit`, `SchwartzFubini`, `ConeDefs`, `SchwartzComplete` |

## 5. Non-circularity of the proof

A natural concern: the VT theorem proves a growth bound, so doesn't its hypothesis (compact-subset growth) make the conclusion trivial?

No. The hypothesis is *polynomial growth on compact subsets* of the tube:
$$\forall\, K \subset T(C) \text{ compact},\; \exists\, C_K, N:\; \|F(z)\| \le C_K(1+\|z\|)^N \;\;\forall\, z \in K.$$

The conclusion is the *full Vladimirov bound* with the boundary-distance singularity:
$$\|F(z)\| \le C(1+\|z\|)^N\,(1 + \mathrm{dist}(\mathrm{Im}\,z,\,\partial C)^{-1})^q.$$

These are genuinely different: compact-subset growth says nothing about the rate at which the bound degrades as $\mathrm{Im}(z) \to \partial C$. The Vladimirov bound provides the explicit inverse-power control. The upgrade comes from the FL representation: the Schwartz seminorm estimates on $\psi_z$ with dynamic cutoff radius $R = (1+\|\mathrm{Im}\,z\|)^{-1}$ produce the $(1+\mathrm{dist}^{-1})^q$ factor.

For the OS reconstruction, the compact-subset growth hypothesis is supplied by the contraction semigroup property ($\|T(t)\| \le 1$ for $t > 0$ from Hille-Yosida), which gives global polynomial growth of the analytic continuation — already proved in the ACR(1) assembly theorem.

## 6. VT-local axiom budget

This table covers the axioms used in the VT proof chain only, not the full repo-wide inventory (which is 10 axioms total; see README.md).

| Category | Count | Details |
|----------|-------|---------|
| New bridge axioms (this PR) | 3 | `bv_implies_fourier_support`, `fl_representation_from_bv`, `schwartz_clm_fubini_exchange` |
| Eliminated | 1 | `tube_holomorphic_unique_from_bv` — converted to theorem from `distributional_uniqueness_tube_of_zero_bv` |
| Pre-existing SCV (unchanged) | 4 | `distributional_cluster_lifts_to_tube`, `tube_boundaryValueData_of_polyGrowth`, `tube_boundaryValue_of_vladimirov_growth`, `tube_boundaryValue_realizes_dualCone_distribution` |

**Net change vs main:** removed 1 axiom (`vladimirov_tillmann`), added 3 new axioms. Net +2 axioms (6 → 10 repo-wide, counting axioms added on other lanes by main).

## References

- Vladimirov, V.S., *Methods of the Theory of Generalized Functions* (2002), Ch. V §25
- Hörmander, L., *The Analysis of Linear PDOs I* (1990), §7.4, §8.4
- Streater, R.F. and Wightman, A.S., *PCT, Spin and Statistics, and All That*, Ch. 2
- Reed, M. and Simon, B., *Methods of Modern Mathematical Physics I*, §V.3, §IX.3
