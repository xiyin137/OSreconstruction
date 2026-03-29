# Comprehensive Mathematical Reading Note: Osterwalder-Schrader Reconstruction Theorem

**Purpose:** Deep mathematical exposition of the complete proof of the OS reconstruction theorem, with precise references to the original papers, for supervising the Lean 4 formalization.

**Author:** Claw  
**Date:** 2026-03-28  
**Primary References:**  
- OS I: Osterwalder & Schrader, "Axioms for Euclidean Green's Functions" (Comm. Math. Phys. 31, 83–112, 1973)  
- OS II: Osterwalder & Schrader, "Axioms for Euclidean Green's Functions II" (Comm. Math. Phys. 42, 281–305, 1975)  
- Streater & Wightman, *PCT, Spin and Statistics, and All That*  

---

## Part I: The Axiom Systems

### 1. Test Function Spaces (OS I §2)

The precise function spaces are critical for the formalization.

**°S(R^{4n}):** Schwartz functions f on R^{4n} such that f and all derivatives vanish when xᵢ = xⱼ for any i < j. This is a **closed** subspace of S(R^{4n}). The Euclidean Green's functions are distributions on this space — they are defined away from coincident points.

**S₊(R^{4n}):** Subspace of °S where f^{(α)}(x₁,...,x_n) = 0 unless 0 < x₁⁰ < x₂⁰ < ··· < x_n⁰. These are the positive-time test functions.

**S(R̄₊):** The quotient space S(R)/S(R₋), a Fréchet space. An element f₊ is an equivalence class. Two equivalent systems of seminorms (OS I Lemma 8.1):
```
|f₊|'_m = inf_{g ∈ S(R₋)} |f + g|_m       (quotient definition, eq. 2.1)
|f₊|''_m = sup_{x≥0, α≤m} (1+x²)^{m/2} |f^{(α)}(x)|   (restriction definition, eq. 2.2)
```

**Sequence spaces:** S = ⊕_n S(R^{4n}), with elements **f** = {f₀, f₁, f₂,...}, f₀ ∈ C, finitely many nonzero.

**Involutions on S:**
- **f → f*:** f*_n(x₁,...,x_n) = f̄_n(x_n,...,x₁) (conjugation + argument reversal)
- **f → Θf:** (Θf)_n(x₁,...,x_n) = f_n(ϑx₁,...,ϑx_n), where ϑx = (−x⁰, **x**) (time reflection)

**Cross product:** (f × g)_n = Σ_{k=0}^n f_{n-k} × g_k. Key property: for f, g ∈ S₊, we have (Θf*) × g ∈ S₋.

### 2. The Euclidean Axioms (OS I §3)

The Euclidean Green's functions are a sequence {S_n}_{n=0}^∞ of distributions:

**E0 (Distributions):** S₀ ≡ 1. S_n ∈ °S'(R^{4n}) for n ≥ 1.

**E1 (Euclidean invariance):** S_n(f) = S_n(f_{(a,R)}) for all R ∈ SO(4), a ∈ R⁴.

**E2 (Osterwalder-Schrader positivity):**
```
Σ_{n,m} S_{n+m}(Θf_n* × f_m) ≥ 0   for all f ∈ S₊
```

**E3 (Symmetry):** S_n(f) = S_n(f^π) for all permutations π ∈ P_n.

**E4 (Cluster property):**
```
lim_{λ→∞} Σ_{n,m} {S_{n+m}(Θf_n* × g_{m(λa,1)}) − S_n(Θf_n*) S_m(g_m)} = 0
```
for all f, g ∈ S₊, a = (0, **a**) spatial.

### 3. The Wightman Axioms (OS I §3)

The Wightman distributions {W_n} satisfy:

**R0 (Temperedness):** W_n ∈ S'(R^{4n}).

**R1 (Poincaré invariance):** W_n(f) = W_n(f_{(a,Λ)}) for (a,Λ) ∈ P↑₊.

**R2 (Wightman positivity):** Σ_{n,m} W_{n+m}(f_n* × g_m) ≥ 0.

**R3 (Local commutativity):** W_n(...,fⱼ,f_{j+1},...) = W_n(...,f_{j+1},fⱼ,...) when supp(fⱼ) and supp(f_{j+1}) are spacelike separated.

**R4 (Cluster property):** lim_{λ→∞} {W_{n+m}(f × g_{(λa,1)}) − W_n(f) W_m(g)} = 0 for a spacelike.

**R5 (Spectral condition):** The Fourier transform Ŵ_{n-1}(p₁,...,p_{n-1}) has support in the product of closed forward cones: supp Ŵ_{n-1} ⊂ V̄₊^{n-1}.

### 4. Key Observation: Spectral Condition is Free

OS I Remark after Theorem R→E: The spectral condition R5 is a **consequence** of E0, E1, E2 alone — it does not require a separate Euclidean axiom. This is because the semigroup construction (from E2) and the Fourier-Laplace representation (from E0) automatically produce distributions supported in the forward cone.

### 5. The Main Theorems (OS I §3)

**Theorem E→R:** E0–E4 ⟹ unique Wightman distributions satisfying R0–R5.

**Theorem R→E:** R0–R5 ⟹ unique Euclidean Green's functions satisfying E0–E4.

**Uniqueness caveat (OS I Remark 1):** The correspondence is unique because we work in °S' (distributions on the off-diagonal). Two sequences agreeing in °S' lead to the same Wightman distributions. Wightman distributions contain NO information about Euclidean Green's functions at coincident points.

---

## Part II: The OS I Error and OS II Correction

### 6. What Went Wrong in OS I

**The flawed step:** OS I Lemma 8.8 claimed that if a function is the Laplace transform of a tempered distribution in each variable separately, then it is the joint Laplace transform. Simon [16] first questioned this, and R. Schrader found the explicit counterexample (OS II §1):

```
F(x,y) = exp(−xy),   x > 0, y > 0
```

This is the Laplace transform of a tempered distribution in x (for each fixed y > 0) and in y (for each fixed x > 0), but NOT the joint Laplace transform of any tempered distribution on R₊².

**Consequence:** The conditions E0–E4 are necessary for a Wightman theory, but whether they are sufficient became an open question. The specific failure: Lemma 8.8 was used to continue S_k from separate one-variable holomorphic extensions to a joint holomorphic function on C₊^k.

### 7. Three Levels of Growth Control (OS II §2–4)

OS II distinguishes three distribution conditions:

**E0 (original):** S_n ∈ °S'(R^{4n}). Temperedness. Sufficient for the semigroup construction but not for the full E→R direction.

**Ě0 (strong, OS II Chapter III):** S_{n-1} ∈ Š'(R^{4(n-1)}₊), where the topology is pulled back from the Fourier-Laplace transform side. This **immediately implies** the existence of Ŵ_{n-1} with correct support — it is essentially the condition that the broken Lemma 8.8 was supposed to derive from E0.

OS II states explicitly: "Although Ě0 restores the equivalence theorem, this new condition is not very satisfactory from the point of view of applications... the continuity of S_{n-1} with respect to the |·|ˇ_p-norms seems difficult to check."

**E0' (linear growth, OS II Chapter IV):** There exist s ∈ Z₊ and a sequence {σ_n} of factorial growth (σ_n ≤ α(n!)^β) such that:
```
|S_n(f)| ≤ σ_n |f|_{n·s}   for all f ∈ S₀(R^{4n})
```

The critical feature: the seminorm index is **n·s** — growing **linearly** in n. The fixed integer s is independent of n.

**E0'' (stronger, OS II Remark after Theorem 4.3):** A slightly stronger pointwise condition. OS II notes that assuming E0'' instead of E0' makes the temperedness arguments in Chapter VI much shorter.

### 8. The Corrected Main Theorem (OS II Theorem 4.3)

**Theorem (OS II):** E0', E1–E4 are necessary and sufficient conditions for Euclidean Green's functions to define a unique Wightman field theory satisfying R0–R5.

**The conceptual split in OS II:**
- **Chapter V (Continuation):** Uses only E0, E1, E2 to construct analytic continuation
- **Chapter VI (Temperedness):** Uses E0' to establish polynomial growth bounds

---

## Part III: E → R Direction — The Complete Proof

### 9. Difference Variables (OS I eq. 4.1, OS II eq. 2.3)

From E1 (translation invariance), the Schwinger functions depend only on differences:
```
S_n(x₁,...,x_{n+1}) = S_n(x₂−x₁,...,x_{n+1}−x_n)   for x₁⁰ < x₂⁰ < ··· < x_{n+1}⁰   (OS I 4.1)
```

The difference-variable Schwinger functions S_n(ξ₁,...,ξ_n) live on R^{4n}₊ = {ξ : ξⱼ⁰ > 0}.

**Restricted SO(4) covariance (OS I eq. 4.2):**
```
S_n(Rξ₁,...,Rξ_n) = S_n(ξ₁,...,ξ_n)
```
provided ξ_k⁰ > 0 and (Rξ_k)⁰ > 0 for all k. The rotation R must preserve the positive-time condition.

### 10. The OS Hilbert Space (OS I §4, eqs. 4.3–4.5)

**The sesquilinear form (OS I eq. 4.3):**
```
(f, g) = Σ_{n,m} S_{n+m}(Θf_n* × g_m)
```
for f, g ∈ S₊.

**Properties:**
- Positive semidefinite by E2
- Conjugate-symmetric: (f,g) = (g,f)̄
- Linear in g, antilinear in f

**Null space:** N = {f ∈ S₊ : (f,f) = 0}.

**Physical Hilbert space (OS I eq. 4.4):**
```
H = (S₊/N)^{completion}
```

**Vacuum:** Ω = [{1, 0, 0,...}] ∈ H.

**Key algebraic identity for the inner product:** The cross product structure ensures that (f,g) can be computed from the Schwinger functions evaluated on time-ordered configurations where the "left" times are reflected (negative) and the "right" times are positive.

### 11. The Contraction Semigroup (OS I §4, eqs. 4.6–4.9)

**Time translation:** For t ≥ 0, define (T_t f)_n(x₁,...,x_n) = f_n(x₁−te₀,...,x_n−te₀) where e₀ = (1,0,0,0).

**Properties on H:**

*Semigroup:* T_{t+s} = T_t T_s.

*Self-adjointness:* (T_t f, g) = (f, T_t g). Proof uses θ ∘ T_t = T_{-t} ∘ θ.

*Contraction (OS I eq. 4.9):* ‖T_t‖ ≤ 1. The proof is the beautiful iteration:
```
‖T_t Φ‖² = (T_t Φ, T_t Φ) = (Φ, T_{2t} Φ) ≤ ‖Φ‖ · ‖T_{2t} Φ‖
```
Apply n times: ‖T_t Φ‖ ≤ ‖Φ‖^{1−2^{-n}} · ‖T_{2^n t} Φ‖^{2^{-n}}. Take n → ∞.

*Strong continuity:* From continuity of the Schwinger functions.

**Generator:** By Lumer-Phillips, T_t = e^{−tH} with H ≥ 0 self-adjoint. HΩ = 0.

**Spatial translations (OS I eq. 4.5):** U(**a**) = translation by (0,**a**) gives a unitary group on H commuting with T_t.

### 12. One-Variable Analytic Continuation (OS I §4, eqs. 4.10–4.11)

**The holomorphic semigroup:** T_τ = e^{−τH} for Re(τ) > 0, via the spectral theorem:
```
⟨Ψ, T_τ Φ⟩ = ∫₀^∞ e^{−τλ} d⟨Ψ, E_λ Φ⟩
```
Holomorphic in τ for Re(τ) > 0 (exponential decay of the integrand).

**The key matrix element formula (OS I eq. 4.10):** For Ψ, Φ ∈ H constructed from positive-time test functions:
```
⟨Ψ, T_τ Φ⟩ = analytic continuation of S^{(m)}(t | h_m)
```
where S^{(m)} is the Schwinger function with one time gap t, and h_m packages all remaining variables as parameters.

**Equation 4.11:** Explicitly:
```
S^{(m)}(t, s | h_m) = ⟨Ψ_{h_m}^{left}, e^{−tH} Ψ_{h_m}^{right}⟩
```
For real t > 0 this equals the Schwinger function. The holomorphic extension to Re(τ) > 0 provides analytic continuation of this one-variable object.

**The parametric structure is crucial:** All variables except the one being continued are parameters. This is the **heart of the OS method**.

### 13. The Fourier-Laplace Bridge (OS I §8, Lemmas 8.5–8.7)

**Lemma 8.5 (OS I):** A distribution F(t,s) in S'(R₊ × R^{d}) satisfying the Cauchy-Riemann equations ∂F/∂t = i·∂F/∂s on t > 0 is represented by a holomorphic function G(τ) on Re(τ) > 0.

**Lemma 8.6 (OS I):** A holomorphic G on Re(τ) > 0 with polynomial growth:
```
|G(τ)| ≤ M(1 + |τ|^α) / (Re τ)^β
```
is the Fourier-Laplace transform of a distribution supported in [0,∞).

**Lemma 8.7 (OS I):** Combines: a CR distribution on the half-plane is the Fourier-Laplace transform of a positive-support distribution.

**Lemma 8.8 (OS I, FLAWED):** Attempted to extend from one variable to many variables simultaneously. Counterexample: F(x,y) = e^{−xy}.

### 14. OS II Inductive Continuation (OS II Chapter V)

OS II replaces the flawed Lemma 8.8 with an inductive procedure.

**The corrected approach (OS II Chapter V opening):** Continue only in time variables. Treat spatial variables as parameters. Build the analytic domain inductively.

**Theorem 4.1 (A₀ — Local analyticity):** Using E0, E1, E2:

*Proof ingredients:*

1. **Cone geometry.** Choose direction vectors e₁,...,e₄ in R⁴ such that for each eμ, the one-variable semigroup continuation can be performed.

2. **Semigroup continuation in each direction.** For each eμ, the matrix element ⟨Ψ, T_{t·eμ} Φ⟩ extends holomorphically in t to Re(t) > 0. This gives analyticity in a flat tube in each of 4 directions.

3. **Euclidean covariance (E1).** SO(4) rotations connect the 4 directions, showing the analytic function is the same (by the identity theorem) in the overlapping regions.

4. **Tube theorem (Malgrange-Zerner).** From flat-tube analyticity in 4 independent directions, pass to analyticity on the convex envelope.

**Result:** Local analyticity in all time variables near the real time-ordered domain.

**Lemma 5.1 (OS II — Quantitative analyticity radius):** Explicit polydisc of analyticity around each real point ξ, with radius controlled by:
- ξᵢ⁰ (the time components)
- ξᵢ⁰/|ξᵢ| (the "timelike ratio")

This quantitative control is essential for the temperedness estimates in Chapter VI.

**Theorem 4.2 (A_r → A_{r+1} — Domain enlargement):**

**The (A_N)/(P_N) alternation:**

- **(A_N):** Scalar-valued analytic continuation on domains C_k^{(N)} in the time variables.
- **(P_N):** Hilbert-space-valued vectors Ψ_n(x,ζ) on mixed domains D_n^{(N)} whose scalar products reproduce the analytically continued Schwinger functions.

The alternation:
```
(P_N) → semigroup/Hilbert-space control
     → define next analytic continuation step
     → (A_{N+1}) → scalar analytic function on larger domain
     → construct vectors on larger domain
     → (P_{N+1})
     → ...
```

**Lemma 5.2 (OS II — Domain growth):** The recursively defined domains C_k^{(N)} grow at a quantitative rate.

**Corollary 5.3 (OS II — Full coverage):** Quantitative lower bound on the time-domain coverage at stage N. The union ∪_N C_k^{(N)} = C₊^k (the full product right half-plane).

**Theorem 4.3 (OS II — Full continuation):** Combines: the Schwinger functions, continued through the inductive procedure, are holomorphic on the full product right half-plane C₊^k in the time variables, with spatial variables as parameters.

### 15. Temperedness Estimates (OS II Chapter VI)

**Why needed:** The Chapter V continuation gives holomorphic functions on C₊^k but not polynomial growth bounds. Without bounds, boundary values are not tempered distributions.

**Where E0' enters:** ONLY in Chapter VI — not for the continuation itself.

**Chapter VI.1: The regularization strategy**

*The problem:* Even if S_k(ξ) is real analytic (from Chapter V), polynomial boundedness does not follow formally.

*Step 1 — Regularization:* Use the local analyticity radius from Lemma 5.1. Choose a compactly supported radial mollifier k_ρ in complex directions and a bump function g_ρ. Rewrite S_k(ξ+ζ) as an average of a regularized object T_k via the mean-value theorem for harmonic functions.

*Step 2 — Positivity channeling:* The regularized T_k still satisfies positivity from the OS form. Crucially, T_k can be written as a Hilbert space scalar product:
```
T_k = ⟨Ψ₁, Ψ₂⟩_H
```

*Step 3 — Semigroup bounds:* The matrix element ⟨Ψ₁, e^{−zH} Ψ₂⟩ gives continuation, bounded by:
```
|⟨Ψ₁, e^{−zH} Ψ₂⟩| ≤ ‖Ψ₁‖ · ‖Ψ₂‖
```

*Step 4 — E0' controls the norms:* The linear growth condition gives:
```
‖Ψ₁‖ ≤ σ_n · (...)^s
‖Ψ₂‖ ≤ σ_{k−n+1} · (...)^s
```
with factorial-growth sequences σ_n (σ_n ≤ α(n!)^β) and polynomial dependence on parameters.

The key point: E0' is channeled through Hilbert-space norms. The linear growth of the seminorm index (n·s) ensures the norms of the vectors Ψ₁, Ψ₂ are controlled.

*Step 5 — Four-direction technique:* Continue in 4k linearly independent directions (from the cone geometry in §14). Apply the Malgrange-Zerner theorem and maximum principle.

**Output:** The real-domain temperedness estimate (OS II eq. 4.5).

**Chapter VI.2: Transporting estimates through the induction**

The estimates from VI.1 (real domain) are carried through the inductive domains C_k^{(N)} using:
- The real-domain bound as the base case
- The Chapter V induction for analyticity on larger domains
- Banach-space-valued maximum principle for transport
- Corollary 5.3 for quantitative domain coverage

The functions are viewed as taking values in a Banach space of continuous functions of spatial variables with polynomial weights.

**Method A vs Method B (OS II explicit distinction):**

*Method A:* Treat spatial variables distributionally throughout. Simpler but needs E0'' (the stronger condition).

*Method B:* Use Euclidean invariance and Glaser-type geometry to prove the relevant functions are honest continuous/analytic functions of spatial variables. Works under the weaker E0'. More geometric and technically demanding.

### 16. Extraction of Wightman Distributions

Once continuation to C₊^k with polynomial bounds is established:

**Step 1:** The holomorphic function G(ζ) on C₊^k with polynomial growth is the Fourier-Laplace transform of a tempered distribution Ŵ supported in V̄₊^k:
```
G(ζ) = ∫ e^{iζ·p} Ŵ(p) dp,   supp(Ŵ) ⊂ V̄₊^k
```

**Step 2:** As Im(ζ) → 0, G has tempered distributional boundary values — the Wightman distributions W_n.

**Step 3:** Verify Wightman axioms:
- R0: From temperedness estimates
- R1: From E1 + continuation
- R2: From E2 → Hilbert space → GNS positivity
- R3: From E3 + edge-of-the-wedge theorem
- R4: From E4 + continuation
- R5: From support of Ŵ in V̄₊^k (automatic from semigroup construction)

---

## Part IV: R → E Direction

### 17. Construction of Schwinger Functions from Wightman Functions

**Step 1: Holomorphic extension.** The Wightman functions W_{n-1}(ξ₁,...,ξ_{n-1}), via the spectral condition and Fourier-Laplace representation, extend to holomorphic functions on the forward tube T_{n-1}.

**Step 2: Euclidean evaluation.** Ordered Euclidean configurations (τ₁ > τ₂ > ··· > τ_n) correspond to points in the forward tube. Define Schwinger functions by evaluation there.

**Step 3: Verification of E0–E4.** (See Part V for the non-trivial steps.)

### 18. The Bargmann-Hall-Wightman Theorem

Required for E3 (permutation symmetry) in R → E, and for Lorentz covariance in E → R.

**Statement:** A holomorphic function F on the forward tube T_{n-1}, covariant under SO⁺(1,d):
```
F(Λξ₁,...,Λξ_{n-1}) = F(ξ₁,...,ξ_{n-1})   for Λ ∈ SO⁺(1,d)
```
extends holomorphically to the permuted extended tube T''_{n-1}, with the extension SO⁺(1,d;C)-invariant and permutation-symmetric.

**Proof structure:**

*Step 1 (Complex Lorentz extension):* SO⁺(1,d;C) is path-connected (Bros-Epstein-Glaser path lemma) and acts holomorphically on T_{n-1}. The identity theorem extends Lorentz covariance to the complex Lorentz group.

*Step 2 (Extended tube = orbit):* By Jost's theorem, the SO⁺(1,d;C) orbit of T_{n-1} is the extended tube T'_{n-1}. T'_{n-1} contains all Jost points (real configurations with all differences spacelike).

*Step 3 (Permuted extended tube):* At Jost points, differences can be permuted while remaining spacelike. The edge-of-the-wedge theorem glues F across permutation boundaries.

**Bros-Epstein-Glaser path lemma:** Any complex Lorentz element is connected to the identity by a path staying in the tube.

- Case 1 (nilpotent): Straight line path, stays in tube by convexity of forward cone.
- Case 2 (semisimple): Eigenvalues e^{±α±iβ}, lightcone components g±(t) = e^{±αt}(q cos βt + p sin βt). Positivity from sinusoidal factor control.

**Translation invariance of BHW extension:** In difference variables, this is automatic (uniform shifts don't change differences). In cumulative-sum variables (as in the formalization), requires additional argument. The formalization uses Route 1: work natively in reduced difference coordinates.

---

## Part V: Complex Analysis Infrastructure

### 19. Edge-of-the-Wedge Theorem

**Statement (Bogoliubov 1957):** F₊ holomorphic on R^n + iΓ, F₋ on R^n − iΓ (Γ open convex cone), continuous boundary values agreeing on R^n, extend to a single holomorphic function on a neighborhood of R^n.

**Proof:** 1D base via Morera's theorem. Multi-D via iterated Cauchy integrals + Osgood's lemma.

**Uses:** Gluing across permutation boundaries (BHW), converting E3 to R3 (locality), extending Schwinger functions across time-ordering boundaries.

### 20. Osgood's Lemma

**Statement:** Separately holomorphic + continuous ⟹ jointly holomorphic.

**Proof:** Construct Fréchet derivative directly. Induction on dimension via C × E decomposition.

### 21. Tube Theorems

**Bochner tube theorem:** Holomorphic on R^n + iC extends to R^n + i·ch(C).

**Malgrange-Zerner:** Separate flat-tube analyticity in enough independent directions ⟹ analyticity on convex envelope. Key tool for converting 4-directional semigroup continuations to local multi-variable analyticity.

### 22. Semigroup-Group Bochner Representation

The semigroup T_t = e^{−tH} and spatial translations U_a = e^{iaP} combine:
```
⟨Ψ, T_t U_a Φ⟩ = ∫ e^{−tλ + ia·p} dμ_{Ψ,Φ}(λ,p)
```
with μ supported in {λ ≥ 0} × R^d. Bridges semigroup and Fourier-Laplace representation.

---

## Part VI: The Wightman Reconstruction Theorem

### 23. GNS Construction

Given Wightman functions {W_n} satisfying positivity:

1. Form space V of formal polynomials in test functions
2. Inner product: ⟨F,G⟩ = Σ W_{n+m}(F̄ ⊗ G)
3. Positivity: ⟨F,F⟩ ≥ 0
4. Null space argument: ⟨X,X⟩ = 0 ⟹ ⟨X,Y⟩ = 0 (quadratic positivity: expand ⟨X+λY, X+λY⟩ ≥ 0)
5. H = (V/ker⟨·,·⟩)^{completion}
6. Vacuum: Ω = [1], Fields: φ(f)[G] = [f⊗G]
7. Reproduce: ⟨Ω, φ(f₁)···φ(f_n)Ω⟩ = W_n(f₁⊗···⊗f_n)

**Uniqueness:** Map φ₁(f₁)···φ₁(f_n)Ω₁ ↦ φ₂(f₁)···φ₂(f_n)Ω₂ is isometric and intertwines fields.

---

## Part VII: Formalization Architecture

### 24. Module Map

| Module | Content | Sorrys | Axioms |
|--------|---------|--------|--------|
| Wightman/ | Axioms, GNS, Wick rotation bridge | 28 | 2 |
| SCV/ | Edge-of-wedge, tube domains, Fourier-Laplace | 2 | 4 |
| ComplexLieGroups/ | BHW, complex Lorentz, Jost points | 2 | 0 |
| vNA/ | Tomita-Takesaki, spectral theory, Stone | 40 | 0 |
| Bridge/ | Axiom-replacement wiring | 0 | 1 |
| **Total** | | **72** | **7** |

### 25. Critical Path Files and Their Paper Correspondence

| File | Paper Section | Content |
|------|--------------|---------|
| OSToWightmanSemigroup.lean | OS I §4, OS II Ch.V (semigroup) | Hilbert space, semigroup, holomorphic extension |
| OSToWightman.lean | OS II Thms 4.1–4.3 | Inductive continuation base step |
| OSToWightmanBoundaryValues.lean | OS II Ch.VI | Temperedness, boundary values, axiom transfer |
| SchwingerAxioms.lean | OS I §5 (R→E) | E0–E4 from Wightman functions |
| SchwingerTemperedness.lean | OS II Ch.VI (R→E) | Zero-diagonal temperedness |
| BHWExtension.lean | Streater-Wightman Ch.2 | Adjacent-swap BHW extension |
| BHWTranslation.lean | Route 1 | Translation invariance of BHW |
| ForwardTubeLorentz.lean | BHW infrastructure | Lorentz covariance on tube |
| GNSConstruction.lean | Wightman reconstruction | GNS from W_n (sorry-free) |
| TubeDomainExtension.lean | Bogoliubov 1957 | Multi-D edge-of-the-wedge (sorry-free) |
| SeparatelyAnalytic.lean | Osgood 1899 | Osgood's lemma (sorry-free) |

### 26. Root E→R Blocker: schwinger_continuation_base_step

**Location:** OSToWightman.lean

**Mathematical content:** Construct holomorphic G on flattened product tube such that OS.S k f = ∫ G(toDiffFlat(wickRotate(x))) · f(x) dx.

**For k=2 (immediate target):**
```
G(ζ) = ⟨Ψ₁(ξ_spatial), T(ζ⁰) Ψ₁(ξ_spatial)⟩_OS
```
One difference variable, one time continuation. Partially implemented.

**The shell mismatch:** Semigroup produces results on product shells χ(u)g(u+ξ); OS axioms use admissible shells χ(u)h(ξ). Center-descent infrastructure shows equal integrals. Remaining gap: proving semigroup evaluation factors through center descent.

**For general k (OS II eq. 5.3):**
```
G(ζ₁,...,ζ_{k−1}) = ⟨Ψ₁, T(ζ₁⁰) A₂ T(ζ₂⁰) ··· T(ζ_{k−1}⁰) Ψ_{k−1}⟩
```

### 27. The 7 Axioms

| # | Name | Mathematical Content | Type |
|---|------|---------------------|------|
| 1 | schwartz_nuclear_extension | Schwartz kernel theorem | Functional analysis |
| 2 | exists_continuousMultilinear_ofSeparatelyContinuous | Banach-Steinhaus multilinear | Functional analysis |
| 3 | semigroupGroup_bochner | Joint semigroup-group Bochner | Harmonic analysis |
| 4 | laplaceFourier_measure_unique | Laplace-Fourier uniqueness | Harmonic analysis |
| 5 | vladimirov_tillmann | Tube growth theorem | SCV |
| 6 | distributional_cluster_lifts_to_tube | Cluster lifting to tube | SCV |
| 7 | reduced_bargmann_hall_wightman_of_input | Reduced BHW theorem | Complex Lie groups |

---

## Appendix: Key Estimates Reference

| Estimate | Statement | Paper Reference |
|----------|-----------|----------------|
| OS form positivity | (f,f) ≥ 0 | OS I (4.3) |
| Contraction | ‖T_t‖ ≤ 1 | OS I (4.9) |
| Holomorphic semigroup | ⟨Ψ,T_τΦ⟩ analytic Re τ > 0 | OS I (4.10) |
| Seminorm equivalence | \|f₊\|'_m ~ \|f₊\|''_m on S(R̄₊) | OS I Lemma 8.1 |
| Extension with norm control | \|f₊\|_{p} ≤ γ\|f₊\|_{2p} | OS II Lemma 2.2 |
| Linear growth | \|S_n(f)\| ≤ σ_n\|f\|_{ns} | OS II (E0') |
| Analyticity radius | Polydisc ~ ξ⁰/\|ξ\| | OS II Lemma 5.1 |
| Domain growth | ∪_N C_k^{(N)} = C₊^k | OS II Corollary 5.3 |
| Fourier-Laplace | G(ζ) = ∫e^{iζ·p} Ŵ(p) dp | OS I Lemma 8.6 |
| Counterexample to 8.8 | F(x,y) = e^{−xy} | OS II §1 |

---

**Last updated:** 2026-03-28 17:00 UTC

---

## Part VIII: Formalization Progress Assessment and Gap Analysis

### 28. Overall Scale

The formalization comprises **142,800 lines** of Lean 4 code across 4 major modules with **71 sorrys** and **11 axioms** (7 OS-critical + 4 vNA-internal). This is an enormous formalization project.

### 29. What Is Fully Proved (Sorry-Free)

The following critical-path components are **completely proved**:

**OS semigroup infrastructure (4,049 lines):** `OSToWightmanSemigroup.lean` — the entire Hilbert space construction, self-adjoint contraction semigroup T_t = e^{−tH}, holomorphic extension to Re(τ) > 0, one-variable matrix element formulas, spectral/Laplace bridge. This corresponds to OS I §4 (eqs. 4.3–4.11) and the semigroup part of OS II Chapter V.

**Spatial momentum bridge (3,569 lines):** `OSToWightmanSpatialMomentum.lean` — one-point semigroup-group spectral bridge, spatial translation invariance on the full right half-plane.

**k=2 base step infrastructure (4,386 lines):** `OSToWightmanK2BaseStep.lean` — center/difference descent, product shell vs admissible shell identification, translation-invariant Schwartz classification.

**k=2 density infrastructure (3,458 lines):** `OSToWightmanK2Density.lean` — compact-support Schwartz density, Stone-Weierstrass core.

**k=2 VI.1 support infrastructure (5,634 lines):** `K2VI1/Support.lean` — the vast majority of the OS II §VI.1 regularization and orbit machinery for k=2.

**Edge-of-the-wedge theorem (2,997 lines):** `TubeDomainExtension.lean` — full multi-dimensional edge-of-the-wedge, a major complex analysis result.

**Osgood's lemma (1,403 lines):** `SeparatelyAnalytic.lean` — separately holomorphic + continuous ⟹ jointly holomorphic, with Cauchy integral parameter.

**Fourier-Laplace package (989 lines):** `LaplaceSchwartz.lean` — generic tempered boundary-value lemmas.

**Paley-Wiener (2,420 lines):** `PaleyWiener.lean` — sorry-free.

**Distributional uniqueness (2,377 lines):** `DistributionalUniqueness.lean` — tube uniqueness from zero boundary value.

**GNS construction (335 lines):** `GNSConstruction.lean` — Wightman reconstruction from W_n.

**BHW extension (315 lines):** `BHWExtension.lean` — honest distributional adjacent-swap lane.

**BHW reduced infrastructure (508 + 513 lines):** `BHWReduced.lean` + `BHWTranslationCore.lean` — Route 1 reduced coordinate infrastructure.

**Schwinger temperedness (2,280 lines):** `SchwingerTemperedness.lean` — zero-diagonal temperedness front, now sorry-free. Uses VT axiom for integrability.

**Total sorry-free critical-path code: ~34,000+ lines.** This represents an extraordinary amount of completed formalization.

### 30. The OS-Critical Sorry Surface (32 sorrys + 7 axioms)

Organized by proof-theoretic role:

#### E → R Direction (13 sorrys)

**Root blocker — OSToWightman.lean (2 sorrys):**
- `exists_acrOne_productTensor_witness` — Construct the ACR(1) holomorphic witness on the product tensor shell
- `acrOne_productTensor_witness_extends_zeroDiagonal` — The witness restricts to reproduce the Schwinger function

These encode the core of OS II Theorems 4.1–4.3: constructing the analytic continuation from the semigroup. The k=2 case is the immediate target.

**k=2 VI.1 frontier — K2VI1/Frontier.lean (4 sorrys):**
- `exists_fixed_strip_fixedTimeKernel_constBound_package_local` — Analytic control of fixed-time kernel on real positive-time section (OS II §VI.1 regularization output)
- `exists_fixed_strip_fixedTimeCenterDiff_headBlockInvariant_local` — Head-block translation invariance of induced CLM (E1 payoff for shell identification)
- Shell limit convergence — Descended-shell approximate-identity argument
- Final distributional assembly — Choose honest Euclidean kernel/witness pair and discharge reproduction

These are the remaining steps in the OS II §VI.1 regularization strategy for k=2.

**Boundary values — OSToWightmanBoundaryValues.lean (7 sorrys):**
- `full_analytic_continuation_flat_tempered_package` — The full tempered package on C₊^k (OS II Theorem 4.3 + Chapter VI)
- `bv_translation_invariance_transfer` — Translation invariance through BV
- `bv_lorentz_covariance_transfer` — Lorentz covariance through BV
- `bv_local_commutativity_transfer` — Locality through BV
- `bv_positive_definiteness_transfer` — Positivity through BV
- `bv_hermiticity_transfer` — Hermiticity through BV
- `bvt_cluster` — Cluster property transport

These are the downstream axiom-transfer chain: once the analytic continuation with tempered bounds exists, each Wightman axiom must be derived from the corresponding OS axiom through the continuation. Most are conceptually straightforward but technically involved.

#### R → E Direction (3 sorrys)

**SchwingerAxioms.lean (2 sorrys):**
- `schwingerExtension_os_term_eq_wightman_term` — The OS=W identification term
- Cluster property of Schwinger functions from Wightman cluster — blocked by `wickRotation_not_in_PET_null` (a.e. forward tube membership) + Fubini decomposition

**ForwardTubeLorentz.lean (1 sorry):**
- `wickRotation_not_in_PET_null` — Algebraic measure-zero step: Wick-rotated configurations that fail to be in the forward tube form a measure-zero set. The polynomial part is proved in separate infrastructure; the remaining gap is the Jost characterization.

#### BHW Infrastructure (1 sorry + 1 axiom)

**BHWTranslation.lean (1 sorry):**
- `isPreconnected_baseFiber` — Pre-existing old-route residual. NOT needed on the merged Route 1 path. This is about fiber connectivity of the PET in cumulative-sum variables.

**BHWReducedExtension.lean (1 axiom):**
- `reduced_bargmann_hall_wightman_of_input` — The reduced-coordinate BHW theorem. Cannot be derived from absolute BHW via lift-project because of a logical circularity (need translation invariance to define the projection, but proving translation invariance is exactly what requires BHW). Axiomatized natively. Future path: either port the BHW proof to reduced coordinates directly, or formalize the PET translation-descent machinery.

#### Complex Lie Groups (2 sorrys)

**PermutationFlowBlocker.lean (2 sorrys):**
- Permutation-flow blockers for the BHW permutation lane. These are about the geometric flow that connects adjacent permutations through the extended tube.

#### Standalone Infrastructure (4 sorrys)

**BochnerTubeTheorem.lean (2 sorrys):**
- `bochner_local_extension` — Local-to-global tube extension
- `bochner_tube_extension` — Full Bochner tube theorem

Not on the immediate critical path (the continuation uses the inductive (A_N)/(P_N) method, not the Bochner tube theorem directly), but load-bearing for some downstream arguments.

**Main.lean (1 sorry):**
- `wightman_uniqueness` — Uniqueness of Wightman QFT up to unitary equivalence

**GNSHilbertSpace.lean (1 sorry):**
- Vacuum uniqueness via Stone's theorem

### 31. The vNA Lane (40 sorrys, 4 axioms)

The von Neumann algebra module is a **separate development lane** not on the OS-critical path. It contains:
- Tomita-Takesaki modular theory (6 sorrys)
- Modular automorphism groups (7 sorrys)
- KMS condition (10 sorrys)
- Caratheodory extension / spectral measures (11 sorrys)
- Spectral powers / unitary groups (2 sorrys + 4 axioms)
- Stone's theorem (1 sorry, but needed for wightman_reconstruction)
- Predual theory (2 sorrys)

This lane matters for the separate GNS/operator reconstruction theorem (`wightman_reconstruction`), but NOT for the Wick-rotation critical path.

### 32. The 7 OS-Critical Axioms: Assessment

| Axiom | Difficulty to Close | Notes |
|-------|-------------------|-------|
| schwartz_nuclear_extension | Medium-Hard | Partially proved in gaussian-field library; gap is importing + deriving kernel theorem |
| exists_continuousMultilinear_ofSeparatelyContinuous | Medium | Proved in gaussian-field; gap is importing |
| semigroupGroup_bochner | Hard | Genuine harmonic analysis; joint semigroup-group Bochner on [0,∞) × R^d |
| laplaceFourier_measure_unique | Medium | Uniqueness clause for Bochner; standard but technical |
| vladimirov_tillmann | Hard | Deep SCV theorem (tube growth bounds) |
| distributional_cluster_lifts_to_tube | Medium-Hard | Poisson integral + Riemann-Lebesgue argument |
| reduced_bargmann_hall_wightman_of_input | Hard | Native reduced-coordinate BHW; requires porting complex Lie group connectedness |

Axioms 1–2 are the closest to closure (external library has the proofs, just needs import bridge).

---

## Part IX: Strategic Recommendations

### 33. Comparison: Formalization vs Paper Proof

| OS Paper Component | Formalization Status | Assessment |
|-------------------|---------------------|------------|
| Test function spaces (OS I §2) | Defined in WightmanAxioms.lean, SchwingerOS.lean | Solid |
| Wightman axioms (R0–R5) | WightmanAxioms.lean | Complete |
| OS axioms (E0–E4) | OsterwalderSchraderAxioms structure | Complete |
| OS Hilbert space (OS I §4) | OSToWightmanSemigroup.lean | **Sorry-free** |
| Contraction semigroup (OS I eqs 4.6–4.9) | OSToWightmanSemigroup.lean | **Sorry-free** |
| Holomorphic extension (OS I eq 4.10) | OSToWightmanSemigroup.lean | **Sorry-free** |
| One-variable continuation (OS I eq 4.11) | OSToWightmanSemigroup.lean | **Sorry-free** |
| Fourier-Laplace lemmas (OS I 8.5–8.7) | LaplaceSchwartz.lean, PaleyWiener.lean | **Sorry-free** |
| Inductive continuation (OS II Thms 4.1–4.3) | OSToWightman.lean | **2 sorrys (ROOT BLOCKER)** |
| Temperedness estimates (OS II Ch. VI) | K2VI1 files | **4 sorrys** |
| Boundary values & axiom transfer | OSToWightmanBoundaryValues.lean | **7 sorrys** |
| BHW theorem | BHWExtension + BHWReduced + axiom | 1 axiom + 1 residual sorry |
| Edge-of-the-wedge | TubeDomainExtension.lean | **Sorry-free** |
| Osgood's lemma | SeparatelyAnalytic.lean | **Sorry-free** |
| GNS construction | GNSConstruction.lean | **Sorry-free** |
| R→E: Schwinger from Wightman | SchwingerAxioms.lean | 2 sorrys |
| R→E: Temperedness | SchwingerTemperedness.lean | **Sorry-free** |

### 34. Priority Ordering for Gap Closure

Based on the dependency structure and mathematical difficulty:

**Priority 1: Close the k=2 E→R base step.**
- Files: K2VI1/Frontier.lean (4 sorrys)
- This is the most concentrated remaining work
- The vast support infrastructure (5,634 lines in K2VI1Support.lean) is already proved
- What remains is the final assembly: fixed-time kernel bounds, head-block translation invariance, shell limit convergence, distributional reproduction
- Mathematical content: OS II §VI.1 regularization for the two-point case
- Once k=2 is closed, it provides the template for general k

**Priority 2: Close the root continuation theorem.**
- Files: OSToWightman.lean (2 sorrys)
- `exists_acrOne_productTensor_witness` and its zero-diagonal extension
- Depends on the k=2 base step (Priority 1) as proof of concept
- For general k: requires the interleaved operator product from OS II eq. (5.3)

**Priority 3: Close the boundary-value transfer chain.**
- File: OSToWightmanBoundaryValues.lean (7 sorrys)
- Once Priorities 1–2 give the holomorphic continuation with tempered bounds, each transfer theorem (translation invariance, Lorentz covariance, locality, positivity, hermiticity, cluster) follows conceptually from the corresponding OS axiom
- Most are "straightforward but technical" — mechanical Lean work rather than deep mathematics
- Exception: `bvt_cluster` (cluster property) requires more substantial argument

**Priority 4: Close the R→E direction.**
- Files: SchwingerAxioms.lean (2 sorrys), ForwardTubeLorentz.lean (1 sorry)
- `wickRotation_not_in_PET_null` is close to proved (polynomial measure-zero part done, Jost characterization remaining)
- Cluster transport needs Fubini decomposition for Fin(n+m)-indexed integrals

**Priority 5: Close axiom bridge for axioms 1–2.**
- Files: WightmanAxioms.lean (2 axioms)
- `schwartz_nuclear_extension` and `exists_continuousMultilinear_ofSeparatelyContinuous` are proved in gaussian-field library
- Remaining work is import bridge + deriving kernel theorem
- This is more engineering than mathematics

**Priority 6: Address remaining axioms and standalone blockers.**
- reduced BHW axiom (hard: needs native reduced-coordinate proof or PET descent)
- Bochner tube theorem (2 sorrys, load-bearing but not immediate blocker)
- semigroupGroup_bochner and vladimirov_tillmann (hard, genuine mathematical axioms)
- wightman_uniqueness (1 sorry, mainly wiring)

**Deprioritized:** The vNA lane (40 sorrys) unless it unblocks something specific.

### 35. Specific Mathematical Recommendations

**For the k=2 VI.1 frontier (Priority 1):**
- The 4 remaining sorrys are all about the **final assembly** of the OS II §VI.1 construction
- The regularization machinery, orbit bounds, and support infrastructure are already proved (5,634 lines!)
- The first sorry (`exists_fixed_strip_fixedTimeKernel_constBound_package_local`) is about establishing analytic control of the fixed-time kernel — this requires polynomial bounds from the regularized OS form, channeled through the E0' linear growth condition
- The second sorry (head-block translation invariance) is the E1 payoff — it says the descended CLM doesn't depend on the center variable, which is exactly the OS parameter-packaging step
- Consult OS II Chapter VI.1 directly for the regularization-positivity-norm bound chain
- Validate intermediate lemma statements with Gemini before attempting proofs

**For the root continuation theorem (Priority 2):**
- The general k case requires the interleaved operator product T(ζ₁⁰) A₂ T(ζ₂⁰) ··· T(ζ_{k-1}⁰) from OS II eq. (5.3)
- This requires GNS field operators and their domains — link to the GNS construction
- The (A_N)/(P_N) alternation must be implemented as an inductive proof
- Validate that the inductive step matches OS II Lemma 5.2 and Corollary 5.3

**For the boundary-value transfer (Priority 3):**
- Most transfer theorems follow a common pattern: OS axiom → analytic continuation preserves property → boundary value inherits property
- Template the proof pattern once, then instantiate for each axiom
- The cluster transfer is the exception — it requires dominated convergence with explicit growth estimates

**For R→E (Priority 4):**
- `wickRotation_not_in_PET_null` needs the Jost characterization: Wick-rotated time-ordered configurations with all differences in the forward cone ⟺ a characterization in terms of time-ordering
- The polynomial measure-zero infrastructure is already proved — the gap is connecting it to the Jost geometry

### 36. Risks and Warnings

**Risk 1: The shell mismatch in E→R.** The product-shell vs admissible-shell identification is the most subtle remaining issue. The center-descent infrastructure is extensive, but the final factorization theorem — that the semigroup evaluation depends only on the descended parameter — must be proved without smuggling the identification as a hypothesis. Consult OS II Chapter V carefully: OS avoids this issue by working in difference variables from the start.

**Risk 2: Intermediate lemma validity.** When decomposing the 4 K2VI1 sorrys into sub-lemmas, each intermediate statement must be mathematically true. The OS II §VI.1 regularization involves several non-obvious steps (choosing mollifiers, Hilbert-space norm estimates, four-direction technique). Validate with Gemini before committing proof effort.

**Risk 3: General k generalization.** The k=2 case uses a single semigroup parameter. General k requires interleaved operators and a multi-step induction. The jump from k=2 to general k is not mechanical — it requires the full (A_N)/(P_N) alternation machinery from OS II Chapter V. Plan this architecture before attempting the proof.

**Risk 4: Axiom debt.** The 7 axioms represent genuine mathematical content that must eventually be proved. The two hardest are `semigroupGroup_bochner` (joint Bochner representation) and `vladimirov_tillmann` (tube growth theorem). These are deep results requiring substantial new infrastructure. Plan a separate workstream for axiom closure.

---

**Last updated:** 2026-03-28 17:30 UTC
