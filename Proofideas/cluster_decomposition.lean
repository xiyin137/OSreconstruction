/-
  Proof Ideas: E4 Cluster Decomposition
  (W_analytic_cluster_integral, bhw_pointwise_cluster_euclidean)

  Goal: Show that the constructed Schwinger functions satisfy the cluster property E4:
    lim_{|a|→∞} S_{n+m}(f ⊗ τ_a g) = S_n(f) · S_m(g)
  where the limit is taken as the spatial separation |a| grows.

  The Schwinger functions are defined as:
    S_n(f) = ∫ W_BHW(Wick(x)) · f(x) dx

  STRUCTURE OF THE PROOF:

  The proof has two layers:
  1. `bhw_pointwise_cluster_euclidean`: pointwise factorization at Euclidean points
  2. `W_analytic_cluster_integral`: integration against Schwartz functions (uses DCT)

  LAYER 1: POINTWISE CLUSTER AT EUCLIDEAN POINTS

  For Euclidean points z_n = (iτ₁,...,iτₙ) and z_m = (iσ₁,...,iσₘ) with
  strictly ordered times, the BHW extension satisfies:

    W_BHW(z₁,...,zₙ, z_{n+1}+a,...,z_{n+m}+a) → W_BHW(z₁,...,zₙ) · W_BHW(z_{n+1},...,z_{n+m})

  as the spatial vector a grows.

  MATHEMATICAL ARGUMENT (Standard: Streater-Wightman §3.4, Glimm-Jaffe §19):

  Step A: Write in difference variables (Jost representation).
    Define ξₖ = zₖ - z_{k+1} for k=1,...,n+m-1.
    Translation invariance means W_{n+m}(z) depends only on ξ₁,...,ξ_{n+m-1}.
    The "gap" variable is ξₙ = zₙ - z_{n+1}, which is shifted by -a.

  Step B: Fourier-Laplace representation.
    By the spectral condition, W_analytic has a Fourier-Laplace representation:
      W_analytic(ξ₁,...,ξ_{n+m-1}) = ∫ e^{ip₁·ξ₁} ... e^{ip_{n+m-1}·ξ_{n+m-1}} dμ(p)
    where μ is a measure supported in ∏ V̄₊ (product of closed forward cones).

    When ξ are in the tube (Im ξₖ ∈ V₊), the exponentials provide convergence.

  Step C: Factor the Laplace integral.
    The translation by a affects only the gap variable ξₙ → ξₙ - a.
    The integral becomes:
      ∫ [∏_{k≠n} e^{ipₖ·ξₖ}] · e^{ipₙ·(ξₙ-a)} dμ(p)
    = ∫ [∏_{k≠n} e^{ipₖ·ξₖ}] · e^{ipₙ·ξₙ} · e^{-ipₙ·a} dμ(p)

    The factor e^{-ipₙ·a} oscillates as |a| → ∞ (for pₙ ≠ 0 spatial components),
    and by the Riemann-Lebesgue lemma, only the pₙ=0 contribution survives.

    At pₙ=0, the integral factors:
      (∫ e^{ip₁·ξ₁}...e^{ip_{n-1}·ξ_{n-1}} dμ₁(p₁,...,p_{n-1})) ·
      (∫ e^{ip_{n+1}·ξ_{n+1}}...e^{ip_{n+m-1}·ξ_{n+m-1}} dμ₂(p_{n+1},...,p_{n+m-1}))
    = W_analytic(z₁,...,zₙ) · W_analytic(z_{n+1},...,z_{n+m})

  SIMPLIFICATION: AVOID DIRECT FOURIER-LAPLACE

  The above argument requires the full Fourier-Laplace representation and
  Riemann-Lebesgue lemma. An alternative approach that avoids this:

  **Key Idea**: Use the Wightman cluster axiom (R4) directly to prove the
  integral-level cluster property, without going through the pointwise version.

  The integral ∫ W_BHW(Wick(x)) · (f ⊗ τ_a g)(x) dx can be related to the
  distributional pairing W_{n+m}(f ⊗ τ_a g) via boundary values. If we can show:

    ∫ W_BHW(Wick(x)) · h(x) dx = W_{n+m}(h)

  for test functions h (this is the "boundary value identity" also needed for E2),
  then the cluster property follows directly from Wfn.cluster.

  STATUS: The "boundary value identity" constructSchwingerFunctions Wfn n f = Wfn.W n f
  is the key missing infrastructure. It's the same identity needed for E2
  (schwinger_os_term_eq_wightman_term). If proved, both E2 and E4 follow.

  ALTERNATIVE: DIRECT CLUSTER WITHOUT BOUNDARY VALUE IDENTITY

  Instead of proving the full BV identity, we can prove the cluster property
  directly at the Euclidean level. The key observation is:

  The BHW extension W_BHW(n+m) is holomorphic, and its boundary values satisfy
  the cluster property (by Wfn.cluster). By a Phragmén-Lindelöf type argument,
  the cluster property lifts from the boundary to the interior of the tube.

  More precisely: for fixed z_n, z_m Euclidean, define
    h(a) := W_BHW(z₁,...,zₙ,z_{n+1}+a,...,z_{n+m}+a) - W_BHW(z₁,...,zₙ)·W_BHW(z_{n+1},...,z_{n+m})

  This is an entire function in the spatial components of a (the time component a₀ = 0
  is fixed at 0, and the spatial components can be complexified).
  By polynomial growth bounds, |h(a)| ≤ C(1+|a|)^N.
  By the Wightman cluster property, ∫ h(a) · φ(a) da → 0 as we smear with
  translated test functions.
  By the identity principle + growth bounds, this forces h(a) → 0 pointwise.

  Actually this argument is not quite right — the distributional limit doesn't
  immediately give pointwise convergence. But with polynomial growth bounds
  and the distributional cluster, dominated convergence gives the integral cluster.

  LAYER 2: INTEGRAL CLUSTER (W_analytic_cluster_integral)

  Given the pointwise cluster at Euclidean points, integrate against Schwartz functions.

  Step 1: For Schwartz f, g, the integrand is dominated by the product of
          polynomial growth of W_BHW and Schwartz decay of f, g.
  Step 2: By dominated convergence (DCT), the integral limit is the pointwise limit.
  Step 3: The pointwise limit is the product, giving the cluster property.

  For Step 1, need: polynomial growth bound on W_BHW at Euclidean points.
  This follows from `polynomial_growth_forwardTube_full` (currently sorry).

  MOST DIRECT APPROACH: PROVE SCHWINGER = WIGHTMAN IDENTITY

  The most economical path is to prove:
    constructSchwingerFunctions Wfn n f = Wfn.W n f
  for all Schwartz f. Then both E2 and E4 follow immediately.

  This identity says: evaluating the BHW extension at Wick-rotated points and
  integrating against f equals the distributional Wightman pairing W_n(f).

  Proof sketch:
  1. W_BHW on the forward tube is a holomorphic extension of W_analytic (from spectral condition)
  2. W_analytic has boundary values = W_n (spectral condition axiom)
  3. At Wick-rotated points with strictly ordered times, W_BHW = W_analytic
     (they agree on the forward tube)
  4. The integral ∫ W_analytic(Wick(x)) · f(x) dx, as the imaginary parts → 0,
     converges to W_n(f) by the boundary value formula
  5. But the Wick-rotated points have FIXED imaginary parts (τ > 0), not approaching 0

  So actually, S_n(f) ≠ W_n(f) in general — they're different things!
  S_n is the Schwinger function (Euclidean), W_n is the Wightman function (Minkowski).

  The correct identity is: S_n and W_n are DIFFERENT objects related by analytic continuation.
  The cluster property for S_n must be proved directly from the analytic properties
  of the BHW extension, not by reducing to W_n.

  CONCLUSION: We need to prove the cluster property at the analytic/Euclidean level directly.
  The Wightman cluster axiom (R4) provides the tool: it gives cluster for the
  distributional W_n, which lifts to the holomorphic W_analytic on the forward tube,
  and then to the BHW extension at Euclidean points.

  REVISED PLAN:
  1. Prove `bhw_pointwise_cluster_euclidean` using:
     - Translation invariance of W_BHW (proved)
     - Polynomial growth bounds (from Fourier-Laplace)
     - Riemann-Lebesgue or direct spectral argument
  2. Prove `W_analytic_cluster_integral` using:
     - `bhw_pointwise_cluster_euclidean` for pointwise limit
     - Polynomial growth + Schwartz decay for domination
     - Dominated convergence theorem

  Both steps require polynomial growth bounds, which are in LaplaceSchwartz.lean (sorry).
  The Riemann-Lebesgue / spectral argument is new infrastructure.

  DEPENDENCIES:
  - `polynomial_growth_forwardTube_full` (WickRotation.lean) — sorry
  - Riemann-Lebesgue lemma for holomorphic functions on tubes
  - Translation invariance of BHW extension at Euclidean points (proved)

  STATUS: In progress. Added `Wfn.cluster` axiom to WightmanFunctions structure.
-/
