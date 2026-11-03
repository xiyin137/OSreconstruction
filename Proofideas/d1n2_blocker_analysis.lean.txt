/-
# Proof Ideas: d=1 Permutation Blocker Analysis

## Date: 2026-03-05

## Status: BLOCKED — both `blocker_isConnected_permSeedSet_nontrivial` and
##          `blocker_iterated_eow_hExtPerm_d1_nontrivial` in PermutationFlowBlocker.lean

---

## 1. PROVED: Real Jost witnesses are impossible for d=1

For d=1, n=2, adjacent swap σ = swap(0,1):
For any real config x : Fin 2 → Fin 2 → ℝ, it is IMPOSSIBLE to have both:
  realEmbed(x) ∈ ExtendedTube(1,2)  AND  realEmbed(swap·x) ∈ ExtendedTube(1,2)

Proof sketch:
- realEmbed(x) ∈ ET means ∃ Λ ∈ CLG(1), ∃ σ' ∈ S₂ : Λ·(σ'·realEmbed(x)) ∈ FT(1,2)
- For real x, Im(Λ·v) for v ∈ ℝ² is: sin(τ)·(sinh(s)·v₀ + cosh(s)·v₁, cosh(s)·v₀ + sinh(s)·v₁)
  where θ = s + iτ.
- FT condition requires Im of all cumulative differences in V⁺.
- For swap·realEmbed(x), the cumulative differences become the REVERSE of those for x.
- But Im(Λ·v) and Im(Λ·(-v)) = -Im(Λ·v) can't both be in V⁺ (sine factor doesn't change sign).
- Hence: if Im(Λ·d) ∈ V⁺, then Im(Λ·(-d)) = -Im(Λ·d) ∈ -V⁺, NOT in V⁺.

Consequence: JostWitnessGeneralSigma approach FAILS for d=1.

---

## 2. PROVED: permForwardOverlapSet(1, 2, swap) is nonempty

Explicit complex witness:
  w = fun k μ => if k = 0 then (if μ = 0 then Complex.I else 10) else (if μ = 0 then 1+3*I else 8)
  Λ = complexLorentzBoost(-S + iπ/2) for some S

The key: d := w₁ - w₀ = (1+2i, -2) has spacelike real part: α_t² - α_x² = 1 - 4 = -3 < 0.
For θ = -S + iπ/2: cosh(θ) = -i·sinh(S), sinh(θ) = -i·cosh(S).
So Im-time(Λ·v) = cosh(S)·α_x - sinh(S)·α_t and Im-space(Λ·v) = sinh(S)·α_x - cosh(S)·α_t.
Then (Im-time)² - (Im-space)² = α_x² - α_t² = 4 - 1 = 3 > 0 strictly.
So Im(Λ·d) has negative time-component while being in -V⁺ (the backwards light cone).

IMPORTANT: The spacelike real part d_x² - d_t² > 0 is the key property needed.
One needs: the REAL PART of the difference (w₁ - w₀) has d_x² > d_t².

---

## 3. ANALYSIS: Both blockers are deeply entangled

blocker_iterated_eow_hExtPerm_d1_nontrivial requires:

Step A: Identify an open subset W ⊆ D = ET ∩ {z | σ·z ∈ ET} where extendF(σ·z) = extendF(z).
Step B: Use identity theorem (via blocker_isConnected_permSeedSet_nontrivial) to propagate to all of D.

For Step A, natural candidate: W = permForwardOverlapSet(1, 2, σ) ∩ ET.
On this set, w ∈ FT and ∃ Λ : Λ·(σ·w) ∈ FT. Then:
  extendF(σ·w) = F(Λ⁻¹·(σ·w)) [by CLG invariance + definition]
              = F(σ·w)          [if Λ = 1, which we can't assume]
But this gives F(Λ⁻¹·(σ·w)) which is not clearly equal to F(w) without more work.

For Step A, the correct approach is:
  extendF(σ·w) = extendF(w) for w ∈ permForwardOverlapSet
should follow from:
  1. On a CLG-path connecting w₀ ∈ FT to some w̃ ∈ FT with σ·w₀ ∈ FT (overlap set),
     the function z ↦ extendF(σ·z) - extendF(z) is holomorphic on D and vanishes on
     some open set (by the CLG-invariance of extendF).
  2. Identity theorem on D then gives extendF(σ·z) = extendF(z) on all of D.

But this is essentially the same as the main blocker! Circularity.

---

## 4. INFRASTRUCTURE GAP: What's missing

For d ≥ 2: JostWitnessGeneralSigma provides real Jost witnesses (using the j=2 spatial
Wick rotation). These give a BASE POINT w_jost where extendF(σ·w) = extendF(w) via:
  - F(w_jost) = F(σ·w_jost) by hF_local (since w_jost ∈ JostSet)
  - extendF = F on FT (by BHW property 2)
  - Hence extendF(σ·w_jost) = extendF(w_jost)

For d = 1: No real Jost witnesses exist. Need a DIFFERENT initial agreement point.

The crucial missing piece: Find some explicit z₀ ∈ permForwardOverlapSet(1,2,σ) where
extendF(σ·z₀) = extendF(z₀) can be proved FROM THE HYPOTHESES (hF_holo, hF_lorentz,
hF_bv, hF_local).

The `hF_local` hypothesis gives: for REAL spacelike points x,
  F(fun k μ => x(swap(i,j)(k))(μ)) = F(fun k μ => x k μ).

But the overlap set permForwardOverlapSet uses COMPLEX points! And for complex w in the
overlap set, the corresponding "real Jost point" argument doesn't apply.

---

## 5. POTENTIAL APPROACH: Use hF_bv (boundary continuity) + complex EOW

The hypothesis hF_bv says: F is continuous at real boundary points (ContinuousWithinAt on FT).

For a real spacelike configuration x (∑ μ, η(μ) * (x(i+1)(μ) - x(i)(μ))² > 0), we have
by hF_local: F(σ·realEmbed(x)) = F(realEmbed(x)).

By hF_bv: F is continuous at real boundary points, so extendF approaches F at these points.

If we could show extendF(σ·realEmbed(x)) = extendF(realEmbed(x)) for real spacelike x,
then by the identity theorem (on the connected D), the equality extends to all of D.

But extendF(realEmbed(x)) = F(realEmbed(x)) requires x to be in ForwardTube, while real
spacelike configurations are on the BOUNDARY of FT (Im = 0).

---

## 6. CONCLUSION: Both blockers remain open

Primary obstacle: No known way to convert the hF_local hypothesis (about real boundary points)
into extendF equality at complex points without:
  (a) Real Jost witnesses in the permForwardOverlapSet [impossible for d=1]
  (b) A complex EOW argument [requires the full BHW chain for d=1]

The d=1 case may require a fundamentally different strategy:
  Option A: Prove it via the `hF_bv` continuity at real spacelike boundary points,
            combined with a distributional identity theorem (not just complex analytic).
  Option B: Prove connectivity of permSeedSet(1,n,σ) first, then use this to get
            a connected overlap domain, and use locality on the boundary.
  Option C: Reduce to d=2 case somehow (if a formal reduction exists).

None of these are currently implemented.

## 7. REFERENCE

- Proofideas file: /Users/xiyin/OSReconstruction/Proofideas/d1n2_blocker_analysis.lean
- Numerical evidence: /private/tmp/permseed_d1n2_refined.py
  - All 80 trials SUPPORTED (n_components=1, largest_frac=1.0)
  - d=1, n=2, various eps values, k in {5,10,20,40,80}
- isConnected_PET_inter_translate: /tmp/isConnected_PET_inter_translate_d1n2.py
  - All 9 shift values returned 1 connected component
-/

-- Placeholder structure to make this a valid Lean file
section d1Blockers
end d1Blockers
