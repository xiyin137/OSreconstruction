/-
# Proof Ideas: h_consistency in BochnerTubeTheorem.lean

## Date: 2026-03-05

## Status: BLOCKED — `h_consistency` in `holomorphic_extension_from_local`

---

## 1. THE PROBLEM

In `holomorphic_extension_from_local` (BochnerTubeTheorem.lean), we define:
  f_ext(z) := G z hz z  (using Classical.choice of local extensions G z hz on V z hz)

To show f_ext is differentiable at z, we need:
  ∀ w ∈ V z hz, f_ext w = G z hz w

i.e., G w hw w = G z hz w  for w ∈ V z hz.

This is `h_consistency`:
```
∀ (z₁ z₂ : Fin m → ℂ) (hz₁ : z₁ ∈ D) (hz₂ : z₂ ∈ D) (w : Fin m → ℂ),
  w ∈ V z₁ hz₁ → w ∈ V z₂ hz₂ → G z₁ hz₁ w = G z₂ hz₂ w
```

---

## 2. WHY IT'S HARD

The hypothesis `hlocal` gives:
  G z₁ hz₁ = f on U ∩ V z₁ hz₁
  G z₂ hz₂ = f on U ∩ V z₂ hz₂

To conclude G z₁ hz₁ w = G z₂ hz₂ w for w ∈ V z₁ ∩ V z₂, we want to use the identity theorem:
  "G z₁ hz₁ - G z₂ hz₂ is holomorphic on V z₁ ∩ V z₂ and vanishes on U ∩ V z₁ ∩ V z₂ ≠ ∅."

BUT: U ∩ V z₁ ∩ V z₂ might be EMPTY even when V z₁ ∩ V z₂ ≠ ∅.
Example: if V z₁ and V z₂ are small neighborhoods near the boundary of D, far from U.

For the identity theorem to apply, we need SOME nonempty open set where G z₁ = G z₂.

---

## 3. MATHEMATICAL CORRECT APPROACH: MONODROMY THEOREM

The correct proof requires the "monodromy theorem":
  If D is simply connected (or even just contractible), analytic continuation along
  any two paths gives the same result. So any two local extensions that agree on U
  must agree everywhere on D (= on any overlap V z₁ ∩ V z₂).

For D = T(conv C) (tube over convex hull of open C):
  T(conv C) IS contractible: the deformation retract h_t(x+iy) = x + i(ty + (1-t)y₀)
  for any fixed y₀ ∈ conv C shows T(conv C) ≃ T({y₀}) = ℝ^m + iy₀ ≅ ℝ^m.

The monodromy theorem then implies h_consistency. But formalizing:
  (a) Contractibility of T(conv C) in Lean → ContractibleSpace
  (b) Contractible ⟹ simply connected (in Lean's π₁ = trivial)
  (c) Monodromy theorem: analytic continuation on simply connected domains is unique

...requires substantial homotopy theory NOT in Mathlib.

---

## 4. WHY THE STANDARD BOCHNER PROOF AVOIDS MONODROMY

The standard proof of Bochner's tube theorem (Hörmander 2.5.10) does NOT use
`holomorphic_extension_from_local` as a black box. Instead, it uses:

(A) FOURIER-LAPLACE APPROACH:
  For F holomorphic on T(C), F has Fourier-Laplace representation:
    F(z) = ∫_ξ f̂(ξ) e^{iz·ξ} dξ
  where the integral converges for Im(z) ∈ C (Paley-Wiener theorem).
  Extension to T(conv C) is by the same integral: it converges for Im(z) ∈ conv(C)
  because the growth condition on f̂ extends from C to conv(C) by convexity.
  This is the correct proof but requires Paley-Wiener theory (5 sorrys in PaleyWiener.lean).

(B) DIRECT CAUCHY INTEGRAL + CONSISTENCY VIA CAUCHY'S THEOREM:
  For polydiscs P₁, P₂ with centers c₁, c₂ ∈ T(C) and overlapping polydiscs,
  the two Cauchy integral representations G₁, G₂ of F agree on P₁ ∩ P₂ because:
  - Both contours can be deformed into each other without crossing T(C)'s boundary
  - This is the multi-variable Cauchy theorem (contour deformation)
  - Requires showing T(C) ∩ P₁ ∩ P₂ ≠ ∅ for overlapping polydiscs with centers in T(C)
  But: T(C) ∩ P₁ ∩ P₂ can be EMPTY (if c₁ ∉ P₂ and c₂ ∉ P₁).

---

## 5. PROPOSED FIX: ADD COMPATIBLE LOCAL EXTENSIONS HYPOTHESIS

The cleanest formal fix is to strengthen `holomorphic_extension_from_local` by adding:

```lean
(h_compat : ∀ (z₁ : Fin m → ℂ) (hz₁ : z₁ ∈ D) (z₂ : Fin m → ℂ) (hz₂ : z₂ ∈ D),
    ∀ w ∈ V z₁ hz₁ ∩ V z₂ hz₂, G z₁ hz₁ w = G z₂ hz₂ w)
```

Then h_consistency = h_compat, QED.

For `bochner_tube_extension`, provide h_compat by:
  - For polydiscs: G z hz = cauchyIntegralPolydisc F (center z) (radii z) restricted to
    Polydisc(center z, radii z).
  - Consistency on P₁ ∩ P₂: both Cauchy integrals agree on T(C) ∩ P₁ ∩ P₂ (if nonempty)
    by the Cauchy integral formula, hence by identity theorem on the connected P₁ ∩ P₂.
  - Still needs: T(C) ∩ P₁ ∩ P₂ ≠ ∅ or an alternative consistency argument.

---

## 6. ALTERNATIVE: AVOID holomorphic_extension_from_local ENTIRELY

For `bochner_tube_extension`, instead of generic local-to-global:

Step 1: Prove bochner_local_extension using Fourier-Laplace:
  G_z(w) = ∫_ξ f̂(ξ) e^{iw·ξ} dξ
  valid for Im(w) ∈ conv(C) ∩ small neighborhood of Im(z).
  [Requires paley_wiener_cone → blocked]

Step 2: f_ext(z) = G_z(z) is well-defined because G_z(z) = ∫_ξ f̂(ξ) e^{iz·ξ} dξ
  independent of choice of local chart z (the FL representation is global).
  h_consistency follows because ALL G_z come from the same formula, just on different
  domains of convergence.

This is the real proof and requires PaleyWiener.lean to be completed first.

---

## 7. STATUS SUMMARY

- `h_consistency` is NOT provable from current hypotheses of `holomorphic_extension_from_local`.
- The theorem as stated is CORRECT mathematically, but the proof requires monodromy theory.
- The correct proof for the Bochner case uses Fourier-Laplace (Paley-Wiener).
- Blocked by: SCV/PaleyWiener.lean (5 sorrys).
- Interim fix: Add h_compat hypothesis to holomorphic_extension_from_local (defers
  the consistency proof to the Bochner-specific case).
- Long-term fix: Complete PaleyWiener.lean and use FL representation throughout.

## 8. REFERENCE FILES

- BochnerTubeTheorem.lean: h_consistency at line 199-206
- SCV/PaleyWiener.lean: 5 sorrys blocking the correct proof
- SCV/LaplaceSchwartz.lean: 6 sorrys (FL transform theory)
- Proofideas/d1n2_blocker_analysis.lean: related analysis for PET connectivity
-/

section BochnerConsistency
end BochnerConsistency
