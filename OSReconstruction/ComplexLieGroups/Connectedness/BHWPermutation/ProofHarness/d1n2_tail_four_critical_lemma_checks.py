#!/usr/bin/env python3
"""
Numerical stress tests for the 4 critical deferred d=1,n=2 lemmas in Tail.lean:

1) blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred
2) blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred
3) blocker_d1N2InvariantBridgePreconnected_fromSource_deferred
4) blocker_d1N2InvariantBridgeCorrection_fromSource_deferred

Important:
- These are heuristic falsification checks, not formal proofs.
- Each test works in finite-dimensional ansatz spaces and finite random samples.
"""

from __future__ import annotations

import argparse
import cmath
import math
import random
from dataclasses import dataclass
from typing import List, Sequence, Tuple

import numpy as np


Complex4 = Tuple[complex, complex, complex, complex]


def invariants_from_uv(u0: complex, v0: complex, u1: complex, v1: complex) -> Complex4:
    q0 = -(u0 * v0)
    q1 = -(u1 * v1)
    p = -0.5 * (u0 * v1 + u1 * v0)
    s = u0 * v1 - u1 * v0
    return (q0, q1, p, s)


def quadric_residual(inv: Complex4) -> complex:
    q0, q1, p, s = inv
    return s**2 - 4 * (p**2 - q0 * q1)


def in_ft_uv(u0: complex, v0: complex, u1: complex, v1: complex, eps: float = 0.0) -> bool:
    return (
        u0.imag > eps
        and v0.imag > eps
        and (u1 - u0).imag > eps
        and (v1 - v0).imag > eps
    )


def sample_ft_uv(rng: random.Random) -> Complex4:
    b0 = rng.uniform(0.2, 3.0)
    d0 = rng.uniform(0.2, 3.0)
    db = rng.uniform(0.2, 3.0)
    dd = rng.uniform(0.2, 3.0)
    u0 = complex(rng.uniform(-3.0, 3.0), b0)
    v0 = complex(rng.uniform(-3.0, 3.0), d0)
    u1 = u0 + complex(rng.uniform(-3.0, 3.0), db)
    v1 = v0 + complex(rng.uniform(-3.0, 3.0), dd)
    return (u0, v0, u1, v1)


def sample_real_ft_uv(rng: random.Random) -> Complex4:
    # Purely imaginary light-cone coordinates with FT positivity.
    u0_im = rng.uniform(0.2, 3.0)
    v0_im = rng.uniform(0.2, 3.0)
    du_im = rng.uniform(0.2, 3.0)
    dv_im = rng.uniform(0.2, 3.0)
    u0 = complex(0.0, u0_im)
    v0 = complex(0.0, v0_im)
    u1 = complex(0.0, u0_im + du_im)
    v1 = complex(0.0, v0_im + dv_im)
    return (u0, v0, u1, v1)


def sample_phase_locked_real_invariant_ft_uv(rng: random.Random) -> Complex4:
    # Construct z in FT with invariants exactly real by phase-locked light-cone data:
    # u_k = r_k e^{iθ}, v_k = -t_k e^{-iθ} with 0 < θ < π, r1 > r0, t1 > t0.
    theta = rng.uniform(0.12, math.pi - 0.12)
    r0 = rng.uniform(0.25, 3.5)
    r1 = r0 + rng.uniform(0.2, 3.5)
    t0 = rng.uniform(0.25, 3.5)
    t1 = t0 + rng.uniform(0.2, 3.5)
    u0 = r0 * cmath.exp(1j * theta)
    u1 = r1 * cmath.exp(1j * theta)
    v0 = -t0 * cmath.exp(-1j * theta)
    v1 = -t1 * cmath.exp(-1j * theta)
    return (u0, v0, u1, v1)


def swap_then_lorentz_uv(
    u0: complex, v0: complex, u1: complex, v1: complex, lam: complex
) -> Complex4:
    # swap first, then complex boost: (u,v) -> (lam*u, lam^-1*v)
    inv_lam = 1.0 / lam
    y0u, y0v = lam * u1, inv_lam * v1
    y1u, y1v = lam * u0, inv_lam * v0
    return (y0u, y0v, y1u, y1v)


def random_nonzero_complex_scale(rng: random.Random) -> complex:
    r = rng.uniform(0.2, 4.0)
    th = rng.uniform(-math.pi, math.pi)
    return cmath.rect(r, th)


def lam_candidates(rng: random.Random, random_count: int) -> List[complex]:
    out: List[complex] = []
    fixed_r = [0.35, 0.6, 1.0, 1.7, 2.8]
    fixed_th = [-2.6, -2.1, -1.6, -1.1, -0.6, 0.6, 1.1, 1.6, 2.1, 2.6]
    for r in fixed_r:
        for th in fixed_th:
            out.append(cmath.rect(r, th))
    for _ in range(random_count):
        out.append(random_nonzero_complex_scale(rng))
    return out


def random_complex_with_pos_imag(
    rng: random.Random, re_lo: float = -4.0, re_hi: float = 4.0, im_lo: float = 0.15, im_hi: float = 4.0
) -> complex:
    return complex(rng.uniform(re_lo, re_hi), rng.uniform(im_lo, im_hi))


def close_inv(a: Complex4, b: Complex4, tol: float = 1e-7) -> bool:
    return max(abs(a[i] - b[i]) for i in range(4)) <= tol


def sample_forwardizable_invariant(
    rng: random.Random,
    lam_trials: int,
    eps: float,
    real_only: bool = False,
) -> Complex4 | None:
    z = sample_real_ft_uv(rng) if real_only else sample_ft_uv(rng)
    u0, v0, u1, v1 = z
    if not in_ft_uv(u0, v0, u1, v1, eps):
        return None
    inv = invariants_from_uv(u0, v0, u1, v1)
    q0, q1, p, s = inv
    if abs(q0) <= eps or abs(q1) <= eps:
        return None
    if real_only and max(abs(q0.imag), abs(q1.imag), abs(p.imag), abs(s.imag)) > 1e-8:
        return None

    for _ in range(lam_trials):
        lam = random_nonzero_complex_scale(rng)
        y = swap_then_lorentz_uv(u0, v0, u1, v1, lam)
        if not in_ft_uv(*y, eps):
            continue
        inv_y = invariants_from_uv(*y)
        target = (q1, q0, p, -s)
        if close_inv(inv_y, target):
            return inv
    return None


def orig_witness_cond(q0: complex, p: complex, s: complex, v0: complex, eps: float) -> bool:
    if abs(q0) <= eps or abs(v0) <= eps:
        return False
    return (
        (v0.imag > eps)
        and (((-q0) / v0).imag > eps)
        and (((q0 - p - s / 2) / v0).imag > eps)
        and ((((p - s / 2 - q0) * v0 / q0).imag) > eps)
    )


def swap_witness_cond(q1: complex, p: complex, s: complex, w0: complex, eps: float) -> bool:
    if abs(q1) <= eps or abs(w0) <= eps:
        return False
    return (
        (w0.imag > eps)
        and (((-q1) / w0).imag > eps)
        and (((q1 - p + s / 2) / w0).imag > eps)
        and ((((p + s / 2 - q1) * w0 / q1).imag) > eps)
    )


def is_real_spacelike_correction_tuple(inv: Complex4, eps: float) -> bool:
    q0, q1, p, s = inv
    if abs(quadric_residual(inv)) > 1e-8:
        return False
    if max(abs(q0.imag), abs(q1.imag), abs(p.imag), abs(s.imag)) > 1e-8:
        return False
    return (q0.real + q1.real - 2.0 * p.real) > eps


def sample_real_spacelike_invariant_from_z_family(
    rng: random.Random, eps: float
) -> Complex4 | None:
    # Real FT light-cone coordinates directly produce real invariant tuples.
    z = sample_real_ft_uv(rng)
    if not in_ft_uv(*z, eps):
        return None
    inv = invariants_from_uv(*z)
    if is_real_spacelike_correction_tuple(inv, eps):
        return inv
    return None


def sample_real_spacelike_invariant_from_phase_locked_z_family(
    rng: random.Random, eps: float
) -> Complex4 | None:
    # A second explicit z-family with complex phases but exactly real invariants.
    z = sample_phase_locked_real_invariant_ft_uv(rng)
    if not in_ft_uv(*z, eps):
        return None
    inv = invariants_from_uv(*z)
    if is_real_spacelike_correction_tuple(inv, eps):
        return inv
    return None


def direct_real_correction_hit_count_from_z_family(
    rng: random.Random, eps: float, attempts: int
) -> int:
    hits = 0
    for _ in range(attempts):
        if rng.random() < 0.5:
            inv = sample_real_spacelike_invariant_from_z_family(rng, eps)
        else:
            inv = sample_real_spacelike_invariant_from_phase_locked_z_family(rng, eps)
        if inv is not None:
            hits += 1
    return hits


def sample_real_spacelike_invariants(rng: random.Random) -> Complex4:
    while True:
        t0 = rng.uniform(-3.0, 3.0)
        x0 = rng.uniform(-3.0, 3.0)
        dt = rng.uniform(-3.0, 3.0)
        dx = rng.uniform(-3.0, 3.0)
        if dx * dx - dt * dt <= 0.25:
            continue
        t1 = t0 + dt
        x1 = x0 + dx
        u0, v0 = t0 + x0, t0 - x0
        u1, v1 = t1 + x1, t1 - x1
        q0, q1, p, s = invariants_from_uv(complex(u0), complex(v0), complex(u1), complex(v1))
        return (q0, q1, p, s)


def collect_samples(
    sampler,
    n: int,
    max_attempts: int,
) -> List[Complex4]:
    out: List[Complex4] = []
    attempts = 0
    while len(out) < n and attempts < max_attempts:
        attempts += 1
        item = sampler()
        if item is not None:
            out.append(item)
    return out


def monomial_exponents(max_degree: int) -> List[Tuple[int, int, int, int]]:
    out: List[Tuple[int, int, int, int]] = []
    for a in range(max_degree + 1):
        for b in range(max_degree + 1 - a):
            for c in range(max_degree + 1 - a - b):
                for d in range(max_degree + 1 - a - b - c):
                    out.append((a, b, c, d))
    return out


@dataclass
class AntiBasisTerm:
    exp: Tuple[int, int, int, int]

    def eval(self, q0: complex, q1: complex, p: complex, s: complex) -> complex:
        a, b, c, d = self.exp
        lhs = (q0**a) * (q1**b) * (p**c) * (s**d)
        rhs = (q1**a) * (q0**b) * (p**c) * ((-s) ** d)
        return lhs - rhs


def build_antisym_basis(max_degree: int) -> List[AntiBasisTerm]:
    basis: List[AntiBasisTerm] = []
    probe = (
        complex(1.1, 0.2),
        complex(-0.7, 0.6),
        complex(0.4, -0.8),
        complex(0.9, 0.5),
    )
    for exp in monomial_exponents(max_degree):
        term = AntiBasisTerm(exp)
        if abs(term.eval(*probe)) > 1e-12:
            basis.append(term)
    return basis


def build_constraint_matrix(
    basis: Sequence[AntiBasisTerm], samples: Sequence[Complex4]
) -> np.ndarray:
    mat = np.zeros((len(samples), len(basis)), dtype=np.complex128)
    for i, (q0, q1, p, s) in enumerate(samples):
        for j, term in enumerate(basis):
            mat[i, j] = term.eval(q0, q1, p, s)
    return mat


def nullspace_svd(mat: np.ndarray, tol: float) -> np.ndarray:
    if mat.shape[0] == 0:
        # No constraints: full space is the nullspace.
        return np.eye(mat.shape[1], dtype=np.complex128)
    _u, sing, vh = np.linalg.svd(mat, full_matrices=True)
    rank = int(np.sum(sing > tol))
    return vh[rank:].conj().T


def evaluate_g(coeff: np.ndarray, basis: Sequence[AntiBasisTerm], inv: Complex4) -> complex:
    q0, q1, p, s = inv
    vals = np.array([term.eval(q0, q1, p, s) for term in basis], dtype=np.complex128)
    return complex(np.dot(vals, coeff))


def candidate_coeffs(
    ns: np.ndarray,
    rng_np: np.random.Generator,
    random_combos: int,
) -> List[np.ndarray]:
    out: List[np.ndarray] = []
    if ns.shape[1] == 0:
        return out
    for j in range(min(3, ns.shape[1])):
        c = ns[:, j]
        nrm = np.linalg.norm(c)
        if nrm > 0:
            out.append(c / nrm)
    for _ in range(random_combos):
        combo = rng_np.normal(size=ns.shape[1]) + 1j * rng_np.normal(size=ns.shape[1])
        c = ns @ combo
        nrm = np.linalg.norm(c)
        if nrm > 0:
            out.append(c / nrm)
    return out


def worst_value_over_samples(
    coeffs: Sequence[np.ndarray],
    basis: Sequence[AntiBasisTerm],
    samples: Sequence[Complex4],
) -> float:
    worst = 0.0
    for c in coeffs:
        for inv in samples:
            worst = max(worst, abs(evaluate_g(c, basis, inv)))
    return worst


def wirtinger_dbar_residual(
    coeff: np.ndarray,
    basis: Sequence[AntiBasisTerm],
    inv: Complex4,
    var_idx: int,
    h: float,
) -> float:
    arr = [inv[0], inv[1], inv[2], inv[3]]

    def eval_at(z: complex) -> complex:
        old = arr[var_idx]
        arr[var_idx] = z
        val = evaluate_g(coeff, basis, (arr[0], arr[1], arr[2], arr[3]))
        arr[var_idx] = old
        return val

    z0 = arr[var_idx]
    fxp = eval_at(z0 + h)
    fxm = eval_at(z0 - h)
    fyp = eval_at(z0 + 1j * h)
    fym = eval_at(z0 - 1j * h)
    dfdx = (fxp - fxm) / (2.0 * h)
    dfdy = (fyp - fym) / (2.0 * h)
    dbar = 0.5 * (dfdx + 1j * dfdy)
    return abs(dbar)


class UnionFind:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> None:
        ra = self.find(a)
        rb = self.find(b)
        if ra == rb:
            return
        if self.size[ra] < self.size[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        self.size[ra] += self.size[rb]

    def component_sizes(self) -> List[int]:
        roots = {}
        for i in range(len(self.parent)):
            r = self.find(i)
            roots[r] = roots.get(r, 0) + 1
        return sorted(roots.values(), reverse=True)


def connectivity_graph_components(samples: Sequence[Complex4], knn_k: int) -> Tuple[int, List[int]]:
    n = len(samples)
    if n == 0:
        return (0, [])
    pts = np.zeros((n, 8), dtype=np.float64)
    for i, (q0, q1, p, s) in enumerate(samples):
        pts[i, :] = [
            q0.real, q0.imag, q1.real, q1.imag, p.real, p.imag, s.real, s.imag
        ]
    # Pairwise distances
    dif = pts[:, None, :] - pts[None, :, :]
    dist = np.linalg.norm(dif, axis=2)
    uf = UnionFind(n)
    k = max(1, min(knn_k, n - 1))
    for i in range(n):
        nbrs = np.argsort(dist[i])[1 : k + 1]
        for j in nbrs:
            uf.union(i, int(j))
    sizes = uf.component_sizes()
    return (len(sizes), sizes)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260304)
    parser.add_argument("--degree", type=int, default=6)
    parser.add_argument("--svd-tol", type=float, default=1e-10)
    parser.add_argument("--eps", type=float, default=1e-10)
    parser.add_argument("--lam-trials", type=int, default=140)
    parser.add_argument("--source-real-spacelike-samples", type=int, default=2500)
    parser.add_argument("--source-real-spacelike-z-samples", type=int, default=1500)
    parser.add_argument("--real-correction-samples", type=int, default=1400)
    parser.add_argument("--complex-domain-samples", type=int, default=1800)
    parser.add_argument("--random-null-combos", type=int, default=20)
    parser.add_argument("--knn-k", type=int, default=10)
    parser.add_argument("--fd-step", type=float, default=1e-6)
    parser.add_argument("--fd-samples", type=int, default=180)
    parser.add_argument("--direct-real-correction-z-search-trials", type=int, default=30000)
    parser.add_argument("--report-threshold", type=float, default=1e-6)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    rng_np = np.random.default_rng(args.seed)

    basis = build_antisym_basis(args.degree)
    print("=== Setup ===")
    print(f"seed={args.seed}")
    print(f"degree={args.degree}")
    print(f"antisym_basis_size={len(basis)}")

    # Local-comm source constraints: sampled real spacelike tuples.
    source_real_spacelike_intrinsic = [
        sample_real_spacelike_invariants(rng) for _ in range(args.source_real_spacelike_samples)
    ]
    source_real_spacelike_from_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_phase_locked_z_family(rng, args.eps),
        n=args.source_real_spacelike_z_samples,
        max_attempts=30 * args.source_real_spacelike_z_samples,
    )
    source_real_spacelike = source_real_spacelike_intrinsic + source_real_spacelike_from_z
    amat_source = build_constraint_matrix(basis, source_real_spacelike)
    ns_source = nullspace_svd(amat_source, tol=args.svd_tol)
    coeffs_source = candidate_coeffs(ns_source, rng_np, args.random_null_combos)

    print("\n=== Source Constraint Ansatz Space ===")
    print(f"source_real_spacelike_intrinsic_samples={len(source_real_spacelike_intrinsic)}")
    print(f"source_real_spacelike_from_z_samples={len(source_real_spacelike_from_z)}")
    print(f"source_real_spacelike_total_samples={len(source_real_spacelike)}")
    print(f"source_constraint_nullspace_dim={ns_source.shape[1]}")

    # Real correction-anchor tuples: quadric + real slice + spacelike inequality.
    real_correction_from_real_ft_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_z_family(rng, args.eps),
        n=args.real_correction_samples,
        max_attempts=20 * args.real_correction_samples,
    )
    real_correction_from_phase_locked_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_phase_locked_z_family(rng, args.eps),
        n=args.real_correction_samples,
        max_attempts=30 * args.real_correction_samples,
    )
    real_correction_intrinsic = [
        sample_real_spacelike_invariants(rng) for _ in range(args.real_correction_samples)
    ]
    real_correction = (
        real_correction_from_real_ft_z
        + real_correction_from_phase_locked_z
        + real_correction_intrinsic
    )

    # Complex witnessed tuples in D.
    complex_domain = collect_samples(
        lambda: sample_forwardizable_invariant(
            rng, args.lam_trials, args.eps, real_only=False
        ),
        n=args.complex_domain_samples,
        max_attempts=60 * args.complex_domain_samples,
    )

    print("\n=== Sampled Domains ===")
    print(f"real_correction_from_real_ft_z_samples={len(real_correction_from_real_ft_z)}")
    print(f"real_correction_from_phase_locked_z_samples={len(real_correction_from_phase_locked_z)}")
    print(f"real_correction_intrinsic_samples={len(real_correction_intrinsic)}")
    print(f"real_correction_total_samples={len(real_correction)}")
    print(f"complex_domain_samples_collected={len(complex_domain)}")
    print(
        "complex_domain_construction="
        + "z_in_FT + explicit swap_then_lorentz(z,lam) witness in FT"
    )
    print(
        "direct_real_correction_hits_from_z_family="
        + f"{direct_real_correction_hit_count_from_z_family(rng, args.eps, args.direct_real_correction_z_search_trials)}"
        + f"/{args.direct_real_correction_z_search_trials}"
    )
    if not real_correction:
        print(
            "warning=NO_REAL_CORRECTION_SAMPLES_FOUND "
            "(quadric+real-slice+spacelike samples not found; check sampler settings)"
        )
    if complex_domain:
        max_quadric = max(abs(quadric_residual(inv)) for inv in complex_domain)
        print(f"max_quadric_residual_complex_domain={max_quadric:.3e}")

    # Test 4: BridgeCorrection_fromSource (heuristic falsification).
    # If source-constrained antisymmetric ansatz can be nonzero on correction-anchor points,
    # that's evidence against the bridge-correction claim in this ansatz.
    worst_corr = worst_value_over_samples(coeffs_source, basis, real_correction)
    print("\n=== Test 4: BridgeCorrection_fromSource (Heuristic) ===")
    print(f"worst_|g|_on_real_correction_domain={worst_corr:.6e}")
    print(f"report_threshold={args.report_threshold:.1e}")
    if not real_correction:
        print("status=INCONCLUSIVE_NO_REAL_CORRECTION_SAMPLES")
    else:
        print(
            "status="
            + (
                "NO_NUMERIC_FALSIFIER_FOUND"
                if worst_corr <= args.report_threshold
                else "POTENTIAL_FALSIFIER_FOUND"
            )
        )

    # Test 1: Core theorem (analyticity+connectedness+correction -> g=0 on D),
    # using correction-sampled constraints (real quadric/slice/spacelike tuples).
    amat_corr = build_constraint_matrix(basis, real_correction)
    ns_corr = nullspace_svd(amat_corr, tol=args.svd_tol)
    coeffs_corr = candidate_coeffs(ns_corr, rng_np, args.random_null_combos)
    worst_core = worst_value_over_samples(coeffs_corr, basis, complex_domain)
    print("\n=== Test 1: Invariant Core Theorem (Heuristic) ===")
    print(f"correction_constraint_nullspace_dim={ns_corr.shape[1]}")
    print(f"worst_|g|_on_complex_witnessed_domain={worst_core:.6e}")
    print(f"report_threshold={args.report_threshold:.1e}")
    if not real_correction:
        print("status=INCONCLUSIVE_EMPTY_CORRECTION_ANCHOR_SET")
        print("note=CORE_TEST_USED_EMPTY_CORRECTION_CONSTRAINT_SET")
    else:
        print(
            "status="
            + (
                "NO_NUMERIC_FALSIFIER_FOUND"
                if worst_core <= args.report_threshold
                else "POTENTIAL_FALSIFIER_FOUND"
            )
        )

    # Test 2: BridgeAnalyticity_fromSource (pointwise differentiability surrogate).
    # Evaluate anti-holomorphic finite-difference residual on sampled complex witnessed points.
    fd_points = complex_domain[: min(len(complex_domain), args.fd_samples)]
    worst_dbar = 0.0
    for coeff in coeffs_source:
        for inv in fd_points:
            for var_idx in range(4):
                worst_dbar = max(
                    worst_dbar,
                    wirtinger_dbar_residual(coeff, basis, inv, var_idx, args.fd_step),
                )
    print("\n=== Test 2: BridgeAnalyticity_fromSource (Numerical Surrogate) ===")
    print(f"fd_points_used={len(fd_points)}")
    print(f"fd_step={args.fd_step:.1e}")
    print(f"max_wirtinger_dbar_residual={worst_dbar:.6e}")
    if not coeffs_source:
        print("note=NO_NONZERO_SOURCE_CONSTRAINED_ANTISYMMETRIC_MODE_IN_ANSATZ")

    # Test 3: BridgePreconnected_fromSource (connectivity surrogate).
    components, sizes = connectivity_graph_components(complex_domain, args.knn_k)
    largest = sizes[0] if sizes else 0
    frac = (largest / len(complex_domain)) if complex_domain else 0.0
    print("\n=== Test 3: BridgePreconnected_fromSource (Graph Surrogate) ===")
    print(f"knn_k={args.knn_k}")
    print(f"graph_components={components}")
    print(f"largest_component_size={largest}")
    print(f"largest_component_fraction={frac:.6f}")
    print("component_sizes_top10=" + str(sizes[:10]))

    # Test 5: ForwardWitnessEq_field_deferred (source-to-forwardizable surrogate).
    # This uses only source-side sampled constraints, then probes complex
    # forwardizable tuples.
    worst_forward = worst_value_over_samples(coeffs_source, basis, complex_domain)
    print("\n=== Test 5: ForwardWitnessEq_field_deferred (Heuristic) ===")
    print(f"worst_|g|_on_complex_forwardizable_domain_from_source_constraints={worst_forward:.6e}")
    print(f"report_threshold={args.report_threshold:.1e}")
    print(
        "status="
        + (
            "NO_NUMERIC_FALSIFIER_FOUND"
            if worst_forward <= args.report_threshold
            else "POTENTIAL_FALSIFIER_FOUND"
        )
    )


if __name__ == "__main__":
    main()
