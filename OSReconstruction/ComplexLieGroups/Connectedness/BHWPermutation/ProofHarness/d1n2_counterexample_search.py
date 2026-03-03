#!/usr/bin/env python3
"""
Heuristic falsification search for the active d=1,n=2 invariant blocker.

We search for an antisymmetric polynomial
  g(q0,q1,p,s) = f(q0,q1,p,s) - f(q1,q0,p,-s)
that vanishes on sampled real spacelike local-commutativity data, then test
whether g can be nonzero on sampled doubly realizable complex tuples.

This is not a proof either way; it is a reproducible stress test.
"""

from __future__ import annotations

import argparse
import cmath
import random
from dataclasses import dataclass
from typing import List, Sequence, Tuple

import numpy as np


Complex4 = Tuple[complex, complex, complex, complex]


def invariants_from_uv(
    u0: complex, v0: complex, u1: complex, v1: complex
) -> Complex4:
    q0 = -(u0 * v0)
    q1 = -(u1 * v1)
    p = -0.5 * (u0 * v1 + u1 * v0)
    s = u0 * v1 - u1 * v0
    return (q0, q1, p, s)


def quadric_residual(inv: Complex4) -> complex:
    q0, q1, p, s = inv
    return s**2 - 4 * (p**2 - q0 * q1)


def in_ft_from_uv(u0: complex, v0: complex, u1: complex, v1: complex) -> bool:
    return (
        (u0.imag > 0.0)
        and (v0.imag > 0.0)
        and ((u1 - u0).imag > 0.0)
        and ((v1 - v0).imag > 0.0)
    )


def swap_then_lorentz_uv(
    u0: complex, v0: complex, u1: complex, v1: complex, lam: complex
) -> Tuple[complex, complex, complex, complex]:
    # swap first: (u0,v0)<->(u1,v1), then complex boost (u,v)->(lam*u, lam^-1*v)
    inv_lam = 1.0 / lam
    y0u, y0v = lam * u1, inv_lam * v1
    y1u, y1v = lam * u0, inv_lam * v0
    return y0u, y0v, y1u, y1v


def sample_real_spacelike_invariants(rng: random.Random) -> Complex4:
    # Real config x0=(t0,x0), x1=(t1,x1), require (dx)^2-(dt)^2 > 0.
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
        q0, q1, p, s = invariants_from_uv(u0, v0, u1, v1)
        return (complex(q0), complex(q1), complex(p), complex(s))


def sample_ft_uv(rng: random.Random) -> Tuple[complex, complex, complex, complex]:
    # Build u0,v0 with positive imag and increments with positive imag.
    b0 = rng.uniform(0.2, 3.0)
    d0 = rng.uniform(0.2, 3.0)
    db = rng.uniform(0.2, 3.0)
    dd = rng.uniform(0.2, 3.0)
    u0 = complex(rng.uniform(-3.0, 3.0), b0)
    v0 = complex(rng.uniform(-3.0, 3.0), d0)
    u1 = u0 + complex(rng.uniform(-3.0, 3.0), db)
    v1 = v0 + complex(rng.uniform(-3.0, 3.0), dd)
    return u0, v0, u1, v1


def sample_forwardizable_tuple(
    rng: random.Random, lam_trials: int = 100
) -> Complex4 | None:
    u0, v0, u1, v1 = sample_ft_uv(rng)
    if not in_ft_from_uv(u0, v0, u1, v1):
        return None
    for _ in range(lam_trials):
        # Random complex boost parameter in C*.
        r = rng.uniform(0.25, 4.0)
        th = rng.uniform(-np.pi, np.pi)
        lam = cmath.rect(r, th)
        y0u, y0v, y1u, y1v = swap_then_lorentz_uv(u0, v0, u1, v1, lam)
        if in_ft_from_uv(y0u, y0v, y1u, y1v):
            return invariants_from_uv(u0, v0, u1, v1)
    return None


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
    exps = monomial_exponents(max_degree)
    # keep only exponents whose antisym term is not identically zero
    basis: List[AntiBasisTerm] = []
    probe = (
        complex(1.2, 0.3),
        complex(-0.7, 1.1),
        complex(0.6, -0.8),
        complex(1.0, 0.4),
    )
    for e in exps:
        t = AntiBasisTerm(e)
        if abs(t.eval(*probe)) > 1e-12:
            basis.append(t)
    return basis


def build_constraint_matrix(
    basis: Sequence[AntiBasisTerm], samples: Sequence[Complex4]
) -> np.ndarray:
    mat = np.zeros((len(samples), len(basis)), dtype=np.complex128)
    for i, (q0, q1, p, s) in enumerate(samples):
        for j, term in enumerate(basis):
            mat[i, j] = term.eval(q0, q1, p, s)
    return mat


def nullspace_svd(mat: np.ndarray, tol: float = 1e-10) -> np.ndarray:
    if mat.size == 0:
        return np.eye(0, dtype=np.complex128)
    _u, sing, vh = np.linalg.svd(mat, full_matrices=True)
    rank = int(np.sum(sing > tol))
    return vh[rank:].conj().T


def evaluate_g(
    coeff: np.ndarray, basis: Sequence[AntiBasisTerm], inv: Complex4
) -> complex:
    q0, q1, p, s = inv
    vals = np.array([t.eval(q0, q1, p, s) for t in basis], dtype=np.complex128)
    return complex(np.dot(vals, coeff))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260303)
    parser.add_argument("--degree", type=int, default=3)
    parser.add_argument("--real-samples", type=int, default=300)
    parser.add_argument("--test-tuples", type=int, default=2000)
    parser.add_argument("--lam-trials", type=int, default=120)
    parser.add_argument("--svd-tol", type=float, default=1e-10)
    parser.add_argument("--report-threshold", type=float, default=1e-6)
    parser.add_argument("--random-null-combos", type=int, default=12)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    np.random.seed(args.seed % (2**32))

    basis = build_antisym_basis(args.degree)
    real_samples = [sample_real_spacelike_invariants(rng) for _ in range(args.real_samples)]
    amat = build_constraint_matrix(basis, real_samples)
    ns = nullspace_svd(amat, tol=args.svd_tol)

    print(f"seed={args.seed}")
    print(f"degree={args.degree}")
    print(f"antisym_basis_size={len(basis)}")
    print(f"real_constraint_rows={amat.shape[0]}")
    print(f"nullspace_dim={ns.shape[1]}")

    if ns.shape[1] == 0:
        print("No nonzero antisymmetric polynomial found within this basis under sampled constraints.")
        return

    samples_forwardizable: List[Complex4] = []
    attempts = 0
    while len(samples_forwardizable) < args.test_tuples and attempts < 20 * args.test_tuples:
        inv = sample_forwardizable_tuple(rng, lam_trials=args.lam_trials)
        attempts += 1
        if inv is not None:
            samples_forwardizable.append(inv)

    print(f"tested_forwardizable_tuples={len(samples_forwardizable)}")
    max_quadric = max((abs(quadric_residual(inv)) for inv in samples_forwardizable), default=0.0)
    print(f"max_quadric_residual={max_quadric:.3e}")

    best_global = 0.0
    best_hits = 0
    best_tuple: Complex4 | None = None
    for k in range(max(1, args.random_null_combos)):
        if ns.shape[1] == 1 or k == 0:
            coeff = ns[:, 0]
        else:
            re = np.random.randn(ns.shape[1])
            im = np.random.randn(ns.shape[1])
            combo = re + 1j * im
            coeff = ns @ combo
        coeff_norm = float(np.linalg.norm(coeff))
        if coeff_norm <= 0:
            continue
        coeff = coeff / coeff_norm

        max_abs = 0.0
        hits = 0
        max_tuple: Complex4 | None = None
        for inv in samples_forwardizable:
            gv = abs(evaluate_g(coeff, basis, inv))
            if gv > max_abs:
                max_abs = gv
                max_tuple = inv
            if gv > args.report_threshold:
                hits += 1

        print(
            f"combo[{k}] max_|g|={max_abs:.6e}, violations={hits}"
            f" (threshold={args.report_threshold})"
        )
        if max_abs > best_global:
            best_global = max_abs
            best_hits = hits
            best_tuple = max_tuple

    print(f"best_max_|g|={best_global:.6e}")
    print(f"best_violations_over_threshold={best_hits} (threshold={args.report_threshold})")
    if best_tuple is not None:
        q0, q1, p, s = best_tuple
        print("best_tuple_invariants:")
        print(f"  q0={q0}")
        print(f"  q1={q1}")
        print(f"  p ={p}")
        print(f"  s ={s}")


if __name__ == "__main__":
    main()
