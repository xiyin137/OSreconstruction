#!/usr/bin/env python3
"""
Numerical sanity checks for the d=1,n=2 invariant witness conditions used in
Tail.lean.

This script checks equivalence between:
1) The intrinsic witness inequalities in invariant variables (q0,q1,p,s,v0,w0),
2) The intended ForwardTube inequalities on light-cone coordinates (u0,v0,u1,v1)
   for the corresponding section points.

It also checks reconstruction consistency from sampled FT points.
"""

from __future__ import annotations

import argparse
import random
from typing import Tuple


UV4 = Tuple[complex, complex, complex, complex]
INV4 = Tuple[complex, complex, complex, complex]


def invariants_from_uv(u0: complex, v0: complex, u1: complex, v1: complex) -> INV4:
    q0 = -(u0 * v0)
    q1 = -(u1 * v1)
    p = -0.5 * (u0 * v1 + u1 * v0)
    s = u0 * v1 - u1 * v0
    return (q0, q1, p, s)


def quadric_residual(q0: complex, q1: complex, p: complex, s: complex) -> complex:
    return s**2 - 4 * (p**2 - q0 * q1)


def in_ft_uv(u0: complex, v0: complex, u1: complex, v1: complex, eps: float) -> bool:
    return (
        (u0.imag > eps)
        and (v0.imag > eps)
        and ((u1 - u0).imag > eps)
        and ((v1 - v0).imag > eps)
    )


def section_orig_uv(q0: complex, p: complex, s: complex, v0: complex) -> UV4:
    # d1N2SectionOrig q0 q1 p s v0 = d1N2InvariantSection (-q0) (-p) s v0
    u0 = (-q0) / v0
    u1 = (-p - s / 2) / v0
    v1 = (p - s / 2) * v0 / q0
    return (u0, v0, u1, v1)


def section_swap_uv(q1: complex, p: complex, s: complex, w0: complex) -> UV4:
    # d1N2SectionSwap q0 q1 p s w0 = d1N2InvariantSection (-q1) (-p) (-s) w0
    u0 = (-q1) / w0
    u1 = (-p + s / 2) / w0
    v1 = (p + s / 2) * w0 / q1
    return (u0, w0, u1, v1)


def orig_invariant_witness_cond(
    q0: complex, p: complex, s: complex, v0: complex, eps: float
) -> bool:
    if abs(q0) <= eps or abs(v0) <= eps:
        return False
    return (
        (v0.imag > eps)
        and (((-q0) / v0).imag > eps)
        and (((q0 - p - s / 2) / v0).imag > eps)
        and ((((p - s / 2 - q0) * v0 / q0).imag) > eps)
    )


def swap_invariant_witness_cond(
    q1: complex, p: complex, s: complex, w0: complex, eps: float
) -> bool:
    if abs(q1) <= eps or abs(w0) <= eps:
        return False
    return (
        (w0.imag > eps)
        and (((-q1) / w0).imag > eps)
        and (((q1 - p + s / 2) / w0).imag > eps)
        and ((((p + s / 2 - q1) * w0 / q1).imag) > eps)
    )


def sample_ft_uv(rng: random.Random) -> UV4:
    b0 = rng.uniform(0.2, 3.0)
    d0 = rng.uniform(0.2, 3.0)
    db = rng.uniform(0.2, 3.0)
    dd = rng.uniform(0.2, 3.0)
    u0 = complex(rng.uniform(-3.0, 3.0), b0)
    v0 = complex(rng.uniform(-3.0, 3.0), d0)
    u1 = u0 + complex(rng.uniform(-3.0, 3.0), db)
    v1 = v0 + complex(rng.uniform(-3.0, 3.0), dd)
    return (u0, v0, u1, v1)


def sample_complex_nonzero(rng: random.Random, min_abs: float = 0.25) -> complex:
    while True:
        z = complex(rng.uniform(-3.0, 3.0), rng.uniform(-3.0, 3.0))
        if abs(z) > min_abs:
            return z


def max_abs_diff(a: UV4, b: UV4) -> float:
    return max(abs(a[i] - b[i]) for i in range(4))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260303)
    parser.add_argument("--pointwise-samples", type=int, default=20000)
    parser.add_argument("--recon-samples", type=int, default=3000)
    parser.add_argument("--pair-samples", type=int, default=1500)
    parser.add_argument("--eps", type=float, default=1e-10)
    parser.add_argument("--find-trials", type=int, default=250)
    args = parser.parse_args()

    rng = random.Random(args.seed)

    pointwise_orig_mismatch = 0
    pointwise_swap_mismatch = 0
    for _ in range(args.pointwise_samples):
        q0 = sample_complex_nonzero(rng)
        q1 = sample_complex_nonzero(rng)
        p = sample_complex_nonzero(rng, min_abs=0.0)
        s = sample_complex_nonzero(rng, min_abs=0.0)
        v0 = sample_complex_nonzero(rng)
        w0 = sample_complex_nonzero(rng)

        inv_orig = orig_invariant_witness_cond(q0, p, s, v0, args.eps)
        u0o, v0o, u1o, v1o = section_orig_uv(q0, p, s, v0)
        coord_orig = in_ft_uv(u0o, v0o, u1o, v1o, args.eps)
        if inv_orig != coord_orig:
            pointwise_orig_mismatch += 1

        inv_swap = swap_invariant_witness_cond(q1, p, s, w0, args.eps)
        u0s, w0s, u1s, v1s = section_swap_uv(q1, p, s, w0)
        coord_swap = in_ft_uv(u0s, w0s, u1s, v1s, args.eps)
        if inv_swap != coord_swap:
            pointwise_swap_mismatch += 1

    recon_orig_fail = 0
    recon_swap_fail = 0
    max_recon_orig_err = 0.0
    max_recon_swap_err = 0.0
    max_quadric_res = 0.0

    for _ in range(args.recon_samples):
        u0, v0, u1, v1 = sample_ft_uv(rng)
        if not in_ft_uv(u0, v0, u1, v1, args.eps):
            continue
        q0, q1, p, s = invariants_from_uv(u0, v0, u1, v1)
        max_quadric_res = max(max_quadric_res, abs(quadric_residual(q0, q1, p, s)))

        if abs(q0) <= args.eps:
            continue
        if not orig_invariant_witness_cond(q0, p, s, v0, args.eps):
            recon_orig_fail += 1
            continue
        z2 = section_orig_uv(q0, p, s, v0)
        max_recon_orig_err = max(max_recon_orig_err, max_abs_diff((u0, v0, u1, v1), z2))
        if not in_ft_uv(*z2, args.eps):
            recon_orig_fail += 1

        # Build swapped tuple directly from this y=(u0,v0,u1,v1):
        # If y has invariants (qy0,qy1,py,sy), then y is a witness for
        # (q0,q1,p,s) = (qy1,qy0,py,-sy) on the swap side.
        qy0, qy1, py, sy = q0, q1, p, s
        qs0, qs1, ps, ss = qy1, qy0, py, -sy
        if abs(qs1) <= args.eps:
            continue
        if not swap_invariant_witness_cond(qs1, ps, ss, v0, args.eps):
            recon_swap_fail += 1
            continue
        y2 = section_swap_uv(qs1, ps, ss, v0)
        max_recon_swap_err = max(max_recon_swap_err, max_abs_diff((u0, v0, u1, v1), y2))
        if not in_ft_uv(*y2, args.eps):
            recon_swap_fail += 1

    pair_total_considered = 0
    pair_with_orig_witness = 0
    pair_with_swap_witness_found = 0
    pair_no_swap_witness_found = 0
    pair_validation_fail = 0
    for _ in range(args.pair_samples):
        u0, v0, u1, v1 = sample_ft_uv(rng)
        if not in_ft_uv(u0, v0, u1, v1, args.eps):
            continue
        q0, q1, p, s = invariants_from_uv(u0, v0, u1, v1)
        pair_total_considered += 1
        if abs(q0) <= args.eps or abs(q1) <= args.eps:
            continue
        if not orig_invariant_witness_cond(q0, p, s, v0, args.eps):
            continue
        pair_with_orig_witness += 1

        found = False
        for _ in range(args.find_trials):
            w0 = sample_complex_nonzero(rng)
            if swap_invariant_witness_cond(q1, p, s, w0, args.eps):
                y = section_swap_uv(q1, p, s, w0)
                qy0, qy1, py, sy = invariants_from_uv(*y)
                ok_inv = (
                    abs(qy0 - q1) < 1e-7
                    and abs(qy1 - q0) < 1e-7
                    and abs(py - p) < 1e-7
                    and abs(sy + s) < 1e-7
                )
                if in_ft_uv(*y, args.eps) and ok_inv:
                    pair_with_swap_witness_found += 1
                    found = True
                    break
                pair_validation_fail += 1
                found = True
                break
        if found:
            pass
        else:
            pair_no_swap_witness_found += 1

    print(f"seed={args.seed}")
    print(f"pointwise_samples={args.pointwise_samples}")
    print(f"pointwise_orig_mismatch={pointwise_orig_mismatch}")
    print(f"pointwise_swap_mismatch={pointwise_swap_mismatch}")
    print(f"recon_samples={args.recon_samples}")
    print(f"recon_orig_fail={recon_orig_fail}")
    print(f"recon_swap_fail={recon_swap_fail}")
    print(f"max_recon_orig_uv_error={max_recon_orig_err:.3e}")
    print(f"max_recon_swap_uv_error={max_recon_swap_err:.3e}")
    print(f"max_quadric_residual={max_quadric_res:.3e}")
    print(f"pair_samples={args.pair_samples}")
    print(f"pair_total_considered={pair_total_considered}")
    print(f"pair_with_orig_witness={pair_with_orig_witness}")
    print(f"pair_with_swap_witness_found={pair_with_swap_witness_found}")
    print(f"pair_no_swap_witness_found={pair_no_swap_witness_found}")
    print(f"pair_validation_fail={pair_validation_fail}")


if __name__ == "__main__":
    main()
