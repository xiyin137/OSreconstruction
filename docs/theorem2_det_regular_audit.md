# Theorem 2 det-regularity audit

Date: 2026-06-04

## Question

Does

```lean
p ∈ AdjacentNormal.reducedSelectedSpacelike d i j
```

force the zero-center reduced-normal source representative at `p` to be
det-regular, i.e. to satisfy

```lean
BHW.sourceRealFullFrameDet d (m + 1) ι
  (reducedNormalAbsoluteSectionCLM ... (reducedNormalFlattenCLE ... p)) ≠ 0
```

for the source-oriented frame used by the determinant-regular collar?

## Definitions checked

`reducedSelectedSpacelike` only constrains the selected pair difference:

```lean
def reducedSelectedSpacelike
    {m : ℕ} (i j : Fin (m + 1)) :
    Set (ReducedSpace d m i j) :=
  {p | MinkowskiSpace.IsSpacelike d p.1}
```

The reduced-normal zero-center section reconstructs absolute source points by
setting the selected pair center to zero and applying `coordInv`. In those
absolute coordinates, the selected pair is placed at `-v / 2` and `v / 2`,
while each spectator is placed at its frozen relative coordinate.

The det-regular condition is a full-frame rank condition:

```lean
def sourceRealFullFrameMatrix
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun a μ => x (ι a) μ

def sourceRealFullFrameDet
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) : ℝ :=
  (sourceRealFullFrameMatrix d n ι x).det
```

Thus selected-spacelike controls one vector `p.1`; det-regularity controls the
linear independence of `d + 1` absolute source point rows selected by `ι`.

## Counterexample

Take the minimal full-frame case `d = 2`, `m = 2`, so there are three source
points in three Minkowski coordinates. Let the selected adjacent pair be
`i = 0`, `j = 1`.

Choose selected difference

```text
v = (0, 1, 0)
```

and put the only spectator at the pair center:

```text
spectator = (0, 0, 0).
```

Then `v` is spacelike because its Minkowski square is `1 > 0`. Hence this
reduced-normal point lies in `reducedSelectedSpacelike`.

The zero-center absolute reconstruction is

```text
x_0 = (0, -1/2, 0)
x_1 = (0,  1/2, 0)
x_2 = (0,  0,   0)
```

For the full frame `ι : Fin 3 ↪ Fin 3` selecting all three source labels, the
real full-frame matrix has rows `x_0`, `x_1`, and `x_2`. Its first and third
columns are zero, and the third row is zero, so the determinant is zero.

Therefore:

```text
p ∈ AdjacentNormal.reducedSelectedSpacelike 2 (0 : Fin 3) (1 : Fin 3)
```

but

```text
BHW.sourceRealFullFrameDet 2 3 ι
  (zero-center reduced-normal source representative at p) = 0.
```

## Route impact

The implication

```lean
reducedSelectedSpacelike_implies_detRegular
```

is false. The determinant-regular producer chain does not cover all theorem-2
selected-spacelike points by itself.

Consequently the rank-deficient / low-frame branch is genuine theorem-2 work,
not an empty case. The remaining route must either:

1. build a rank-deficient producer chain, or
2. prove a stratification/removable-boundary argument showing that the
   determinant-regular chain determines the desired distributional pairing on
   the rank-deficient locus, or
3. isolate degenerate configurations where OS permutation symmetry gives the
   required equality directly.

This audit also confirms that the current det-regular conditional bridges
should be treated as a dense/open-leg producer, not as a complete replacement
for the arbitrary selected-spacelike theorem-2 hypothesis.
