# Connected Lorentz/Poincare Migration

## Purpose

This note explains the April 2026 cleanup that changed the default meaning of
`LorentzGroup` and `PoincareGroup` in the Wightman/reconstruction layer.

The short version is:

- `LorentzGroup d` now means the connected proper-orthochronous Lorentz group
  `SO^+(1,d)`.
- `PoincareGroup d` now means the connected proper-orthochronous Poincare group
  `ISO^+(1,d) = R^(d+1) ⋊ SO^+(1,d)`.
- The full disconnected groups are still present, but under explicit names:
  `FullLorentzGroup d` and `FullPoincareGroup d`.

This matches the standard physics-facing covariance convention used by the
Wightman and Osterwalder-Schrader axioms. Parity and time reversal are not part
of the default covariance group.

## Why this change was needed

Before this migration, the repo used a stronger and less standard default
meaning:

- `LorentzGroup d` meant the full group `O(1,d)`.
- `PoincareGroup d` meant the full semidirect product with `O(1,d)`.
- the physically standard proper-orthochronous subgroup appeared as a
  secondary `Restricted` surface.

That created a mismatch between:

- the mathematical objects used in the Wick-rotation / BHW / forward-tube route,
- the standard Wightman/OS axiom surfaces,
- and the names exposed to collaborators working in the public reconstruction
  API.

The result was repeated translation layers like “restricted covariance,” even in
places where the connected component was already the only physically intended
group.

## New naming convention

### Lorentz side

New default meaning:

- `LorentzGroup d` = connected proper-orthochronous Lorentz group `SO^+(1,d)`

Explicit full group:

- `FullLorentzGroup d` = full Lorentz group `O(1,d)`

Discrete symmetry helpers that remain available:

- `LorentzGroup.parity`
- `LorentzGroup.timeReversal`

These now live as compatibility accessors into the full group, rather than
being bundled into the default covariance group.

### Poincare side

New default meaning:

- `PoincareGroup d` = connected proper-orthochronous Poincare group

Explicit full group:

- `FullPoincareGroup d` = full Poincare group with full Lorentz factor

## Mathematical rationale

The standard scalar QFT covariance convention is:

- Wightman side: proper-orthochronous Poincare covariance
- Euclidean/OS side: Euclidean rotation covariance by `SO`, with reflection
  positivity handling the time-reflection part separately

So the connected component is the right default object for the ordinary axiom
package. Full `O(1,d)` or full `O(d+1)` symmetry is extra structure, not the
default covariance assumption.

This migration does **not** delete the full groups. It just stops treating them
as the default meaning of “Lorentz group” or “Poincare group.”

## Main code changes

### Foundational group definitions

The key files are:

- [Lorentz.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Groups/Lorentz.lean)
- [Poincare.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Groups/Poincare.lean)

The main outcome is:

- `LorentzGroup d` now packages the proper + orthochronous conditions directly
- `PoincareGroup d` now uses that connected Lorentz factor directly
- `FullLorentzGroup d` and `FullPoincareGroup d` preserve the old ambient full
  groups

### Bridge layer

The bridge file is:

- [AxiomBridge.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Bridge/AxiomBridge.lean)

The preferred conversion names are now:

- `lorentzGroupToWightman`
- `wightmanToLorentzGroup`

Old restricted-wrapper bridge names were removed from the Wightman side.

### Public analytic / Wick-rotation surfaces

The following public theorem surfaces were normalized from old
`Restricted`-typed statements to bare `LorentzGroup d`:

- [WightmanAxioms.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/WightmanAxioms.lean)
- [AnalyticContinuation.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean)
- [BHWExtension.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean)
- [BHWReducedExtension.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean)
- [ForwardTubeLorentz.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/ForwardTubeLorentz.lean)
- [OSToWightmanTubeIdentity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTubeIdentity.lean)
- [OSToWightmanBoundaryValuesBase.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean)
- [OSToWightmanBoundaryValues.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean)
- [SchwingerAxioms.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean)

This is the main user-facing effect of the migration.

## What was removed

On the Wightman/Poincare side, the following compatibility surfaces are now
gone:

- `LorentzGroup.Restricted`
- `PoincareGroup.IsRestricted`
- `PoincareGroup.Restricted`
- `restrictedLorentzGroupToWightman`
- `wightmanToRestrictedLorentzGroup`

If you still have local code using those names, the fix is not to recreate the
old wrappers. The fix is to use the connected default objects directly.

## What remains

This migration did **not** try to rename every historical occurrence of the word
“restricted” across the entire repository.

In particular, the independent `ComplexLieGroups` subsystem still contains the
name:

- `LorentzLieGroup.RestrictedLorentzGroup`

But in that subsystem it is only a local alias. The actual default connected
object there is already:

- `LorentzLieGroup.LorentzGroup`

So this remaining name is not a mathematical mismatch in the production
Wightman/reconstruction API. It is just older local terminology inside that
independent copy of the connected-complex-Lorentz infrastructure.

## Collaborator guidance

If you are touching Wightman/reconstruction code, use this rule:

- use `LorentzGroup d` when you mean the ordinary physical covariance group
- use `PoincareGroup d` when you mean the ordinary physical Poincare symmetry
- use `FullLorentzGroup d` or `FullPoincareGroup d` only when you genuinely
  need parity, time reversal, or another disconnected-component argument

If you see old local notes or comments talking about “restricted Lorentz” on the
Wightman side, interpret them as historical language for what is now just the
default `LorentzGroup`.

## Verification

The migration was verified with exact Lean builds on the final local state:

- `lake build OSReconstruction.Bridge.AxiomBridge` -> `0`
- `lake build OSReconstruction.Wightman` -> `0`

Those checks were run after the final removal of the dead Wightman-side
compatibility wrappers.

## Bottom line

This migration is a semantic cleanup, not a new physics theorem.

It makes the repo’s default group names match the standard mathematical meaning
used by the Wightman and OS axioms:

- connected proper-orthochronous group as the default
- full disconnected group available only under explicit `Full...` names

That is the intended convention going forward.
