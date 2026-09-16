# Standard Lean Comparator

Start with **[Definitions.lean](Definitions.lean)**. It contains the mathematical
definitions and the three reconstruction propositions in one Mathlib-only Lean
file. It imports no implementation modules. Ordinary Mathlib notions, such as
Schwartz functions, integration and differentiability, retain their usual
library definitions.

The [HTML mathematical specification](../../docs/COMPARATOR_NOTE.html) states the
test spaces, quantified axioms, growth conditions, Wick pairing, fixed reverse
constructor, and all three propositions in mathematical notation. It covers
every named declaration in `Definitions.lean`, with source names alongside.
Each definition and statement has mathematical-physics commentary, and reused
defined symbols link back to their definitions. The growth section also explains
the correspondence with OS II and the equivalence of the two input conditions.

This uses the official [leanprover/comparator](https://github.com/leanprover/comparator),
following the same Challenge/Solution arrangement as
[sphere-six-complex](https://github.com/deancureton/sphere-six-complex).
The definitions are shared between the two environments; they are not generated
copies of the implementation's declarations.

| File | Role |
| --- | --- |
| [Definitions.lean](Definitions.lean) | Trusted mathematical definitions and propositions. |
| [Challenge.lean](Challenge.lean) | Three named targets, with intentional theorem proof placeholders. |
| [Solution.lean](Solution.lean) | The same targets, proved using the implementation and adapters. |
| [WightmanBridge.lean](WightmanBridge.lean), [OSBridge.lean](OSBridge.lean) | Correspondence between the audit definitions and implementation records. |
| [ReverseBridge.lean](ReverseBridge.lean) | Identity between the independently defined reverse constructor and the implementation. |
| [comparator.json](comparator.json) | Exact targets and axiom whitelist; no definition holes. |

The targets are `OSReconstructionAudit.e_to_r`, `e_to_r_osii`, and `r_to_e`.
The reverse target uses `constructSchwinger` from `Definitions.lean`.
`constructSchwinger_eq` in `ReverseBridge.lean` proves that this independently
defined function agrees with the production Schwinger constructor. The existing
[Contracts.lean](../Contracts.lean) also checks the original reverse proposition
with its exact production constructor. The reverse direction does not conclude
an OS growth condition.

`Solution.lean` proves equivalence with each original specification before
applying the production theorems. Changes to the implementation must preserve
these proofs or prompt a deliberate review of the mathematical statements in
`Definitions.lean`. Verification never regenerates that trusted file.

## Run

From the authoritative `os-reconstruction/` package:

```sh
# Linux: sandboxed build/export, statement comparison, whitelist, kernel replay.
bash verification/check.sh comparator

# macOS or local development: explicitly opt into unsandboxed build/export.
bash verification/check.sh comparator --development
```

The first run fetches and builds the source revisions in
[tool-versions.sh](tool-versions.sh). It requires Git, Bash, Ruby and elan;
Linux sandbox setup additionally requires Go 1.24 or newer and a working
`systemd-run --user` service manager. Tools are cached outside the project's
writable `.lake` directory, under
`${XDG_CACHE_HOME:-$HOME/.cache}/osreconstruction-comparator` by default.
Set `OS_COMPARATOR_TOOLS_DIR` to choose another absolute path. The package's
Lean toolchain is 4.33.0-rc1. Comparator builds with its own toolchain,
while the exporter is pinned to match the package's version.

The Linux runner follows upstream's `systemd-run` restriction on Unix sockets.
It also removes Comparator's `--best-effort` Landrun flag, so an unsupported
Landlock policy causes a failure instead of a weaker sandbox. The pinned
Landrun requires a kernel with Landlock ABI 9 for this strict policy.
Development mode uses upstream's explicitly unsandboxed shim and prints that
limitation. A successful development run is **not** evidence of sandbox
isolation.

Dependencies must already be available locally, for example after the usual
`lake exe cache get`. Sandbox builds have no network access. Use a trusted
checkout and dependency cache; for adversarial submissions, follow upstream's
[trust assumptions](https://github.com/leanprover/comparator#readme) before
building any submitted code.

## What acceptance establishes

Comparator exports the Challenge and Solution environments separately, checks
that target statements and all constants in their definition closure match,
checks the solution's transitive axiom closure, and replays the exported proof
in a fresh Lean kernel environment. Only `propext`, `Quot.sound` and
`Classical.choice` are permitted. The Challenge placeholders are never imported
by the Solution or by the default production build.

The recorded verification uses `enable_nanoda: false`: proof replay runs in a
fresh instance of Lean's kernel. Nanoda, a separate kernel implementation, has
not been tested on this package; no compatibility or performance result for it
is claimed. Here independence refers to the separate mathematical specification,
exported-environment comparison, and fresh replay. Verification by a second
kernel implementation remains an additional check. The source gate does not
pin `enable_nanoda`, since enabling that optional check does not remove the
mandatory Lean replay or relax the target, definition-hole, or axiom checks.

The source gate also checks this boundary, and the existing `quick`,
`contracts`, and `full` verification commands remain available. `contracts`
and `full` typecheck Challenge and Solution as separate modules; the standard
Comparator performs the additional exported-environment checks. Comparator does
not replace mathematical review of the trusted definitions or the adapters'
intended interpretation.
