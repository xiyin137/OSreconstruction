# CLAUDE.md — Project Instructions for Claude Code

## Project Overview

This is a Lean 4 formalization of the Osterwalder-Schrader reconstruction theorem, built on Mathlib (v4.28.0) with a `gaussian-field` dependency. The codebase covers Wightman axioms, von Neumann algebras, several complex variables (SCV), and complex Lie groups.

## Lean Code Writing Workflow

**Do not try to write all code at once.** Follow this iterative process:

1. Write down as much Lean code as you can in one run.
2. Check Lean MCP feedback (e.g., error messages, type mismatches, unknown identifiers) for any mistakes.
3. Correct the errors based on the feedback.
4. Repeat until the code compiles cleanly or the only remaining gaps are intentional `sorry` placeholders.

This incremental approach avoids compounding errors and catches Mathlib API mismatches early.

## Proof Planning

When planning a proof, if you are unsure about an intermediate step or unsure whether an existing definition is correct for the intended purpose, **ask the user** before proceeding. Do not guess at mathematical correctness — request human intervention to clarify the proof strategy or validate definitions.

## Explaining Theorems and Definitions

When asked to explain a theorem or definition in the codebase, **always read the actual Lean code** (the `def`, `structure`, `theorem`, `lemma`, `class`, etc.) rather than relying solely on comments or docstrings. Comments can be outdated or incomplete — the code is the source of truth.

## Environment

- `gh` (GitHub CLI) is at `/opt/homebrew/bin/gh` (not on default PATH — use full path)

## Build Commands

- Full build: `lake build`
- Targeted build (most common): `lake build OSReconstruction.Wightman.Reconstruction.Main`
- **Avoid using `lake build` as much as possible.** Prefer using IDE diagnostics and `lake env lean <file>` for single-file checking. Full builds are slow and should only be used when necessary.

## Key Conventions

- Lean 4 with Mathlib — always check Mathlib API names rather than guessing.
- `sorry` is used as an explicit placeholder for unfinished proofs in production; do not silently remove or replace `sorry` without a verified proof.
- Explicit `axiom` declarations are used for deferred hard-analysis results (currently 7 in the tracked tree). Do not remove or modify axioms without discussion.
- Prefer editing existing files over creating new ones.
- Follow the route discipline described in README.md: the OS semigroup/Hilbert-space/analytic-continuation route is the canonical E -> R path.

## Communication and PR Workflow

- All design discussions, strategy notes, and communications with other agents should be written as markdown files under the `communication/` folder.
- **Before submitting any PR**, read the relevant files in `communication/` and incorporate their reasoning into the PR description:
  - If the PR includes **major definition changes** (new structures, redefined types, changed axiom surfaces), explain *why* the old definition was inadequate and what the new one does better, citing the communication docs.
  - If the PR only **fills in sorries or proves axioms** without changing definitions, keep the description concise — do not over-explain.
- PR descriptions should contain only the summary section — do not include a test plan.
- **When creating a PR to the original repo**, do not include `CLAUDE.md` or the `communication/` folder in the PR. These are local project-management files and should not be pushed upstream.

## File Organization

- `OSReconstruction/Wightman/` — Wightman axioms, reconstruction, Wick rotation
- `OSReconstruction/SCV/` — several complex variables infrastructure
- `OSReconstruction/ComplexLieGroups/` — BHW/Lorentz connectedness
- `OSReconstruction/vNA/` — von Neumann algebra foundations
- `OSReconstruction/Bridge/` — axiom bridges between modules
- `Proofideas/` — scratch/experimental work, not production
