# Counting time in one's own measurements: the Lorentz *c* of a time series, verified in Lean

**Ian Carleton** · ORCID [0009-0000-5071-0367](https://orcid.org/0009-0000-5071-0367)

This repository holds a Lean-verified **kinematics of the Lorentz *c* for time series** in three state variables, together with the paper that states it in ordinary mathematical notation.

## What is proved

The setting is an observer who records a state in three variables, counts time in its own measurements (tick *k* is time *k*), and takes its unit of length from its own window (the metric *M*⁻¹, where *M* is the second moment of the window's steps).

**Part I, one observer** (library `GeneralizedC`):
- every window whose steps span ℝ³ has exactly one Lorentz *c*: its largest step, in the window's own unit;
- every pair of samples in the window is then causally separated, and one step is lightlike;
- √3 ≤ *c* ≤ √*N*, where *N* is the number of steps;
- *c* does not depend on the units of the axes;
- after rescaling to *c* = 1, the textbook Lorentz group O(1,3) leaves the window's critical speed at 1.

**Part II, between observers** (library `GeneralizedCSymmetry`, which imports Part I and does not change it):
- the cross-speed of one observer's steps in another observer's frozen unit: existence, uniqueness, unit-freeness;
- when two observers share one cone, and a complete list of the ways they can fail to;
- Ignatowsky's theorem in 1+1: a family of frame changes that satisfies reciprocity, parity, group closure and time order is one Lorentz-type family with exactly one parameter *K* ≥ 0. Its invariant speeds are exactly those with *K u*² = 1.

**Not claimed:**
- that any system's law of motion is Lorentz-invariant (dynamical invariance);
- that *c* is a speed of light or of a signal;
- Ignatowsky's theorem in 1+3.

See the paper's §5 for the full scope.

## Contents

| Path | What it is |
|---|---|
| `paper/main.tex`, `paper/main.pdf` | the paper (CC-BY-4.0) |
| `lean/GeneralizedC/` | Part I: 15 files |
| `lean/GeneralizedCSymmetry/` | Part II: 3 files |
| `lean/Axioms.lean`, `lean/AxiomsSymmetry.lean` | the axiom audits: 103 and 31 `#print axioms` lines |
| `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json` | Lean v4.35.0, Mathlib v4.35.0, pinned |

## How to verify

You need [elan](https://github.com/leanprover/elan). Then run:

```bash
cd lean
lake exe cache get              # prebuilt Mathlib
lake build                      # must finish with no errors and no "declaration uses 'sorry'"
lake env lean Axioms.lean       # Part I audit
lake env lean AxiomsSymmetry.lean   # Part II audit
```

Every audit line must list only `propext`, `Classical.choice` and `Quot.sound`.

**Release check (2026-11-27).** The `lean/` tree in this release (git tree `92bd7069728214e9bd50f069cecceafa81624238`) was built with `leanprover/lean4:v4.35.0`. `lake build` finished cleanly (2834 jobs; no errors, no `sorry`). The audits printed 103 (Part I) and 31 (Part II) results, every one depending only on `[propext, Classical.choice, Quot.sound]`; no `sorryAx` appears. Compare the tree hash with `git rev-parse HEAD:lean`. Any `sorryAx` would mean a gap. The Lean checker, not the author, certifies the theorems. The paper only states what they say.

## How to cite

See `CITATION.cff`; GitHub shows a "Cite this repository" button. The DOI will be added here once the Zenodo archive is minted.

## AI assistance

The question, the definitions' intent, every decision on scope and wording, and the review of each result are the author's. The Lean proofs and the drafting of this text were done with the assistance of an AI model (Claude, Anthropic). The model is not an author. Correctness of the theorems rests on the Lean build and the axiom audits above, which anyone can rerun.

## Licence

- The Lean code is licensed under Apache-2.0 (`LICENSE`).
- The paper text and figures are licensed under CC-BY-4.0 (`LICENSE-paper`).
