# heights — contributor instructions

## Mission

Formalize the comparison between the logarithmic Weil height of an elliptic
curve's `j`-invariant and its Faltings height, following J. H. Silverman,
“Heights and Elliptic Curves,” Chapter X of Cornell–Silverman (eds.),
*Arithmetic Geometry* (Springer, 1986), especially Proposition 2.1.

## Copyright boundary

This repository is public. Do not commit scans, PDFs, OCR output, or substantial
extracts from copyrighted references. In particular,
`references/arithmetic_geometry.pdf` and `references/silverman-heights.txt` are
ignored local-only paths and must remain absent from Git history. Cite published
sources and consult a legally obtained copy when checking the literature.

## Project status

- `Plans/HeightsSpec.md` records the formalization design and honesty boundary.
- `Plans/HeightsWorkLog.md` records completed work and the latest handoff.
- `Plans/AnalyticPeriodFeasibility.md` tracks the remaining analytic gates.
- Taxis issue #32 is the umbrella project. Its unassigned `ready-to-clanck`
  children are the preferred independently actionable tasks.

The unconditional theorem currently compares Weil height with the repository's
formula-defined `silvermanHeightOfCurve`. Do not identify that definition with
an Arakelov/Faltings height until the remaining analytic realization and
identification theorems have actually been proved.

## Development workflow

- The project is pinned by `lean-toolchain` and `lake-manifest.json`.
- Keep Lean changes small and commit coherent milestones.
- Run targeted `lake build` checks while developing.
- Before handing off a completed slice, run `LAKE_JOBS=6 ./scripts/ci-checks.sh`.
- Preserve the trust audits. Do not add `axiom`, `sorry`, `admit`, unsafe
  declaration tricks, or structures whose hypotheses simply encode the desired
  conclusion.
- Update the Blueprint and relevant planning/status documents when theorem
  status changes.
- Never commit credentials or agent-specific orchestration state.

## Public repository

The canonical remote is `https://github.com/lana-agents/heights`. Open work
should be based on current `main`; claim the corresponding Taxis task before
starting when the board's current agent protocol requires it.
