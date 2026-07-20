# Heights work log

## P0 — 2026-07-20 (`0e77dc1`)

Bootstrapped the pinned Lean/mathlib package, added the import/link-check scaffold,
repository orchestration metadata, and the private Silverman chapter extraction.
No blueprint, comparator, audits, or mathematical formalization was added.

## P0 spec — 2026-07-20 (`bf8109e`, `8679329`)

Authored and adversarially reviewed `Plans/HeightsSpec.md` (2 rounds: round 1
CHANGES REQUESTED on two API-accuracy defects, round 2 ACCEPTED). Filed two
child issues under taxis #32 for the mathlib-scale gaps the spec identified:
#56 (global minimal-discriminant ideal assembly over number fields, needed by
P4/P5) and #57 (complex uniformization bridge between `WeierstrassCurve.j`
and the modular `j`-function, needed by P8/P9). P0 gate closed.

## Autonomous run 1 — 2026-07-20

The first autonomous run added six small, audited commits:

* `3d03f66` defines absolute normalized logarithmic height, proves its rational
  numerator/denominator formula (including `0`), and passes the first comparator
  target.
* `ebb2b5b` proves weighted Jensen and nonnegativity bounds, specializes them to
  infinite-place multiplicities with total weight `[K : ℚ]`, and passes the
  second comparator target.
* `3e546de` defines the correctly normalized modular discriminant and modular
  `j`, proves nonvanishing/denominator identities, and records the `q`-product.
* `d305145` compiles the honest local-minimal, global-ideal, period, and reduced
  principal-ideal interfaces. No existence theorem or comparison is packaged in
  them.
* `6283a5e` defines Silverman's finite-plus-archimedean height expression from
  the realization interfaces and proves every logarithm argument and its degree
  denominator are positive. It is not identified with an Arakelov height.
* `713420f` constructs and proves uniqueness/nonvanishing of the complementary
  unstable ideal once denominator divisibility is proved, and splits the
  logarithmic minimal-discriminant norm accordingly. It does not assume or
  prove denominator divisibility.

`./scripts/ci-checks.sh` passes through `713420f`; the public axiom audit reports
only `propext`, `Quot.sound`, and `Classical.choice`. The next substantive open
fronts are the canonical reduced-principal-ideal/finite-place height identity,
denominator divisibility from local minimality, and the absolute modular
fundamental-domain estimates. The two realization gaps (#56 and #57) remain
honestly certificate-level.

## Autonomous run 2 — 2026-07-20 (`cd4aeb8`; orchestrator polled and pushed per-commit throughout)

Landed (pushed as each commit appeared, per the revised push-after-every-commit
protocol): `2f3ac46` (GitHub Actions CI + staged Verso blueprint Pages
deployment — see the private-repo caveat below), `47aa6cd` (local `j`-pole
bounds by minimal discriminants), `fe71948` (**proves**
`denominator_dvd_minimalDiscriminant` — `D ∣ Δmin` is now a theorem, not a
hypothesis, closing the gap round-1 P1 review flagged), `072467c` (canonical
`unstableMinimalDiscriminant` built from that proof, replacing the free-`γ`
interface), `01c5c12` (`twelve_mul_silvermanHeight_eq`,
`comparisonExpression_eq` — the exact algebraic identity reducing Proposition
2.1's certified comparison to a finite-place term plus the archimedean sum),
`fe46dbc`–`1628547` (per-finite-place and global finite-place Weil-height
identities, including `x = 0`), `cd4aeb8` (reduces the certified comparison
expression to purely archimedean modular terms — the finite-place side of the
certified Proposition 2.1 comparison is now essentially complete; the
remaining open front is the archimedean modular fundamental-domain estimate,
now being worked in parallel as issue #99).

Run validated `LAKE_JOBS=6 lake build`, `Blueprint/scripts/ci-pages.sh`,
`./scripts/ci-checks.sh`, and the trust/axiom audits before finishing;
independently re-verified by the orchestrator. GitHub Pages for the blueprint
will 404 until the repo is public (requires purging the copyrighted PDF from
history first) or the org enables Pages for private repos.

## Autonomous run 3 — 2026-07-20 (`5a93557`, main line, run concurrently with 3 sub-issue agents)

Deliberately avoided `Heights/ModularJ.lean` and `Heights/Certificates.lean`
(owned by the concurrent issue-99/100/101 agents). Landed:
`159b1fd` (certified good/multiplicative reduction, `IsSemistable`; proves
semistability gives `D = Δmin` hence `unstableMinimalDiscriminant m r = ⊤`),
`45d2f85` (specializes the archimedean comparison identity to the semistable
case), `5a93557` (derives the semistable absolute-value bound from the
general corrected bounds). Independently re-verified: full
`LAKE_JOBS=6 ./scripts/ci-checks.sh` passes, 170 declarations audited, all
within `{propext, Quot.sound, Classical.choice}`. Filed and labeled
`ready-to-clanck` #113 (complete equation (11): bound the archimedean
log-log sum by normalized `j`-height) and #115 (the `ε`-absorption bound for
the rational specialization, `Plans/HeightsSpec.md` P7).

## Parallel sub-issue agents launched — 2026-07-20

Per owner directive, launched 3 sub-issue pi agents in dedicated git
worktrees off `main@fe46dbc` (each claimed via the `o-claimed` label +
assignee + comment, each capped at `LAKE_JOBS=4`, cap of 3 concurrent
sub-issue agents plus the 1 main-line agent): issue-99 (modular
fundamental-domain estimate, `Heights/ModularJ.lean` only), issue-100
(construct `ReducedPrincipalIdealData`, `Heights/Certificates.lean` only),
issue-101 (construct `GlobalMinimalDiscriminantData` over `ℚ`, first slice of
#56, `Heights/Certificates.lean` only). Also filed `ready-to-clanck` (label 3)
#102 (audit tooling: verify blueprint `lean :=` links) and #103 (blueprint
proof-sketch prose) for later pickup, left unclaimed under the concurrency
cap. No `gh`/GitHub API PR token exists yet, so resolved sub-issue branches
are self-merged into `main` by the orchestrator after independent
verification, not opened as real PRs.

**Orchestrator side-quest while run 2 was in flight:** filed and labeled
`ready-to-clanck` (id 3) five self-contained, dedup-checked parallelizable
subtasks under #32, chosen to not touch any file run 2 is currently editing
(`Heights/IdealFactorization.lean`, `Heights/SilvermanHeight.lean`,
`Heights/Certificates.lean`):
* #99 — prove `modular_delta_j_fd_comparison` (the archimedean fundamental-domain
  estimate; pure modular-forms analysis, `Heights/ModularJ.lean`).
* #100 — construct `ReducedPrincipalIdealData` for any nonzero number-field
  element (should be unconditionally provable via Dedekind factorization, not
  certificate-level — currently only ever assumed as a hypothesis).
* #101 — first slice of #56: construct `GlobalMinimalDiscriminantData` for
  elliptic curves over `ℚ` specifically (tractable; general number fields
  remain #56's harder open case).
* #102 — audit tooling: verify the blueprint's `lean :=` links actually
  resolve to real compiling declarations.
* #103 — blueprint proof-sketch prose for already-`lean :=`-linked nodes
  (currently signature restatements, not real exposition).
