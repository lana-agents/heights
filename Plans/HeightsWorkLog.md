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

## Autonomous run 4 — 2026-07-20 (`701fdaf`, main line, concurrent with the 3 sub-issue agents)

Still avoided `Heights/ModularJ.lean` and `Heights/Certificates.lean`. Picked
up its own run-3 follow-ups plus more: `5950764` (equation (11) specialized
to the actual normalized Weil height, closing #113), `6bbe1dc` (the `ε`-
absorption bound for the P7 rational specialization, closing #115),
`7c1e921` (aggregates the pointwise modular estimates into the corrected
comparison bounds), `a13b2aa` (certified comparison quantifier bridge, in
the correct quantifier order), `701fdaf` (bridge accepting the standard
modular-discriminant estimate form that issue-99's construction is expected
to produce, so that merge should be low-friction once it lands). Blueprint
updated to match. `LAKE_JOBS=6 ./scripts/ci-checks.sh` passed before commit;
orchestrator re-verification is queued (the box is under real load from 3
sub-issue agents running concurrently, so the verification build is slower
than usual — not a correctness concern).

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

## Issue #100 resolved and merged — 2026-07-20 (`0293ae3`)

First sub-issue agent to land (after one transient kill/relaunch with no
lost work — see below). Constructed `exists_reducedPrincipalIdealData` and
the canonical `reducedPrincipalIdealData` in `Heights/Certificates.lean`:
cancels the ideal-theoretic gcd from an arbitrary fraction representation to
produce coprime integral numerator/denominator ideals for any number-field
element, handling `x = 0` via the documented normalization. Pure existence
construction, no comparison content. Merged cleanly (main never touched
`Heights/Certificates.lean` in the interim, confirmed by diffing against the
branch's actual base). Independently re-verified: full `ci-checks.sh`
passes. Taxis #100 closed.

Note: the first attempts at issue-99 and issue-100 were both killed
(`SIGTERM`, exit 143) simultaneously partway through, cause unresolved (not
OOM — memory was never under pressure) but likely incidental to running 4
concurrent `pi` processes plus orchestrator verification builds on this box.
No commits existed in either worktree at the time, so nothing was lost;
both were relaunched fresh and issue-100 completed normally on the second
attempt.

## Autonomous run 5 — 2026-07-20 (`6c97b53`, main line)

Consumed #100's landing: removed every `ReducedPrincipalIdealData K W.j`
hypothesis from `Heights/IdealFactorization.lean`, canonicalizing the
unstable ideal and all downstream comparison/semistable theorems to use
`Heights.reducedPrincipalIdealData` internally instead of taking it as a
parameter — turning those results unconditional in that one respect.
Updated `Plans/HeightsSpec.md` and the Blueprint to match (the headline
`proposition_2_1_certified` signature in the spec no longer quantifies a
witness `r`, using `unstableMinimalDiscriminant m` directly).
`Comparator/config.json`/`Solution.lean` unaffected — neither configured
target used that data, and the headline stays unexported pending the
modular estimate. Independently re-verified: full `ci-checks.sh` passes,
185 declarations audited, all within the permitted axiom set.

## Issue #99 resolved and merged — 2026-07-20 (`ce8915a`)

The last genuinely analytic gap. Proves `modularDeltaJ_fd_comparison` and
the companion `modularIm_logLogJ_fd_comparison` (equation (11)'s archimedean
partner) using cusp asymptotics, the discriminant product expansion, and
truncated fundamental-domain compactness. Exports the comparator target,
updates the Blueprint. Merged cleanly (only `Blueprint.lean` was touched by
both lines of work; auto-merged without conflict). Independently
re-verified: 189 declarations audited, all clean. Taxis #99 closed.

**Milestone:** `thm:proposition-2-1-certified` in the Blueprint is now
"reduced to `prop:modular-estimates`," and that proposition is proved — so
the entire certified Proposition 2.1 chain's *mathematical content* (finite-
place identity, semistable specialization, equation (11), ε-absorption, and
now the archimedean modular estimates) is complete. What remains is purely
the two realization certificates (`GlobalMinimalDiscriminantData`,
`ArchimedeanPeriodData` — #56/#101 and #57). The two now-proved modular
lemmas aren't wired into `proposition_2_1_certified_of_standard_modular_estimates`
yet (that theorem still takes the bounds as existential hypotheses); doing
so is queued as the next main-line step.

Second observation: issue-101 (relaunched after its own kill, on top of
current `main`, with instructions to commit incrementally) has already
produced at least one commit mid-run this time, unlike its first ~4-hour
attempt which produced none — the incremental-commit mitigation appears to
be working.

## Autonomous run 6 — 2026-07-20 (main line)

Closed the final wiring gap in certified Proposition 2.1. The new public
`proposition_2_1_certified` and
`proposition_2_1_semistable_certified` theorems apply the two unconditional
fundamental-domain estimates directly, so their only remaining inputs are
`GlobalMinimalDiscriminantData`, `ArchimedeanPeriodData`, and (for the
specialization) certified semistability. Updated the Blueprint proof links and
status text accordingly. Full `ci-checks.sh` passes; 191 public declarations
were audited, all within the permitted axiom set.

The frozen expanded comparator target also proved compatible with the new
certificate-level theorem. Added uniqueness of the denominator in any reduced
principal-ideal representation, used it to identify the comparator's supplied
ideal with the canonical denominator, assembled the two realization
certificates, and exported `silverman_proposition_2_1_certified`. The complete
four-target comparator is now configured. A second full check passed with 198
public declarations audited.

## Issue #101 resolved and merged — 2026-07-20 (`1cfbfc4`)

A full, unconditional existence result for every elliptic Weierstrass curve
over `ℚ` — not a partial slice. Applies mathlib's DVR minimal-model theorem
(`WeierstrassCurve.exists_isMinimal`) at each prime's valuation subring,
bridges to the project's `HeightOneSpectrum`-based valuation framework via
a `Valuation.IsEquiv` argument, bounds every local minimal exponent by a
single global integral model's discriminant multiplicities, and assembles
the bounded exponents into a genuine ideal via Dedekind-domain unique
factorization (`nonempty_globalMinimalDiscriminantData_rat`,
`globalMinimalDiscriminantDataRat`). Merged cleanly (main never touched
`Heights/Certificates.lean` in the interim). Independently re-verified with
a clean, uncontended build (no other pi processes running): 215
declarations audited, all clean. A mid-run report of a blocked full build
was a false alarm from cross-worktree `.lake` build-cache hardlink sharing
while main-line concurrently rewrote `Heights/IdealFactorization.lean` —
worth remembering for future concurrent-worktree setups (hardlink
`.lake/packages`, but prefer independent `.lake/build` per worktree, or at
minimum re-verify from a quiescent state before trusting a mid-flight
build failure). The general number-field case remains open as #56; the
"simultaneously minimal at every prime" fact used here is special to
class-number-one-style base rings. Taxis #101 closed.

## Milestone: certified Proposition 2.1 complete for K = ℚ, modulo one certificate — 2026-07-20

With #99, #100, and #101 all merged, `Heights.proposition_2_1_certified` and
`proposition_2_1_semistable_certified` hold **unconditionally for K = ℚ**:
`GlobalMinimalDiscriminantData ℚ W` is now always constructible
(`globalMinimalDiscriminantDataRat`), so the only remaining hypothesis for
`K = ℚ` is `ArchimedeanPeriodData ℚ W` (#57 — the complex-uniformization
bridge from `WeierstrassCurve.j` to the modular `j`-function; nothing else
is missing). For general number fields, both `GlobalMinimalDiscriminantData`
(#56) and `ArchimedeanPeriodData` (#57) remain open. Every other
mathematical ingredient of Silverman's Proposition 2.1 — the finite-place
Weil-height identity, the archimedean modular fundamental-domain estimates,
equation (11), the `ε`-absorption bound, and the semistable specialization
— is now proved unconditionally with no realization-data hypotheses at all.

## Autonomous run 7 — 2026-07-20

Closed tooling issue #102 with `d18ecb3`: CI now parses every Verso
`lean :=` annotation, elaborates all linked declaration names under
`import Heights`, and runs a negative fixture proving a nonexistent link is
rejected. The full bounded build and trust/axiom audits passed.

Investigated #57 rather than forcing a uniformization construction. Commit
`d232a6e` proves `modularJ_smul`, reduces fundamental-domain preimages to
surjectivity, and proves
`nonempty_archimedeanPeriodData_of_modularJ_surjective`. Thus the exact
minimum blocker for the current certificate interface is now the honest
analytic theorem `Function.Surjective Heights.modularJ`; no period or
uniformization existence is claimed. The detailed source survey and
**STOP-as-phase-sized / GO-as-decomposed-mathlib-project** judgment are in
`Plans/ArchimedeanUniformizationFeasibility.md`. The spec's P0–P9 table,
Blueprint, and umbrella documentation were updated to the actual milestone.
Filed ready-to-clanck #128 (modular-`j` surjectivity, the minimal route) and
#129 (identify `PeriodPair.G` with `E₄/E₆`, the first genuine geometric route
slice). Full CI passed with 227 public declarations audited and only
`propext`, `Quot.sound`, and `Classical.choice`.

## Autonomous run 8 — 2026-07-20

Closed #129 with `72449c6`. The new focused module
`Heights/LatticeEisenstein.lean` constructs the period pair `(τ, 1)`, transports
`PeriodPair.G` through `latticeEquivProd` to mathlib's full integer-pair
Eisenstein sum, and proves the exact normalizations
`G₄ = π⁴ E₄ / 45` and `G₆ = 2 π⁶ E₆ / 945`. It also derives
`g₂ = 4 π⁴ E₄ / 3`, `g₃ = 8 π⁶ E₆ / 27`, and
`g₂³ - 27 g₃² = 4096 π¹² Δ`, including nonvanishing. This is the completed
first slice of #57 Route B, not a quotient-torus or arbitrary-curve
uniformization theorem.

Updated the Blueprint, feasibility report, and spec to record the result and
filed ready-to-clanck #137 for the next independent slice: construct the short
lattice Weierstrass curve and identify its algebraic `j` with `modularJ`.
The minimal Route A blocker remains #128 (surjectivity of `modularJ`). Full CI
passed with 239 declarations audited and only `propext`, `Quot.sound`, and
`Classical.choice`.

## Autonomous run 9 — 2026-07-20

Completed #137, the second explicit slice of #57 Route B. The new focused
module `Heights/LatticeWeierstrass.lean` defines the short Weierstrass curve
`y² = x³ - g₂x/4 - g₃/4` attached to `(τ, 1)`. Mathlib's differential equation
for `℘` proves `(℘(z), ℘'(z)/2)` lies on its affine equation away from the
lattice. Direct invariant calculations give `c₄ = 12g₂` and
`Δ_W = g₂³ - 27g₃² = 4096π¹²Δ(τ)`, yielding an honest
`WeierstrassCurve.IsElliptic` instance and the exact identity
`WeierstrassCurve.j = Heights.modularJ τ`.

The Blueprint and feasibility report now mark Route B steps 1 and 2 complete.
No quotient-torus descent, projective extension at lattice points, group-law
compatibility, arbitrary-curve uniformization, or modular-`j` surjectivity is
claimed; those remain the substantial Route B / Route A gaps. Full
`LAKE_JOBS=6 ./scripts/ci-checks.sh` passed with 259 declarations audited and
only `propext`, `Quot.sound`, and `Classical.choice`. Filed ready-to-clanck
#138 for the next independent Route B slice: package the off-lattice affine
`(℘,℘′/2)` point and prove its invariance under lattice translation, without
yet claiming a quotient descent or projective extension.

## Autonomous run 15 — 2026-07-20

Completed #152, the pole-free continuity slice of #57 Route B. The new module
`Heights/LatticeAffinePointTopology.lean` factors the existing affine point map
through the explicit affine equation locus and its open embedding into
`LatticeCurvePoint τ`. Mathlib's differentiability theorems for `℘` and `℘′`
away from the period lattice prove continuity of both the coordinate-valued
map and the wrapped curve-point map on `LatticeComplement τ`.

Commit `0a24904` recorded the precise pole-free boundary and passed full CI
with 317 declarations audited. The same run then filed and completed #153 in
`Heights/LatticePointMapTopology.lean`: `PeriodPair.order_weierstrassP` makes
`℘` leave every compact set near a lattice point, and projecting any compact
subset of the affine curve to its first coordinate transfers this escape to
the affine point map. It therefore converges to infinity in the one-point
compactification. The total map `ℂ → LatticeCurvePoint τ` is continuous, and
the quotient-map criterion proves its descended map from `ℂ/L` continuous.
Analytic extension, group-law compatibility, bijectivity, and uniformization
are still not claimed.

The run also completed expository issue #103. Eleven Blueprint nodes now explain
the normalization choices and proof ideas behind absolute height, rational
height arithmetic, the modular discriminant and `j`, weighted Jensen, the five
realization/formula interfaces, and their exact honesty boundaries. No private
reference text was reproduced; the prose summarizes the mathematics in the
repository's own words. Full CI remained clean with 326 declarations audited.

Finally, #154 packages compactness of the source quotient. The continuous
projection `ℂ → ℂ/L` is periodic under the full `ℤ`-lattice, so
`IsZLattice.isCompact_range_of_periodic` makes its range compact; quotient
surjectivity identifies that range with the whole space. This adds no
injectivity, group-law, analyticity, or uniformization claim.

## Autonomous run 16 — 2026-07-20

Closed the general finite-place realization project #56. Commit `f35c342`
generalizes the rational denominator-clearing argument: localization supplies a
denominator for each Weierstrass coefficient, their product gives one nonzero
algebraic integer, and a scaling change clears the weighted denominators
simultaneously over `𝓞 K`. The resulting global integral model bounds every
chosen local minimal discriminant exponent. Dedekind ideal factorization then
assembles those bounded exponents into `GlobalMinimalDiscriminantData K W` for
every number field, via `nonempty_globalMinimalDiscriminantData` and the chosen
`globalMinimalDiscriminantData`.

Commit `bda6210` consumes the construction in the headline chain.
`silvermanHeightOfPeriods`, `unstableMinimalDiscriminantOfCurve`, and
`proposition_2_1_of_periods` instantiate the previous certificate-level theorem
with the constructed finite data; the semistable specialization is instantiated
as well. Thus `ArchimedeanPeriodData K W` is now the sole remaining realization
input over every number field, not only over `ℚ`. This is still a formula-defined
Silverman height and does not claim an Arakelov/Hodge-bundle Faltings-height
identification or unconditional period existence.

The Blueprint, specification, feasibility report, and root documentation now
record the completed arithmetic branch. Full `LAKE_JOBS=6
./scripts/ci-checks.sh` passes with 344 public declarations audited, all within
`{propext, Quot.sound, Classical.choice}`. Taxis #56 was closed; #128/#57 remain
the hard archimedean front.

The run also landed the first genuine algebraic compatibility of the explicit
uniformization map in `3162f06`. `LatticePointMapNegation.lean` uses evenness of
`℘` and oddness of `℘′` to prove that the total and descended maps preserve zero
and negation. It deliberately does not package a group homomorphism: the
addition theorem remains open and was filed as standalone ready-to-clanck issue
#155. CI passes with 349 audited declarations after this slice.

## Autonomous run 17 — 2026-07-20

The first addition-theorem prerequisite is now formalized in
`Heights/WeierstrassDifferential.lean`. Differentiating mathlib's cubic
Weierstrass relation initially gives the desired second-order equation times
`℘′`. Rather than divide pointwise and lose the ramification points, the proof
uses analytic no-zero-divisors on the connected lattice complement. The
alternative that `℘′` vanishes identically would make `℘` constant there and
contradicts its order-two pole. Thus `Heights.deriv_derivWeierstrassP` proves
`℘′′ = 6℘² - g₂/2` at every non-lattice point.

The ODE has also yielded the exact fiber theorem, rather than only an addition-
theorem prerequisite. `Heights/WeierstrassFibers.lean` packages `(℘,℘′)` as a
real locally Lipschitz first-order system. ODE uniqueness gives equality on a
real interval; the complex identity theorem globalizes it off the translated
lattices; and the order-two pole forces the translation difference to be a
period. Thus `℘(z)=℘(w)` iff `z≡±w (mod L)`, while `(℘,℘′)` separates classes
modulo `L`.

`Heights/LatticePointMapInjectivity.lean` consumes this result to prove
`latticePointMap_eq_iff_sub_mem` and
`latticeQuotientPointMap_injective`. Together with compactness, Hausdorffness,
and continuity, `isClosedEmbedding_latticeQuotientCurvePointMap` packages the
descent as a closed topological embedding. This completes the injective half of
the explicit set-theoretic parameterization. It remains an honest intermediate
result toward #155, not the Weierstrass addition formula: addition
compatibility, the group-homomorphism package, surjectivity, and uniformization
remain open. The now-separable surjectivity half of the explicit quotient map
was filed as ready-to-clanck #159.

## Autonomous run 18 — 2026-07-21

The explicit lattice-curve surjectivity gap #159 is now solved in
`Heights/WeierstrassSurjectivity.lean`. For any proposed omitted value `a`, the
proof extends `1/(℘-a)` by zero at the period lattice. The order-two pole theorem
makes this extension analytic at every lattice point; away from the lattice the
omitted-value assumption makes the reciprocal analytic. Periodicity and
mathlib's compact-range theorem make the entire function bounded, so
Liouville's theorem makes it constant, contradicting its zero value at the
lattice and nonzero value at a half-period. Thus `℘` attains every complex
value away from its poles.

The short Weierstrass equation then shows that every affine curve point occurs:
a preimage of its `x`-coordinate has derivative sign `2y` or `-2y`, and
negating the parameter handles the second case. Consequently the total and
descended lattice point maps are surjective. Combined with run 17's
injectivity, continuity, compact source, and Hausdorff target, the descended
map is packaged as `latticeQuotientCurvePointHomeomorph : ℂ/L ≃ₜ Eτ(ℂ)`.
This is an honest topological uniformization of the explicit lattice curve,
not yet an analytic equivalence or group isomorphism. Addition compatibility
remains #155, while arbitrary-curve uniformization and modular-`j` surjectivity
(#128) remain open.

## Autonomous run 19 — 2026-07-21

Run 19 advances #155 without claiming the missing global addition theorem.
`Heights/WeierstrassPrincipalPart.lean` extracts the exact local pole data from
mathlib's omitted-summand power series.  It proves that the regular parts
`℘(z)-z⁻²` and `℘′(z)+2z⁻³` tend to zero, and hence that at every lattice point
`l` the normalized functions `(z-l)²℘(z)` and `(z-l)³℘′(z)` tend to `1` and
`-2`, respectively.

The same file proves the first removable-singularity calculation for the
addition law: for arbitrary constants `a,b`, the secant `x`-coordinate
candidate `((℘′(z)-b)/(2(℘(z)-a)))²-℘(z)-a` tends to `a` as `z→0`.  This is the
correct local behavior for adding the point at infinity to `(a,b/2)`.  It is
not yet equality with `℘(z+w)`, does not establish the corresponding
`y`-coordinate limit, and therefore does not close #155 or package a group
homomorphism.  The feasibility report and Blueprint now expose this exact
boundary.

## Autonomous run 20 — 2026-07-21

Run 20 completed the second removable coordinate calculation in
`Heights/WeierstrassPrincipalPart.lean`. The stronger estimate
`(℘(z)-z⁻²)/z → 0` controls the cancellation left after the leading poles are
removed, and the secant-law `y`-candidate now tends to `b/2` at the origin.
Together with run 19, both secant coordinates have the correct limit when one
summand approaches infinity. No equality with the coordinates at `z+w` was
claimed.

## Autonomous run 21 — 2026-07-21

`Heights/WeierstrassAdditionDifferential.lean` names the secant slope and its
two coordinate candidates and proves the next local analytic step. Whenever
`b² = 4a³ - g₂a - g₃`, direct differentiation away from the lattice and
vertical secants gives `s′ = ℘ - X`, `X′ = 2Y`, and
`Y′ = 3X² - g₂/4`. Thus `(X,2Y)` satisfies exactly the same polynomial
first-order ODE as `(℘,℘′)`.

The same module installs the limiting values `a` and `b/2` at zero and applies
Riemann's removable-singularity theorem, proving that both extended candidates
are analytic there. This is genuine progress toward #155, but not the addition
theorem: ODE uniqueness has not yet identified the candidates locally with
`(℘(z+w),℘′(z+w)/2)`, and no identity theorem has globalized that comparison.
Consequently the point map is still not claimed to preserve addition or
packaged as a group isomorphism.

## Autonomous run 22 — 2026-07-21

Run 22 closes #155. `Heights/WeierstrassAddition.lean` proves the local
addition identity by real ODE uniqueness and the complex identity principle,
then globalizes it on the connected complement of a countable exceptional set.
The resulting theorem identifies both secant coordinates with
`(℘(z+w), ℘′(z+w)/2)` whenever the secant is nonvertical.

`Heights/LatticePointMapAddition.lean` matches those coordinates with
mathlib's affine elliptic-curve addition. For doubling, it chooses an auxiliary
parameter outside a countable union of lattice translates and reduces the
tangent case to three already-proved nonvertical secants. Pole, inverse, and
period cases are then handled separately. The total point map preserves every
addition, and the bijective descended map is packaged as
`latticeQuotientPointMapAddEquiv : ℂ/L ≃+ Eτ(ℂ)`. This is a genuine additive
uniformization of the explicit lattice curve, not a claim of an analytic
Lie-group equivalence or arbitrary-curve uniformization. Full CI, trust, axiom,
and Blueprint checks pass with 430 audited declarations.

## Autonomous run 23 — 2026-07-21

Run 23 closes the weak archimedean realization gap #128/#57 without a valence
theorem or modular-curve compactification. `Heights/ModularJ.lean` first proves
that `‖modularJ τ‖ → ∞` at the cusp from the existing scaled `q`-asymptotic.
The complex open mapping theorem then makes the nonconstant holomorphic image
open. To prove it closed, a convergent sequence of values is lifted and moved
into the standard fundamental domain; cusp growth bounds the imaginary parts,
and compactness of the corresponding truncated fundamental domain supplies a
convergent subsequence of preimages. Connectedness of `ℂ` gives
`Heights.modularJ_surjective`.

`Heights.nonempty_archimedeanPeriodData` now constructs the deliberately weak
`j`-compatible data for every elliptic curve over a number field. This is not a
claim that the selected parameters arise by integrating a differential on the
input curve. `silvermanHeightOfCurve`, `proposition_2_1`, and
`proposition_2_1_semistable` instantiate both formula-level data interfaces,
while explicitly retaining the honesty boundary: no independently constructed
Arakelov Faltings height or arbitrary-curve analytic uniformization is claimed.
Full CI, trust, axiom, comparator, and Blueprint checks pass with 441 audited
declarations. Filed ready-to-clanck #173 for the now-separable canonicality
question: prove the formula is independent of the weak period-data choice.

## Autonomous run 24 — 2026-07-21

Run 24 resolves #173 without assuming orbit equivalence. A reciprocal-coordinate
ODE at the pole proves that `g₂` and `g₃` determine a period lattice. Equality
of modular `j` gives an algebraic variable change between the two explicit
lattice curves; its `c₄` and `c₆` transformation laws therefore identify the
lattices up to homothety. Comparing their two integral bases and using positivity
of the upper-half-plane imaginary parts constructs an actual `SL(2, ℤ)` element,
proving `Heights.exists_smul_eq_of_modularJ_eq`.

The weight-twelve discriminant law and imaginary-part transformation then show
that `‖silvermanModularDiscriminant τ‖ * τ.im ^ 6` depends only on `modularJ τ`.
Consequently `silvermanHeight_periodData_independent` proves equality for any
two qualifying `ArchimedeanPeriodData` values, and every such value agrees with
`silvermanHeightOfCurve`. This makes the formula canonical. At the end of run
24 the remaining caveat was stated as absence of genuine periods; run 25
sharpens that boundary below.

## Autonomous run 25 — 2026-07-21

Run 25 confirms that the recurring complex-twist caveat was too strong.
For every `p : ArchimedeanPeriodData K W` and infinite place `v`, the equality
`p.j_eq v`, `latticeWeierstrassCurve_j`, and mathlib's
`WeierstrassCurve.exists_variableChange_of_j_eq` over the separably closed
field `ℂ` produce an actual admissible variable change

`C • W.map v.embedding = latticeWeierstrassCurve (p.τ v)`.

`Heights/ArchimedeanAlgebraicRealization.lean` proves this existence theorem,
fixes a chosen change, and records its equation equality. It also proves the
exact `u³` scaling of `2y + a₁x + a₃` and the resulting exact `u⁻¹` scaling of
the rational invariant-differential coefficient. Thus the
selected lattice genuinely algebraically realizes the specified complex base
change, and twists do not remain over `ℂ`.

The sharpened honesty boundary is now point-level analytic rather than
algebraic: mathlib has no variable-change equivalence/additive equivalence on
`Affine.Point`, no invariant holomorphic differential and integration package
for an arbitrary Weierstrass curve, and no Arakelov/Hodge metric. The result
therefore still does not identify `silvermanHeightOfCurve` with an independently
constructed Faltings height. Filed ready-to-clanck #174 for the separable
point-level variable-change equivalence and additive compatibility.

## Autonomous run 26 — 2026-07-21

Run 26 completes #174 in `Heights/VariableChangePoint.lean`. For an admissible
change `C`, the file proves the exact transformed equation, explicit forward
and inverse coordinate identities, negation and secant/tangent slope formulas,
and transformed addition coordinates. These package the documented coordinate
map as

`C.pointAddEquiv W : (C • W).toAffine.Point ≃+ W.toAffine.Point`.

The additivity proof covers vertical, secant, and tangent cases against
mathlib's actual affine group law; it is not merely a transported operation.
Specializing to the chosen same-`j` change gives
`ArchimedeanPeriodData.latticeCurvePointAddEquiv`, and composing with the
already-proved explicit lattice equivalence gives

`LatticeQuotient (p.τ v) ≃+ (W.map v.embedding).toAffine.Point`.

Thus arbitrary embedded input curves now have an honest algebraic additive
uniformization at the point-type level. The target has not been given a
topology, the equivalence is not claimed continuous or analytic, and no
invariant differential has been defined or integrated. Those remain the exact
boundary before an Arakelov/Faltings interpretation.

## Autonomous run 27 — 2026-07-21 (`4177aff`)

Performed a focused feasibility review of the one genuinely analytic statement
left after #174. `Plans/AnalyticPeriodFeasibility.md` separates the already
proved algebraic/additive uniformization from the missing intrinsic
complex-manifold atlas, global invariant holomorphic differential, analyticity
of the existing maps, and integration/covering-space computation of all
periods. It records the expected normalization precisely: the chosen variable
change should pull the embedded invariant differential back to `u⁻¹ dz`, so
the periods should be `u⁻¹` and `u⁻¹τ` and their ratio should be the selected
`τ`. Transporting the analytic structure and form tautologically along the
existing equivalence is explicitly not accepted as an intrinsic realization.

Landed one concrete first step:
`isAddQuotientCoveringMap_latticeQuotientMk` and
`isCoveringMap_latticeQuotientMk` package `ℂ → ℂ/L` as the quotient covering
map for translation by the discrete period lattice. Updated the feasibility
report, specification, and Blueprint to remove stale pre-#174 claims and link
the new declarations. Full `LAKE_JOBS=6 ./scripts/ci-checks.sh` passes; 616
public declarations use only the permitted axiom subset.

Filed and labeled `ready-to-clanck` two deduplicated standalone slices: #175
(complex-manifold structure on the source lattice quotient) and #176 (intrinsic
one-point-compactification topology for arbitrary complex Weierstrass point
types and variable-change homeomorphisms). Posted the narrowed feasibility
judgment to umbrella issue #57. The analytic-period frontier is GO only as this
decomposed infrastructure project; an Arakelov/Faltings identification remains
a further, larger layer.

## Autonomous run 28 — 2026-07-21

Audited the mature specification, Blueprint, and comparator against the current
all-curves formula-defined theorem. Removed stale phase-gate and pre-additive-
uniformization wording, made the Proposition 1.1 boundary explicit, and updated
the recorded source layout. The comparator now also exercises modular `j`
surjectivity and canonicity of the Petersson-normalized discriminant metric,
the two P8/P9 facts responsible for existence and choice-independence of
`silvermanHeightOfCurve`.

Added `scripts/audit_comparator.sh` and a negative fixture so CI rejects a
configured theorem absent from the challenge or a solution theorem list that
differs from the config. All six challenge targets retain exactly one reviewed
proof placeholder, while their solution exports compile and pass the public
axiom audit. Full `LAKE_JOBS=6 ./scripts/ci-checks.sh` passes; 618 public
declarations use only `propext`, `Quot.sound`, and `Classical.choice`. No
analytic-period or Arakelov claim was added.
