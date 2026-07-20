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
