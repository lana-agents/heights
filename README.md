# heights

Lean 4 / Mathlib (`v4.32.0`) formalization of heights on elliptic curves and on curves over
number fields. It started as Silverman's comparison of the Weil height of `j` with the
elliptic-curve height (J. H. Silverman, "Heights and Elliptic Curves", Ch. X of
Cornell–Silverman, *Arithmetic Geometry*, 1986, Prop. 2.1). It now also contains the height
machine on curves and the conductor/different bounds of Mochizuki's *Arithmetic elliptic curves
in general position* ([GenEll], §1–2), and two isogeny estimates. These are used by the IUT/ABC
programme ([`lana-agents/iut`](https://github.com/lana-agents/iut)) and by the
[`lana-agents/genl`](https://github.com/lana-agents/genl) fork.

No `sorry`, `admit` or `axiom` occurs in `Heights/` (checked with `git grep`). The only `sorry`s
in the repository are the six reviewed placeholders in `Comparator/Challenge.lean`, which is the
statement side of the comparator harness and is listed in `scripts/trust-exceptions.tsv`.
`scripts/ci-checks.sh` runs the build, the trust audit and the axiom audit (`propext`,
`Quot.sound`, `Classical.choice` only).

## Main results

### Silverman, Proposition 2.1 (formula-defined height)

* `Heights.proposition_2_1`, `Heights.proposition_2_1_semistable`
  (`Heights/IdealFactorization.lean`). There is a constant `C ≥ 0` such that for every number
  field `K` and every elliptic curve `W/K`,
  `h(j) + log N(γ)/[K:ℚ] − 12 h(W)` lies in `[−C, 6 log(1 + h(j)) + C]`, and its absolute value
  is at most `6 log(1 + h(j)) + C` for semistable `W`. These are proved with no hypotheses.
* Here `h(W)` is `Heights.silvermanHeightOfCurve` (`Heights/SilvermanHeight.lean`). It is
  defined by Silverman's formula (Prop. 1.1): the minimal discriminant plus the archimedean
  term `|Δ(τ_v)| (Im τ_v)^6`, with `τ_v` chosen by `Heights.modularJ_surjective`. The
  definition does not depend on that choice.
* There are also certificate-level versions: `proposition_2_1_certified`,
  `proposition_2_1_of_periods`, and versions that take the modular estimates as arguments.
* **Not claimed:** `silvermanHeightOfCurve` is not identified with an Arakelov/Faltings height.
  Period integration, the Hodge metric and analyticity of the explicit uniformization for the
  intrinsic manifold structure are open (`Plans/AnalyticPeriodFeasibility.md`, taxis #180,
  #181).
* Supporting analytic work, all proved:
  * `modularJ` and the fundamental-domain estimates (`Heights/ModularJ.lean`).
  * The lattice-quotient uniformization of the explicit lattice curve.
  * Same-`j` classification over `ℂ`, which gives an actual variable change to the embedded
    curve.
  * The compact complex-manifold structure `complexWeierstrassPointIsManifold` on every
    nonsingular complex Weierstrass curve.

### Height machine on curves over number fields ([GenEll] §1)

These results live in `Heights/Curve/`, over the function fields `Belyi.CurveField` from
[`lana-agents/belyi`](https://github.com/lana-agents/belyi), and are all proved:

* Heights of tuples, `Heights.Curve.tupleHeight`. Comparison `A_s ≤ A_t ⇒ h_s ≲ h_t` is
  `tupleHeight_le_of_minOrd_le`, and invariance under linear equivalence is
  `abs_tupleHeight_sub_sub_le` (Prop. 1.4).
* Heights of divisors, `Heights.Curve.divHeight`: additivity, linear equivalence and positivity
  (`divHeight_add`, `divHeight_add_div`, `divHeight_bddBelow`, …), and functoriality under
  finite maps (`divHeight_pullback`).
* The log-different `Heights.Curve.logDiff` and the log-conductor `Heights.Curve.logCondOf`
  (Def. 1.5). Model independence is `logCondOf_le_logCondOf_add` (Rem. 1.5.1).
* Prop. 1.6, `log-cond ≲ height`: `logCondOf_le_tupleHeight_sub`, and for effective divisors
  `logCondOf_le_divHeight`.
* The compactness argument of [GenEll] Thm. 2.1, `Heights.Curve.exists_subseq_bounded`.

### Differents, conductors and discriminants (number-field core of [GenEll] Prop. 1.7)

These are in `Heights/Different/` and are all proved:

* Bounds on the different (Serre's bound, tame and unramified criteria).
* Log-conductors `Heights.Different.cond` along extensions: `cond_le_cond_add`,
  `logDisc_add_cond_le`.
* Kummer–Fermat extensions `F(c^{1/N}, (1−c)^{1/N})`:
  `logDisc_le_logDisc_add_cond_add` (and `_of_adjoin`), with the explicit constant
  `kummerConst N`. `Heights.Curve.logDisc_le_of_eq_adjoin` gives the version for subfields
  of `ℚ̄`.

### Other results

* Absolute heights on `ℚ̄` (`Heights/Absolute/`): `logHeight_one_eq_gen`, and Northcott
  over `ℚ̄`, `Heights.Absolute.finite_setOf_finrank_le_logHeight_le`.
* From bounds at embeddings to bounds at places (`Heights/Local/Bounded.lean`):
  `Heights.Local.abs_log_finitePlace_le`, `abs_log_infinitePlace_le`.
* Isogeny estimates for [GenEll] Lemma 3.5:
  * Vélu's product formula `Heights.Velu.prod_mul_sum_sub_sum` (`Heights/VeluProduct.lean`).
  * `x`-coordinates of `N`-torsion points over `ℂ` are `O(N²)`, with explicit dependence on
    `Δ` and `j`: `Heights.exists_torsion_x_bound` (`Heights/TorsionArchimedean.lean`).
  * No Faltings height and no quotient curve is constructed. The `iut` cyclic-subgroup bound
    uses these estimates instead of a Faltings-height argument.

## Use in the IUT/ABC programme

* `lana-agents/iut` pins this repository at `721496c` (its `lake-manifest.json`).
  * `Iut/Tripod/CyclicPoints.lean` and `CyclicArch.lean` use `Heights.Velu` and
    `Heights.exists_torsion_x_bound` for the cyclic-subgroup bound `Iut.Tripod.cyclicBoundOdd`.
  * `Iut/Tripod/GeneralPosition.lean` uses `Heights.Local.Bounded`.
  * `TorsionNewton.lean` uses `Heights.VariableChangePoint`.
  * `Heights.Curve.logDiff` is used for log-differents.
* The `lana-agents/genl` fork requires the same revision. Its genuine height theory of curves,
  `Genl.Curves`, is built on `Heights.Curve` and `Heights.Different`.

## Branches

`main` contains everything. The work branches `wp-height-theory`, `wp-height-theory-curve`,
`wp-isogeny` and `wp-integrate` are all merged into `main` (`721496c` is the `wp-integrate`
merge).

## Dependencies

* Mathlib `v4.32.0`.
* [`lana-agents/belyi`](https://github.com/lana-agents/belyi) at `9ce4d3f`, for
  `Belyi.CurveField` (curves over number fields as function fields, places, divisors,
  algebraic points).

## Documentation

* [`Plans/HeightsSpec.md`](Plans/HeightsSpec.md): specification and honesty boundary. The status
  table in §5 is authoritative for the Silverman part.
* [`Plans/HeightsWorkLog.md`](Plans/HeightsWorkLog.md): work log.
* [`Plans/AnalyticPeriodFeasibility.md`](Plans/AnalyticPeriodFeasibility.md): remaining analytic
  gates.
* `Comparator/`: comparator harness (see [`Comparator/README.md`](Comparator/README.md)).

## Building

```
lake exe cache get
lake build
LAKE_JOBS=6 ./scripts/ci-checks.sh   # build + trust and axiom audits
```

Copyrighted reference material (the Silverman chapter) is deliberately not in this repository.

Authors: Dagur Asgeirsson, Christian Merten.

License: Apache 2.0 (see LICENSE)
