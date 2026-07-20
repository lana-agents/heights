# Archimedean period realization feasibility report

**Date:** 2026-07-20  
**Scope:** taxis #57; `ArchimedeanPeriodData` in
`Heights/Certificates.lean`; mathlib `v4.32.0`  
**Decision:** **STOP as a phase-sized implementation; GO only as a decomposed
mathlib-scale project.**

## 1. The exact blocker is smaller than full uniformization

The current certificate contains only a fundamental-domain point and an
identity of `j`-invariants:

```lean
structure ArchimedeanPeriodData ... where
  τ : InfinitePlace K → ℍ
  mem_fd : ∀ v, τ v ∈ ModularGroup.fd
  j_eq : ∀ v, v.embedding W.j = modularJ (τ v)
```

Consequently, the minimum theorem needed to instantiate this interface is

```lean
Function.Surjective Heights.modularJ
```

rather than an explicit equivalence between the points of `W` and a complex
torus. This run proved the reduction, but not surjectivity:

* `Heights.modularJ_smul` proves invariance under `SL(2, ℤ)`.
* `Heights.exists_mem_fd_modularJ_eq_of_surjective` moves any preimage into
  `ModularGroup.fd`.
* `Heights.nonempty_archimedeanPeriodData_of_modularJ_surjective` chooses such
  a preimage at every infinite place.

This is an interface-level reduction only. It does **not** prove that the
chosen `τ` is a period ratio obtained by integrating a differential on `W`,
does not construct `W(ℂ) ≃ ℂ/L`, and does not identify the formula-defined
`silvermanHeight` with an Arakelov/Hodge-bundle Faltings height.

## 2. What mathlib already supplies

### Lattices and Weierstrass functions

`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` has:

* `PeriodPair`, a pair of real-linearly independent complex periods;
* `PeriodPair.lattice`, its rank-two `ℤ`-submodule, together with
  `latticeBasis` and `latticeEquivProd`;
* the meromorphic functions `weierstrassP` and `derivWeierstrassP`, their
  periodicity and parity, and the pole-order theorem `order_weierstrassP`;
* lattice Eisenstein sums `PeriodPair.G`, invariants `g₂ = 60 G 4` and
  `g₃ = 140 G 6`; and
* `PeriodPair.derivWeierstrassP_sq`, the differential equation
  `℘'(z)^2 = 4℘(z)^3 - g₂℘(z) - g₃` away from the lattice.

A compile-checked scratch prototype constructed a `PeriodPair` from every
`τ : ℍ` using the pair `(1, τ)`; real linear independence follows immediately
by taking imaginary parts and using `τ.im_pos`. Thus the direction
`τ → lattice` is routine with the present API.

The file itself marked the next bridge precisely: the docstring for
`PeriodPair.G` says `TODO: Establish connections with the ModularForm
library.` This repository now supplies that bridge in
`Heights/LatticeEisenstein.lean`. For the basis `(τ, 1)`, it proves
`G 4 = π ^ 4 / 45 * E₄ τ`, `G 6 = 2 * π ^ 6 / 945 * E₆ τ`, the corresponding
`g₂`/`g₃` identities, and
`g₂ ^ 3 - 27 * g₃ ^ 2 = 4096 * π ^ 12 * discriminant τ`; hence the lattice
discriminant is nonzero. These lattice-sum normalization results feed the explicit construction in
`Heights/LatticeWeierstrass.lean`.  That file defines
`y² = x³ - g₂x/4 - g₃/4`, proves `(℘(z), ℘'(z)/2)` satisfies the affine
equation away from the lattice, computes its algebraic discriminant as
`g₂³ - 27g₃²`, instantiates `WeierstrassCurve.IsElliptic`, and identifies its
algebraic `j` with `Heights.modularJ τ`.  The next pole-free slice is also now
formalized in `Heights/LatticeAffinePoint.lean`: the coordinate pair is
packaged as an actual affine elliptic-curve point on `ℂ \ L`, translation by a
lattice element is proved to preserve that domain, and periodicity of `℘` and
`℘′` proves invariance of the point map.  The successor module
`Heights/LatticeQuotientPoint.lean` now sends every lattice element to the
point at infinity, proves invariance of this total map, and descends it as a
function on the additive quotient `ℂ/L`.  The source quotient is now equipped
with its standard topological-additive-group structure in
`Heights/LatticeQuotientTopology.lean`: the canonical projection is proved
continuous, open, and a quotient map, and closedness of the period lattice
gives a `T1Space`.  The target of the descended map now also has a conservative,
explicit-curve-only topology in `Heights/LatticeCurveTopology.lean`: a named
wrapper around the lattice-curve point type is homeomorphic to the one-point
compactification of its affine equation locus.  The affine Weierstrass equation
is proved to cut out a closed, locally compact subspace of `ℂ × ℂ`; therefore
the wrapper is compact and `T4` (in particular Hausdorff and regular), and the
affine chart is an open embedding.  Finally,
`Heights/LatticeAffinePointTopology.lean` factors the pole-free point map
through that affine chart and proves it continuous from the complement of the
lattice, using differentiability of `℘` and `℘′`.  This does not establish the
limit at a lattice point or continuity of the total/descended point map there;
analytic extension across infinity, group-law compatibility, bijectivity,
complex-torus equivalence, and arbitrary-curve uniformization have not been
proved.

### Modular forms and the fundamental domain

The needed analytic functions and transformation theory are present:

* `ModularForm.E₄`, `ModularForm.E₆`, and
  `ModularForm.discriminant`;
* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` and nonvanishing of
  the discriminant on `ℍ`;
* q-expansions and cusp asymptotics; and
* `ModularGroup.exists_smul_mem_fd`.

The lattice/modular-series proof uses
`EisensteinSeries.tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries` to
express the full sum over integer pairs as a zeta factor times the primitive
Eisenstein series. `riemannZeta_four` gives the weight-four constant, and
`riemannZeta_two_mul_nat` specializes to weight six. Transport through
`PeriodPair.latticeEquivProd` identifies that integer-pair sum with
`PeriodPair.G` for the lattice generated by `(τ, 1)`.

The level-one dimension and Sturm-bound files control q-expansions. They do
not provide a valence formula, a compactified modular curve, or a theorem that
`E₄^3 / Δ` is onto `ℂ`. A source search also found no Rouché theorem or
argument-principle API already specialized enough to turn the cusp expansion
into this surjectivity statement.

### Algebraic elliptic curves

The algebraic side is comparatively strong:

* `WeierstrassCurve.j` and its change-of-variables invariance are present;
* `WeierstrassCurve.ofJ` constructs a curve with any prescribed algebraic
  `j`-invariant; and
* `WeierstrassCurve.exists_variableChange_of_j_eq` proves over a separably
  closed field that elliptic Weierstrass curves with equal `j` are related by
  a variable change.

The required nonsingular lattice curve with the correct modular `j` is now
constructed in `Heights/LatticeWeierstrass.lean`.  Consequently these
classification results are available for a later converse argument, but they
still do not produce a lattice from an arbitrary algebraic curve or prove
modular-`j` surjectivity.

## 3. Concrete missing theorem stack

There are two honest routes.

### Route A: discharge the current certificate only

1. Prove `Function.Surjective Heights.modularJ`.
2. Apply the three reduction theorems listed in §1.

Step 1 is still substantial. Plausible proofs require either a valence theorem
for level-one modular forms / compactification of the modular quotient, or a
new complex-analysis argument from the q-expansion (for example an
argument-principle or Rouché-style proof). The pinned library has components
for holomorphic and meromorphic functions, but not the assembled modular-curve
result.

### Route B: genuine complex uniformization

1. **Completed in `Heights/LatticeEisenstein.lean`:** package the lattice
   generated by `(τ, 1)` and prove the exact `PeriodPair.G 4`, `PeriodPair.G 6`,
   `g₂`, `g₃`, and lattice-discriminant normalizations.
2. **Completed in `Heights/LatticeWeierstrass.lean`:** define the short
   Weierstrass curve from `g₂,g₃`; prove that `(℘,℘'/2)` satisfies its affine
   equation away from the lattice, that its discriminant is nonzero, and that
   its algebraic `j` is `Heights.modularJ τ`.
3. **Partially completed in `Heights/LatticeAffinePoint.lean`,
   `Heights/LatticeQuotientPoint.lean`,
   `Heights/LatticeQuotientTopology.lean`,
   `Heights/LatticeCurveTopology.lean`, and
   `Heights/LatticeAffinePointTopology.lean`:** package `(℘(z),℘'(z)/2)` as an
   affine point away from the lattice, extend it at lattice points by the
   point at infinity, prove invariance of the total map under lattice
   translation, descend it set-theoretically through the additive quotient
   `ℂ/L`, package the quotient's standard topology (including continuity,
   openness, and quotient-map status of `ℂ → ℂ/L`, and its `T1` separation),
   and transport the one-point-compactification topology to a named wrapper of
   the explicit curve-point target.  The affine equation locus is closed and
   locally compact, so the target wrapper is compact and `T4` (hence Hausdorff
   and regular), and its affine chart is an open embedding.  The pole-free
   point map is continuous into that chart.  Still missing: prove its limit at
   every lattice point and hence continuity of the total and descended maps,
   then prove analytic extension, group-law compatibility, bijectivity, and
   analyticity of the descended map.
4. In the converse direction, obtain a lattice from an arbitrary algebraic
   complex elliptic curve (normally via periods of a holomorphic differential
   or an inverse elliptic integral), then identify the resulting curve using
   the same-`j` theorem.

Mathlib has generic quotient-group infrastructure, but the pinned elliptic
files contain no complex-torus object carrying the required analytic/group
structure and no descended `℘` equivalence. Steps 3 and 4 therefore require
major new infrastructure, not glue code.

## 4. Judgment

**STOP** for a single heights phase/run. Even after completing the explicit
lattice curve, invariant computation, total point map, and set-theoretic
quotient descent, neither modular-`j` surjectivity nor full algebraic/analytic
uniformization is currently a phase-sized consequence of the pinned APIs. Attempting to manufacture `ArchimedeanPeriodData` from a
stronger assumption that already supplies the desired `τ`, or adding an
isomorphism as an unproved structure field, would merely move the gap and is
not acceptable.

**GO** only if #57 is treated as a decomposed mathlib-scale project. Route A is
the shortest path to the repository's present headline theorem; Route B is the
right long-term path if “period data” is to carry its full geometric meaning
and if the formula-defined height is eventually to be related to a genuine
Faltings height. The source quotient topology, a conservative compact
Hausdorff one-point-compactification topology on the explicit target, and
continuity on its pole-free affine chart are now available, but they do not
resolve continuity at the pole, analytic extension, or the uniformization gap. Until one route lands, the unconditional
`K = ℚ` result correctly retains `ArchimedeanPeriodData ℚ W` as its sole
remaining certificate.
