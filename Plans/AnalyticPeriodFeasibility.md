# Analytic-period realization: focused feasibility assessment

**Date:** 2026-07-21  
**Scope:** the remaining analytic part of taxis #57 after main commit `be0167b`  
**Decision:** **GO only as a decomposed infrastructure project.** There is now a
concrete route, but the missing work is not one theorem and should not be
presented as a routine corollary of the algebraic uniformization.

## 1. What is already proved, and what “period” still means

For every infinite place `v`, `ArchimedeanPeriodData` chooses `τ v` in the
standard fundamental domain. The repository proves all of the following.

1. The explicit lattice curve attached to `τ v` is nonsingular and has the
   embedded algebraic `j`-invariant of `W`.
2. A chosen admissible variable change identifies that lattice equation with
   `W.map v.embedding`.
3. The Weierstrass point map gives both a homeomorphism and an additive
   equivalence from `ℂ / L(τ v)` to the explicit lattice curve.
4. The variable change gives an additive equivalence from the explicit lattice
   curve to the actual embedded point group of `W`.

Thus

```lean
ArchimedeanPeriodData.latticeQuotientToEmbeddedPointAddEquiv
```

is a genuine bijective additive-group uniformization of the given curve. The
remaining question is not whether some lattice curve in the same `j`-class
exists, whether a complex twist survives, or whether the group laws agree.
All three questions are closed.

The still-unproved analytic statement is stronger and independent: equip the
embedded curve with its **intrinsic** complex-analytic structure and invariant
holomorphic differential `ω_W`, prove the displayed algebraic equivalence is
biholomorphic for that structure, and prove that integrating `ω_W` around all
loops gives a lattice homothetic to `ℤ + ℤτ`. Merely transporting a manifold
structure and a differential from `ℂ/L` along the already-proved equivalence
would make this true by definition. That is useful as a model, but it would not
identify the transported objects with the curve's independently defined
analytic structure and invariant differential, so it is not an honest solution
to the remaining question.

## 2. The expected normalization is already determined algebraically

Let `C` be the chosen change for which

```lean
C • W.map v.embedding = latticeWeierstrassCurve (p.τ v).
```

Its coordinate map runs from the lattice curve to the embedded curve. The
proved coefficient identity says that the pullback of the usual rational
expression

\[
  \omega_W = \frac{dx}{2y+a_1x+a_3}
\]

has the expected scalar `C.u⁻¹` relative to the corresponding expression on
the lattice curve. On the pole-free Weierstrass parametrization,
`x = ℘(z)` and `y = ℘'(z)/2`, so formally the latter expression pulls back to

\[
  \frac{d\wp(z)}{\wp'(z)}=dz.
\]

Consequently the expected periods of `ω_W` are

\[
  C.u^{-1},\qquad C.u^{-1}\tau,
\]

and their ratio is exactly the already chosen `τ`. No further normalization
choice is hidden here. What is missing is making this calculation global at
ramification points and infinity, then connecting it to integrals of an
intrinsically defined form.

## 3. Pinned-mathlib feasibility findings

The following were checked against mathlib `v4.32.0`.

### 3.1 The source quotient has a concrete covering-space route

`Mathlib.Topology.Covering.Quotient` provides
`AddSubgroup.isAddQuotientCoveringMap_of_comm`; a `PeriodPair` lattice has a
discrete subtype. This run proves

```lean
isAddQuotientCoveringMap_latticeQuotientMk
isCoveringMap_latticeQuotientMk
```

in `Heights/LatticeQuotientTopology.lean`. Hence the canonical map
`ℂ → ℂ/L` is now packaged as a covering map, not only as a quotient map.
Mathlib also provides chart construction from a local homeomorphism via
`IsLocalHomeomorph.chartedSpace`, and quotient-action charted-space
infrastructure in `Mathlib.Geometry.Manifold.Instances.Quotient`.

The repository now closes the missing manifold step for this particular
translation action in `Heights/LatticeQuotientManifold.lean`. It constructs the
covering-local-inverse charts, proves their transitions are locally translations
by lattice elements, obtains a one-dimensional complex `IsManifold` instance,
and proves `latticeQuotientMk` is a local complex-analytic diffeomorphism. This
specialized proof is needed because mathlib's general quotient-manifold file
still lists the corresponding smoothness results as TODOs. Descending `dz` as
a bundled global one-form remains open.

### 3.2 Complex manifolds exist in mathlib, but not elliptic-curve manifolds

`Mathlib.Geometry.Manifold.Complex` supports holomorphic maps on a supplied
complex manifold. The pinned elliptic-curve API supplies no topology,
`ChartedSpace`, `IsManifold`, holomorphic atlas, cotangent line, or invariant
holomorphic differential for `WeierstrassCurve.toAffine.Point`.

The repository now closes the topology-only precursor: every nonsingular
complex Weierstrass equation has a named point wrapper with the
one-point-compactification topology of its affine equation locus, and every
admissible variable change is a homeomorphism for the independently
constructed source and target topologies. It also packages the forward and
inverse polynomial coordinate changes as a genuine ambient biholomorphism of
`ℂ × ℂ`, and proves that the affine-locus homeomorphism is its restriction.
Thus the affine analytic calculation for variable changes is complete, but
restriction to curve manifolds still requires their missing atlases. This
compact Hausdorff topology is enough for continuity, but it is not a complex
atlas. The natural target construction must therefore add independent charts:

* at a finite nonsingular point, use whichever partial derivative of the
  Weierstrass equation is nonzero and a complex implicit-function theorem;
* at infinity, use a projective/local parameter such as `-x/y` and prove the
  coordinate formulas extend holomorphically.

This is the largest foundational layer. The general compact Hausdorff wrapper
is now complete, but topology alone does not discharge it.

### 3.3 Integration exists in ambient normed spaces, not yet on manifolds here

`Mathlib.MeasureTheory.Integral.CurveIntegral.Basic` defines

```lean
curveIntegral (ω : E → E →L[𝕜] F) (γ : Path a b)
```

for paths in a normed vector space. It does not directly integrate a cotangent
field along a path in an arbitrary charted manifold. The complex analysis
library also has primitives and the fundamental theorem of calculus. These can
support local calculations, but there is no ready theorem saying that a global
holomorphic one-form on a complex elliptic curve has a period homomorphism on
its fundamental group.

This gap can probably be kept local to this project. Once the quotient is a
complex manifold and `dz` descends, covering-space path lifting can define or
compute integrals through lifts. To prove the **full** period lattice, not only
two sample integrals, one must show every lifted loop ends at a lattice
translate and that every lattice translate occurs. Mathlib's covering and
homotopy-lifting APIs are relevant, but the required period theorem is not
already packaged.

## 4. Honest theorem stack

The remaining work should be split into the following gates.

1. **Source complex manifold.** **Atlas and projection complete:** `ℂ/L` has
   an intrinsic complex charted/manifold structure and the quotient projection
   is locally biholomorphic. **Still open:** package and descend the constant
   form `dz`.
2. **Intrinsic target topology and atlas.** The equation-defined compact
   Hausdorff topology and variable-change homeomorphisms are complete. Give
   every nonsingular complex Weierstrass point type a one-dimensional
   complex-manifold structure from its equation, independently of any selected
   `τ`.
3. **Invariant differential.** Define the global regular form represented by
   `dx/(2y+a₁x+a₃)`, including the alternate local expressions needed where
   that denominator vanishes and at infinity. Prove it is holomorphic and
   nowhere zero.
4. **Analyticity of the existing maps.** The ambient affine variable-change
   map and its inverse are now packaged as biholomorphic polynomial maps, and
   the affine-locus homeomorphism is proved to be their restriction. After the
   target atlas exists, restrict this result to the curve manifolds, extend it
   through infinity, and prove the explicit Weierstrass map biholomorphic for
   the independently constructed structures.
5. **Pullback identity.** Upgrade the existing rational coefficient identities
   to an equality of global one-forms. Prove the lattice parametrization pulls
   the lattice-curve form back to `dz`, including ramification points and
   infinity; then obtain `C.u⁻¹ dz` for the embedded curve.
6. **Period computation.** Define integration along curve paths, compute the two
   fundamental loop integrals, and use covering-space lifting to identify all
   loop integrals with `C.u⁻¹(ℤ+ℤτ)`. The ratio is therefore `τ`.
7. **Arakelov/Faltings identification.** Only after the preceding gates should
   the project address the Hodge bundle, its metric and Arakelov degree. This is
   a further project, not a consequence of period realization alone.

The atlas/projection portion of gate 1 and the topology-only slice of gate 2
are complete. The ambient affine variable-change slice of gate 4 is also
complete, but no curve-level biholomorphism follows until gate 2 supplies its
atlas and the map is controlled at infinity. Descending `dz` finishes gate 1;
the complex-atlas part of gate 2, gate 3, the remaining parts of gates 4--6,
and then gate 7 remain substantial.

## 5. Judgment for the heights mission

No analytic-period assumption is needed for the theorem already proved in this
repository: `silvermanHeightOfCurve` is a canonical formula-defined quantity,
and its independence from the selected weak period data follows from the
`SL₂(ℤ)` orbit theorem and the weight-twelve transformation law. The proved
Proposition 2.1 comparison is therefore honest as a theorem about that formula.

Calling the result a comparison with an independently constructed Arakelov
Faltings height would still be unjustified. The next honest milestone is not a
single “prove `τ` is the period” declaration; it is the independently built
complex curve and invariant differential through gates 1--6 above. The source
complex torus and locally biholomorphic projection are now concrete completed
infrastructure, but they do not by themselves alter that overall feasibility
judgment.
