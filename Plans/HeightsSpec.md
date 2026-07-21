# Heights: phase-gated implementation specification

**Status:** living specification and implementation record. The original
phase-gated workflow has been superseded by autonomous development; the current
status table in §5 is authoritative.

**Pinned environment:** Lean 4 / mathlib `v4.32.0`

**Primary target:** taxis issue #32

## 1. Objective and source of truth

This repository aims to formalize the comparison between the absolute logarithmic
Weil height of the `j`-invariant and the elliptic-curve/Faltings height in J. H.
Silverman, “Heights and Elliptic Curves,” Chapter X of Cornell–Silverman (eds.),
*Arithmetic Geometry*, Springer (1986), especially Proposition 2.1. The local
source of truth is the complete chapter extraction
`references/silverman-heights.txt`; the page images are in the private file
`references/arithmetic_geometry.pdf`.

The extraction is from a scan and has OCR/ligature errors. In particular, the
factor in Proposition 1.1 can look like `12` in the extraction. Equations (8) and
(9), and the later comparison with `12 h(E/K)`, disambiguate it: the formula to
formalize is

\[
h_{\mathrm{Silv}}(E/K)=\frac{1}{12d}\left(
 \log N_{K/\mathbf Q}(\Delta_{E/K})-
 \sum_{v\mid\infty}n_v\log\bigl(|\Delta_{\rm mod}(\tau_v)|
 (\operatorname{Im}\tau_v)^6\bigr)\right),\qquad d=[K:\mathbf Q].
\]

Thus this height has both a finite-place minimal-discriminant term and an
archimedean modular-discriminant/period term. It is not permissible to replace it
by a coefficient height or by the Weil height of `j`. Remark 2.2 identifies this
quantity as the elliptic-curve version of the Faltings-height comparison.

The reference PDF is copyrighted and this repository is private. Both the PDF
and the non-redistributable chapter extraction must be removed from history or
otherwise excluded before any public release. No phase may copy substantial
reference text into source, blueprint, or generated documentation.

## 2. Honesty boundary

### 2.1 Mathematics to be proved in this repository

#### Normalizations

For a number field `K`, write

```lean
noncomputable def normalizedLogHeight
    (K : Type*) [Field K] [NumberField K] (x : K) : ℝ :=
  Height.logHeight₁ x / Module.finrank ℚ K
```

Mathlib's `Height.logHeight₁` is the logarithm of the relative height `H_K`:
`NumberField.logHeight₁_eq` is a sum over all places with infinite-place
multiplicities. Silverman's `h(x)` is the absolute height, so division by
`d = Module.finrank ℚ K` is essential. Over `ℚ`, this agrees with
`Rat.logHeight₁_eq_log_max`.

Use `Ideal.absNorm` for the absolute norm of an integral ideal and define

```lean
noncomputable def logIdealNorm (I : Ideal (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm I)
```

only when the relevant proof establishes `I ≠ ⊥`; this avoids treating the norm
of the zero ideal as legitimate height data.

Mathlib and [Silv] use different normalizations for the modular discriminant.
Mathlib has `η^24 = q ∏(1-qⁿ)^24`, while [Silv] includes `(2π)^12`. Keep that
constant explicit:

```lean
noncomputable def silvermanModularDiscriminant (τ : ℍ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ 12 * ModularForm.discriminant τ

noncomputable def modularJ (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ
```

The `j` quotient uses mathlib's normalized discriminant and has the usual
`q⁻¹ + 744 + ⋯` normalization; the Proposition 1.1 metric term uses
`silvermanModularDiscriminant`. Both discriminants are nonzero by
`ModularForm.discriminant_ne_zero` and `Real.pi_ne_zero`. The identity
`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` confirms the `j`
normalization. Dropping `(2π)^12` would only change Proposition 2.1 by an
absolute constant, but it would make the claimed Proposition 1.1 formula false
by a fixed additive normalization, so this plan does not drop it.

#### Unconditional targets

The following do not assume any elliptic uniformization certificate.

1. **Rational-height arithmetic.** Prove the exact numerator/denominator formula
   and its scaled variants from `Rat.logHeight₁_eq_log_max`.
2. **Reduced principal fractional ideals.** For `x ≠ 0`, construct coprime
   integral ideals `A, D` such that `(x) = A D⁻¹`. Define the denominator of
   `0` to be `⊤` and handle its numerator separately as `⊥`; this branch is
   required because elliptic curves with `j = 0` occur in Proposition 2.1.
   Prove the relative-height identity uniformly:
   \[
   \log H_K(x)=\log N(D)+
     \sum_{v\mid\infty}n_v\log\max\{|x|_v,1\}.
   \]
   This is equation (10) of [Silv], expressed using mathlib's normalized finite
   places.
3. **Analytic modular estimates with absolute constants.** Here
   `Δmod = silvermanModularDiscriminant`. Prove that constants `CΔ, Cy` exist,
   independent of `τ`, such that for every `τ ∈ ModularGroup.fd`,
   \[
   \left|-\log|\Delta_{\rm mod}(\tau)|-
     \log\max\{|j_{\rm mod}(\tau)|,1\}\right|\le C_\Delta
   \]
   and
   \[
   \left|\log(\operatorname{Im}\tau)-
     \log\log\max\{|j_{\rm mod}(\tau)|,e\}\right|\le C_y.
   \]
   The proof must use the actual functions above, their `q`-expansions, and a
   compact/truncated-fundamental-domain argument; these estimates may not be
   certificate fields.
4. **Weighted log-log estimate.** Formalize equation (11), including
   `∑ v.mult = d`, by weighted concavity/AM–GM:
   \[
   0\le\sum_v n_v\log\log\max\{|j|_v,e\}
   \le d\log(1+h(j)).
   \]
   Intermediate Jensen lemmas will be stated for arbitrary finite families of
   nonnegative reals.

#### Certificate-level Proposition 1.1 and Proposition 2.1

Given only the non-conclusion-smuggling data in §2.2, define

```lean
noncomputable def silvermanHeight
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (p : ArchimedeanPeriodData K W) : ℝ :=
  (Real.log (Ideal.absNorm m.ideal) -
      ∑ v : InfinitePlace K,
        v.mult * Real.log
          (‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6)) /
    (12 * Module.finrank ℚ K)
```

(Casts will be made explicit in Lean.) This is a formula-defined Silverman
height, not a placeholder real number called “Faltings height.” Proposition 1.1
justifies that formula once the supplied ideals and periods are genuinely those
of `W`.

For `W.j ≠ 0`, let `(W.j) = A D⁻¹` be reduced; for `W.j = 0`, set
`D = ⊤`. Let `Δmin = m.ideal`, prove `D ∣ Δmin`, and define the unstable
minimal discriminant `γ` by `Δmin = D * γ`. The zero-`j` branch must be proved,
not discharged by a nonzero assumption. The main certificate-level target is
one pair of **absolute** constants, independent of
`K`, `W`, and all certificates:

```lean
theorem proposition_2_1_certified :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (K : Type*) [Field K] [NumberField K]
      (W : WeierstrassCurve K) [W.IsElliptic]
      (m : GlobalMinimalDiscriminantData K W)
      (p : ArchimedeanPeriodData K W),
      let hj := normalizedLogHeight K W.j;
      let γ := unstableMinimalDiscriminant m;
      let hF := silvermanHeight W m p;
      -C ≤ hj + logIdealNorm γ / Module.finrank ℚ K - 12 * hF ∧
      hj + logIdealNorm γ / Module.finrank ℚ K - 12 * hF
        ≤ 6 * Real.log (1 + hj) + C
```

The reduced principal-ideal representation is now constructed unconditionally,
so the displayed signature uses its canonical choice and does not quantify an
external witness. Global minimal-discriminant data is also constructed over
every number field; `proposition_2_1_of_periods` instantiates `m` with that
choice, leaving only `ArchimedeanPeriodData`. The theorem must not quantify an
arbitrary `hF : ℝ`.

Define certified semistability place-by-place as “good or multiplicative” for a
minimal local model. Prove that semistability implies `γ = ⊤`, then derive

```lean
theorem proposition_2_1_semistable_certified :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (K : Type*) [Field K] [NumberField K]
      (W : WeierstrassCurve K) [W.IsElliptic]
      (m : GlobalMinimalDiscriminantData K W)
      (p : ArchimedeanPeriodData K W),
      IsSemistable K W m →
      |normalizedLogHeight K W.j - 12 * silvermanHeight W m p| ≤
        6 * Real.log (1 + normalizedLogHeight K W.j) + C
```

This was the largest initially justified headline result. The finite data and
the minimal `j`-compatible archimedean interface are now constructed, and the
latter is proved to algebraically realize every embedded input curve; the
distinction from an Arakelov Faltings height remains essential.

#### What is not claimed

The repository does **not** claim:

* an unconditional construction of the Faltings height as the Arakelov degree of
  the Hodge bundle;
* periods defined by integrating a differential on every embedded `W/K`
  (although the selected lattice curve is now related to it by an actual
  algebraic variable change);
* a packaged point-level analytic isomorphism for an arbitrary curve
  `E(ℂ) ≃ ℂ/(ℤ+ℤτ)` (the equation-level algebraic change is proved);
* an unconditional all-curves comparison with an independently constructed
  Arakelov Faltings height. The all-curves theorem now proved concerns only
  `silvermanHeightOfCurve`, the explicitly formula-defined height.

Those become targets only after the feasibility gate in P8. Merely restricting to
`K = ℚ` or to a totally real field does not remove the archimedean term: even a
real place requires a complex period lattice. Corollary 2.3 also depends on
Proposition 2.1 and therefore does not bypass this gap. Its elementary rational
identities are honest intermediate results, but its Faltings-height inequalities
remain certificate-level until uniformization is instantiated.

### 2.2 Exact interface signatures for missing geometric realization

The signatures below are proposed API shapes. P4 must compile-check and may make
minor namespace/cast changes without strengthening their mathematical content.
The declarations compile in the following scoped environment:

```lean
open scoped NumberField UpperHalfPlane nonZeroDivisors
open NumberField IsDedekindDomain
```

#### Local integrality and minimal discriminant exponents

To avoid pretending that mathlib has already assembled local models globally,
define integrality directly with the number-field prime valuation:

```lean
structure IsIntegralAt
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (W : WeierstrassCurve K) : Prop where
  a₁ : v.valuation K W.a₁ ≤ 1
  a₂ : v.valuation K W.a₂ ≤ 1
  a₃ : v.valuation K W.a₃ ≤ 1
  a₄ : v.valuation K W.a₄ ≤ 1
  a₆ : v.valuation K W.a₆ ≤ 1

structure IsLocalMinimalDiscriminantExponent
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (W : WeierstrassCurve K) (n : ℕ) where
  change : WeierstrassCurve.VariableChange K
  integral : IsIntegralAt K v (change • W)
  exponent : v.valuation K (change • W).Δ = WithZero.exp (-(n : ℤ))
  maximal : ∀ C : WeierstrassCurve.VariableChange K,
    IsIntegralAt K v (C • W) →
      v.valuation K (C • W).Δ ≤ WithZero.exp (-(n : ℤ))
```

`IsLocalMinimalDiscriminantExponent` is data-valued because its `change` field
stores a variable change; a `Prop`-valued structure may contain only proof
fields. The order is correct for mathlib's multiplicative valuation: additive
order `n` is represented by `exp (-n)`, and a minimal discriminant exponent gives
the maximal multiplicative valuation among integral changes. This signature is a
restatement of local minimality, not of any height comparison. P4 must prove its
compatibility with `WeierstrassCurve.IsIntegral`,
`WeierstrassCurve.IsMinimal`, and `WeierstrassCurve.valuation_Δ_aux` after
localization whenever the required instances synthesize.

#### Global minimal-discriminant realization

```lean
structure GlobalMinimalDiscriminantData
    (K : Type*) [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] where
  ideal : Ideal (𝓞 K)
  ideal_ne_bot : ideal ≠ ⊥
  realizes : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    IsLocalMinimalDiscriminantExponent K v W
      (multiplicity v.asIdeal ideal)
```

This supplies one integral ideal and proves that every prime exponent is the
local minimum. It does not supply `D ∣ ideal`, an unstable ideal, a height, or an
inequality. Those are repository theorems. Literature justification is Tate's
local-minimal-model description used in [Silv] Proposition 1.1: the global ideal
is characterized by its local discriminant exponents, even when no single global
minimal Weierstrass equation exists.

#### Archimedean periods

```lean
structure ArchimedeanPeriodData
    (K : Type*) [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] where
  τ : InfinitePlace K → ℍ
  mem_fd : ∀ v, τ v ∈ ModularGroup.fd
  j_eq : ∀ v,
    v.embedding W.j = modularJ (τ v)
```

This supplies a period ratio in the standard fundamental domain and its
compatibility with the algebraic `j`-invariant. It does not contain a bound on
`τ.im`, a bound on `discriminant`, the height formula, or the target comparison.
The signature is justified by complex uniformization and classification of
complex elliptic curves by `j`; choosing the fundamental domain makes the
global modular bounds directly applicable. The repository now separately
proves that equal `modularJ` values lie in one `SL₂(ℤ)` orbit and that
`‖silvermanModularDiscriminant τ‖ * τ.im ^ 6` is invariant on that orbit.
Thus `silvermanHeight` is independent of the qualifying period-data choice.
Moreover, `ArchimedeanPeriodData.exists_variableChange_to_latticeCurve` proves
that `j_eq` supplies an actual admissible algebraic variable change from the
complex base change of `W` to the explicit lattice curve; the complex twisting
obstruction therefore disappears. The exact `u³` scaling of
`2y + a₁x + a₃` and the resulting exact `u⁻¹` rational differential
coefficient are also proved. The formula still uses the actual
`silvermanModularDiscriminant` (including `(2π)^12`) and the actual `τ.im`, so
both archimedean factors of Proposition 1.1 remain visible.

A stronger future interface may package the variable change as an additive and
analytic point equivalence, define invariant differentials and their integrals,
and derive the period lattice in that language. That stronger object is
preferable for an Arakelov interpretation, but it is not required to prove the
analytic comparison from Proposition 1.1's formula.

#### Reduced principal fractional ideals

This is expected to be proved rather than assumed. If mathlib API friction makes
a temporary data object useful, its maximum permitted content is:

```lean
structure ReducedPrincipalIdealData
    (K : Type*) [Field K] [NumberField K] (x : K) where
  numerator : Ideal (𝓞 K)
  denominator : Ideal (𝓞 K)
  denominator_ne_bot : denominator ≠ (⊥ : Ideal (𝓞 K))
  numerator_ne_bot : (x ≠ 0) → numerator ≠ (⊥ : Ideal (𝓞 K))
  zero_normalization : (x = 0) →
    numerator = (⊥ : Ideal (𝓞 K)) ∧ denominator = (⊤ : Ideal (𝓞 K))
  coprime : IsCoprime numerator denominator
  span_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ x =
    FractionalIdeal.coeIdeal numerator /
      FractionalIdeal.coeIdeal denominator
```

It may not contain a relative-height formula, divisibility by a minimal
discriminant, or a comparison inequality. The object records the standard
coprime ideal factorization `(x)=A D⁻¹` used immediately before equation (9),
with an explicit convention for `x = 0` rather than silently assuming `j ≠ 0`.

### 2.3 Explicit library gaps and forbidden shortcuts

The finite realization gap and the algebraic archimedean realization are now
discharged; an analytic/integration gap remains.

1. **Global arithmetic assembly (completed).** `Reduction.lean` proves local
   minimal-model existence over a DVR. This repository bridges it to the
   number-field valuation framework, clears all five coefficient denominators
   by one scaling over `𝓞 K`, bounds the local minimal exponents by the resulting
   integral discriminant, and uses Dedekind ideal factorization to construct
   `GlobalMinimalDiscriminantData K W` for every number field (taxis #56).
2. **Complex uniformization bridge.** Mathlib has upper-half-plane geometry,
   modular forms, the modular discriminant, period lattices, and Weierstrass
   `℘`, but no theorem producing periods from an arbitrary algebraic elliptic
   curve over `ℂ`. This repository constructs the explicit curve attached to
   `(τ, 1)` and proves that its descended Weierstrass map is both a
   homeomorphism and an additive equivalence `ℂ/L ≃+ Eτ(ℂ)`. It also proves
   `Function.Surjective modularJ` by showing the holomorphic image is open and,
   using cusp growth plus compact truncated fundamental domains, closed. This
   constructs the minimal `ArchimedeanPeriodData` interface for every curve.
   Same-`j` classification over `ℂ` now gives an actual algebraic variable
   change from each embedded input curve to its selected lattice curve, and the
   invariant-differential denominator scaling is explicit. It still does not
   package that change as an additive/analytic point equivalence, define periods
   by integration, or give an Arakelov identification.
   See `Plans/ArchimedeanUniformizationFeasibility.md` and taxis #57/#128/#174.

Forbidden in every phase:

* declaring the missing facts as Lean axioms;
* adding a certificate field equal to Proposition 1.1's complete height formula
  for an arbitrary real-valued “height”;
* adding a field that is either inequality of Proposition 2.1;
* defining “Faltings height” to be `normalizedLogHeight K W.j / 12`;
* replacing `|Δmod(τ)| (Im τ)^6` by a free real or a coefficient-height proxy;
* claiming the `ℚ` case avoids periods;
* hiding an unproved realization theorem behind a typeclass instance.

### 2.4 Verified mathlib `v4.32.0` API snapshot

The following was checked against `.lake/packages/mathlib/Mathlib/`.

#### Heights

* `Mathlib.NumberTheory.Height.Basic` defines
  `Height.AdmissibleAbsValues`, `Height.mulHeight₁`,
  `Height.logHeight₁`, `Height.mulHeight`, and `Height.logHeight`.
  It proves `Height.one_le_mulHeight₁`, `Height.zero_le_logHeight₁`, and
  the place-sum formula `Height.logHeight₁_eq`.
* `Mathlib.NumberTheory.Height.Projectivization` defines
  `Projectivization.mulHeight` and `Projectivization.logHeight`, with
  `Projectivization.logHeight_nonneg`.
* `Mathlib.NumberTheory.Height.NumberField` provides the number-field instance
  `NumberField.instAdmissibleAbsValues`, the exact formulas
  `NumberField.mulHeight₁_eq` and `NumberField.logHeight₁_eq`, and
  `NumberField.totalWeight_eq_finrank`. It proves Northcott finiteness as
  `NumberField.finite_setOf_mulHeight₁_le` and
  `NumberField.finite_setOf_logHeight₁_le`. For rationals it proves
  `Rat.mulHeight₁_eq_max` and `Rat.logHeight₁_eq_log_max`.
* `Mathlib.NumberTheory.Height.MvPolynomial` proves homogeneous-map estimates
  `Height.logHeight_eval_le'` and `Height.logHeight_eval_ge'` (as well as
  explicit versions without the prime).
* `Mathlib.NumberTheory.Height.Northcott` supplies a `Northcott` instance for
  `Height.logHeight₁` from one for `Height.mulHeight₁`.
* `Mathlib.NumberTheory.Height.EllipticCurve` currently proves only
  `WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le`.
  Despite the file title, its TODO list still says to define naïve height and
  prove the approximate parallelogram law. It contains no canonical height,
  `j`-height, or Faltings-height comparison.

#### Algebraic elliptic curves and reduction

* `WeierstrassCurve.j`, `WeierstrassCurve.map_j`, and the discriminant and
  `c₄,c₆` relations are in
  `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`.
  `WeierstrassCurve.variableChange_j` is in `VariableChange`.
* `Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ` defines
  `WeierstrassCurve.ofJ` and proves `WeierstrassCurve.ofJ_j`.
* `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` defines
  `WeierstrassCurve.IsIntegral`, `WeierstrassCurve.IsMinimal`,
  `WeierstrassCurve.valuation_Δ_aux`, `WeierstrassCurve.minimal`, and
  `WeierstrassCurve.reduction`. It proves
  `WeierstrassCurve.exists_isIntegral` and
  `WeierstrassCurve.exists_isMinimal`. Reduction predicates are
  `HasGoodReduction`, `HasMultiplicativeReduction`,
  `HasAdditiveReduction`, and `HasSplitMultiplicativeReduction`; the old
  `IsGoodReduction` name is deprecated.
* The reduction file is local: its base is a DVR with a fraction field. Search
  found no global `minimalDiscriminant` ideal, no unstable minimal
  discriminant, and no semistable all-places assembly for number fields.
* Dedekind-domain and number-field infrastructure needed for an assembly does
  exist: `IsDedekindDomain.HeightOneSpectrum.valuation`, ideal
  `multiplicity`, `Ideal.finprod_heightOneSpectrum_pow_multiplicity`, and
  `Ideal.absNorm`.

#### Modular and archimedean analysis

* Contrary to an initial “possibly absent” assumption,
  `Mathlib.NumberTheory.ModularForms.Discriminant` defines
  `ModularForm.discriminant (τ) = eta τ ^ 24 = q∏(1-qⁿ)^24`. This is the
  normalized modular-form convention; [Silv]'s analytic discriminant is
  `(2π)^12` times this function, which the project must define explicitly. The
  file proves
  `ModularForm.discriminant_eq_q_prod`,
  `ModularForm.discriminant_ne_zero`,
  `ModularForm.discriminant_T_invariant`,
  `ModularForm.discriminant_S_invariant`, and the cusp asymptotic
  `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow`. It also packages it
  as `CuspForm.discriminant`.
* `Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing` proves
  `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`. Normalized
  `ModularForm.E₄` and `ModularForm.E₆` and their `q`-expansions are available.
  There is no pre-existing modular `j` function under a `j`,
  `klein`, or `jInvariant` name; the quotient `E₄^3/Δ` must be defined here.
* `Mathlib.NumberTheory.Modular` defines `ModularGroup.fd` (notation `𝒟`),
  proves `ModularGroup.exists_smul_mem_fd`, and proves
  `ModularGroup.three_le_four_mul_im_sq_of_mem_fd`.
  `Mathlib.NumberTheory.ModularForms.Bounds` supplies compact/truncated-domain
  bounding machinery, notably
  `ModularGroup.exists_bound_fundamental_domain_of_isBigO`.
* `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` defines
  `PeriodPair`, `PeriodPair.lattice`, `PeriodPair.weierstrassP`,
  `PeriodPair.derivWeierstrassP`, lattice invariants `PeriodPair.g₂` and
  `PeriodPair.g₃`, and proves `PeriodPair.derivWeierstrassP_sq`. Its own TODO
  says to connect lattice Eisenstein series to the modular-forms library.
  `Heights/LatticeEisenstein.lean` now supplies the exact `G₄/G₆` to `E₄/E₆`
  normalization and proves the resulting lattice discriminant nonzero.
  `Heights/LatticeWeierstrass.lean` constructs the associated short curve and
  identifies its algebraic `j` with `modularJ`; `Heights/LatticeAffinePoint.lean`
  packages `(℘, ℘′/2)` as an affine point away from the lattice and proves
  invariance under lattice translation; and
  `Heights/LatticeQuotientPoint.lean` extends that map at the poles and descends
  it set-theoretically through `ℂ/L`. The quotient and target topologies are
  packaged in `Heights/LatticeQuotientTopology.lean` and
  `Heights/LatticeCurveTopology.lean`, with source compactness proved in
  `Heights/LatticeQuotientCompact.lean`; `Heights/LatticeAffinePointTopology.lean`
  proves continuity on the pole-free affine chart, and
  `Heights/LatticePointMapTopology.lean` uses the pole order to prove continuity
  of the total and descended maps at infinity. Search still found no analytic
  complex torus attached to a `PeriodPair`, no analytic extension across
  infinity, and no algebraic elliptic-curve uniformization theorem.
* `UpperHalfPlane`, its `SL₂` action, `qParam`, and the analytic ingredients are
  therefore present. The missing part is the bridge from an algebraic curve to
  this analytic data, not the modular discriminant itself.
* A case-insensitive source search found no occurrence of “Faltings” in
  mathlib and no alternate Faltings-height definition.

## 3. Comparator challenge suite and justification

Create:

```text
Comparator/Challenge.lean
Comparator/Solution.lean
Comparator/config.json
```

`Challenge.lean` imports only `Mathlib`. Each target is a standalone theorem and
its body is exactly one reviewed `sorry`. Helper definitions may be included but
may contain no proof holes. `Solution.lean` imports the project and re-exports a
proved project theorem at exactly the challenge type. `config.json` lists only
targets whose project proofs currently compile; an unproved challenge remains in
`Challenge.lean` but is absent from the config.

Planned targets:

| ID | Standalone content | Planned phase | Why it is diagnostic |
|---|---|---:|---|
| `rat_height_scaled_denominator` | For `q : ℚ` and positive `n : ℕ`, `Height.logHeight₁ q + log n = log (max (q.num.natAbs*n) (q.den*n))` with explicit casts. | P2 | Checks the exact rational normalization used in Corollary 2.3. |
| `weighted_log_one_add_average` | Weighted Jensen/AM–GM inequality for `∑ wᵢ log(1+xᵢ)` with nonnegative `xᵢ` and `∑wᵢ=d>0`. | P2 | Isolates equation (11), including degree normalization. |
| `modular_delta_j_fd_comparison` | Existence of an absolute constant bounding `-log ‖(2π)^12 Δ(τ)‖ - log(max ‖E₄(τ)^3/Δ(τ)‖ 1)` for `τ ∈ ModularGroup.fd`. | P3 | Exercises the genuinely analytic heart and the [Silv]/mathlib normalization rather than an abstract proxy. |
| `silverman_proposition_2_1_certified` | The expanded, project-independent statement of the certified two-sided estimate, quantifying `W`, ideals, and periods directly and defining the Silverman height by the displayed finite-plus-archimedean formula. | P6 | Headline comparison; it cannot be passed by naming an arbitrary real “Faltings height.” |

The final target's exact expanded type is frozen at the P4 interface gate, after
all casts and ideal quotient representations compile. It must import only
`Mathlib`; it may duplicate transparent helper definitions from the challenge,
but may not import `Heights` or include an assumption equivalent to either final
inequality.

Initially `config.json` is empty. P2 adds the first two IDs, P3 adds the third,
and P6 adds the headline ID. A CI check compares config entries against
`Solution.lean` declarations and rejects stale or aspirational entries.

## 4. Repository conventions, trust audit, and phase gates

### Layout and naming

```text
Heights/
  WeilHeight.lean
  IdealFactorization.lean
  ModularJ.lean
  ModularBounds.lean
  Certificates.lean
  SilvermanHeight.lean
  Comparison.lean
  Semistable.lean
Comparator/
Blueprint/                 # Verso blueprint, based on blueprint-verso
scripts/
Plans/
```

`Heights.lean` becomes the public umbrella import. Public declarations receive
docstrings and source citations. Definitions are kept separate from uncertain
realization theorems. No source file may import anything from `references/`.

Build commands are always bounded, for example `LAKE_JOBS=6 lake build` or
`lake build -j6`.

### Trust audit

`scripts/audit_trust.sh` scans tracked source and project-control files, not the
ignored `.lake` dependency tree. It must fail on:

* forbidden Lean trust escapes: `axiom`, proof holes, `native_decide`,
  `implemented_by`, and `unsafe` declarations;
* committed credentials: private keys, common token/password/authorization
  assignments, the taxis token shape, and credential-bearing URLs;
* machine-local absolute paths such as `/home/...`, `/Users/...`, or a tracked
  `.pi/orchestration/taxis.env`.

The only proof-hole exceptions are the one-hole theorem bodies in
`Comparator/Challenge.lean`. Exceptions live in a reviewed TSV/JSON file as
exact `(path, line, token, reason)` records. There are no directory, prefix, or
glob exceptions. The audit verifies that every exception matches exactly one
current occurrence and that every exception is used; line movement therefore
requires explicit review. Documentation occurrences needed to describe the
policy are either scanned with token-aware rules or entered as exact records,
never broadly excluded.

### Axiom audit

`scripts/AuditAxioms.lean` enumerates every public declaration in project
modules, excluding declarations in `Comparator.Challenge`, and prints/checks its
transitive axioms. `scripts/audit_axioms.sh` builds that module, parses a
machine-stable marker format, and fails unless every axiom is exactly one of:

```text
propext
Quot.sound
Classical.choice
```

It also fails if a project declaration is missed, if an unknown declaration
cannot be inspected, or if a challenge proof-hole axiom leaks through
`Solution.lean`. The shell audit and Lean audit run in CI after the bounded full
build.

### Development protocol

The phase-gate protocol used for bootstrap and initial specification review has
been superseded by the autonomous workflow in `CLAUDE.md`. The checks and honesty
criteria below remain requirements, but phases are now organizational landmarks,
not mandatory implement/review gates. Small honest commits, full bounded CI, the
trust/axiom audits, and taxis status reporting remain in force.

## 5. Phases

The detailed briefs below are retained as historical design context. This table
is the current status; a completed row means the repository has the promised
mathematical content, not that the abandoned review ceremony was performed.

| Phase | Current status (updated 2026-07-21) |
|---|---|
| P0 | Complete: package and reviewed honesty specification. |
| P1 | Complete: blueprint, comparator, bounded CI, trust and axiom audits. |
| P2 | Complete: normalized heights, reduced ideals, finite-place identity, weighted bounds. |
| P3 | Complete: actual modular functions and both absolute fundamental-domain estimates. |
| P4 | Complete: realization interfaces compile and contain no comparison conclusions. |
| P5 | Complete: denominator divisibility, canonical unstable ideal, exact finite/archimedean decomposition, semistability. |
| P6 | Complete: both certified Proposition 2.1 theorems and the expanded comparator target. |
| P7 | Partially complete: rational arithmetic, equation (11), and ε-absorption are proved; no uncertified Faltings-height corollary is claimed. |
| P8 | Arithmetic branch GO and complete over every number field (#56). Archimedean Route A and its algebraic strengthening are complete: `modularJ_surjective` constructs `ArchimedeanPeriodData`, and same-`j` classification gives an actual variable change to every embedded input curve (#57/#128). Route B also gives a topological and additive uniformization of the explicit lattice curve. Point-level arbitrary-curve analytic uniformization, integration, and Arakelov identification remain unavailable (#174). |
| P9 | Complete for the formula-defined object: `silvermanHeightOfCurve`, `proposition_2_1`, and its semistable specialization have no realization-certificate arguments. No comparison with an independently constructed Arakelov Faltings height is claimed. |

### P0 — Bootstrap (already committed)

**Commit:** `0e77dc1`.

**Scope.** Added the Lean package scaffold (`Heights.lean`, `lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`), repository/orchestration instructions,
ignore rules, and the pypdf chapter extraction. `Heights.lean` imports `Mathlib`
and contains only a trivial link-check example. The commit did not add a
blueprint, comparator, audits, height definitions, or mathematical
formalization; it did not modify the already-present copyrighted PDF.

**Checks.** Inspect the commit diff; optionally run `LAKE_JOBS=6 lake build`;
confirm no formal theorem from [Silv] is claimed.

**Gate.** This specification and work log receive adversarial review. The P0 row
is completed only by that reviewer.

### P1 — Governance, blueprint skeleton, audits, and comparator harness

**Scope.** Incorporate accepted spec corrections. Add the Verso blueprint
skeleton, trust and axiom audits, CI/bounded-build scripts, and the comparator
layout with four challenge holes and an empty config. Add no comparison proof.

**Checks.** `LAKE_JOBS=6 lake build`; blueprint build; trust audit; axiom audit;
challenge has exactly one reviewed hole per target; config is empty; credential
fixture tests demonstrate both acceptance and rejection paths without real
secrets.

**Gate.** Reviewer checks that audit exceptions are exact records, that the
copyright warning is prominent, and that no blueprint prose overstates the
honesty boundary.

### P2 — Weil-height normalization and ideal arithmetic

**Scope.** Implement `normalizedLogHeight`, rational scaled-denominator
identities, reduced principal fractional-ideal factorization, the finite-place
height identity, and the general weighted Jensen/AM–GM lemma. Add the first two
comparator solutions/config entries and blueprint statements.

**Checks.** Full bounded build and audits; direct tests over `ℚ`, including
`q = 0`; all divisions by `d` have positivity proofs; no field-degree factor is
silently dropped.

**Gate.** Reviewer reconciles every normalization with
`NumberField.logHeight₁_eq`, equations (9)–(11), and
`Rat.logHeight₁_eq_log_max`.

### P3 — Modular `j` and absolute analytic estimates

**Scope.** Define `modularJ`; prove nonvanishing prerequisites, modular
invariance needed for well-defined fundamental-domain use, the two
fundamental-domain estimates of §2.1, and the third comparator target. Use
`q`-expansions for the cusp and compactness below a fixed imaginary-height
cutoff.

**Checks.** Full bounded build and audits; constants are quantified before `τ`
and do not depend on a field or curve; no estimate is assumed as an interface;
comparator imports only `Mathlib`.

**Gate.** Adversarial analytic review checks both normalizations (`E₄³/Δ`, not
a factor-1728 variant, but `(2π)^12Δ` in Proposition 1.1), behavior near zeros
of `E₄`, positivity of all logarithm arguments, and the compactness argument.

### P4 — Feasibility gate: compile the certificate boundary

**Scope.** Implement and compile the §2.2 interfaces, compatibility lemmas with
`Reduction.lean`, `silvermanHeight`, local semistability predicates, and the
expanded headline challenge type. Do not yet prove Proposition 2.1.

**Feasibility questions.** Verify:

1. whether prime valuations on `K` suffice cleanly or localization API is
   required;
2. whether ideal quotient/cancellation supports a canonical unstable ideal;
3. whether local minimality proves denominator divisibility without Tate
   algorithm;
4. whether the period `j_eq` orientation is stable under the chosen
   `InfinitePlace.embedding`.

If any answer is negative, stop and revise the interface or phase plan. Do not
add stronger certificate fields to force progress.

**Checks.** Full bounded build/audits; declarations have no proof holes; direct
source audit confirms no comparison proposition appears as a field.

**Gate.** Reviewer performs a conclusion-smuggling audit field by field and must
explicitly accept the interface before P5 starts.

### P5 — Proposition 1.1 formula object and finite-place assembly

**Scope.** Prove that the reduced denominator ideal divides the certified minimal
discriminant ideal; construct `γ`; rewrite `12 * silvermanHeight` into the exact
equation (9) decomposition. Prove semistability implies `γ = ⊤` from good or
multiplicative local valuation conditions.

**Checks.** Full bounded build/audits; ideal equalities are proved prime by prime;
`Ideal.absNorm` is applied only to nonzero ideals; finite and archimedean terms
both remain in the formula.

**Gate.** Reviewer compares the Lean rewrite term-by-term with equations (8),
(9), and (10), including signs and the factor `12d`.

### P6 — Certified Proposition 2.1

**Scope.** Combine P2, P3, and P5 to prove the universal two-sided estimate and
its semistable absolute-value specialization. Add the headline comparator
solution/config entry and complete the corresponding blueprint proof links.

**Checks.** Full bounded build, blueprint, comparator, trust, and all-public axiom
audits. Quantifier inspection must show the constant precedes `K`, `W`, and
certificates. The theorem must use `silvermanHeight`, not an arbitrary real.

**Gate.** Adversarial reviewer reconstructs the mathematical proof from Lean
lemmas and certifies that this is exactly a conditional/certificate-level
Proposition 2.1.

### P7 — Largest unconditional corollaries and the rational specialization

**Scope.** Prove all parts of Corollary 2.3 that are independent of period
existence: rational numerator/denominator/discriminant identities, the
`c₄,c₆,Δ,j` algebra, and the elementary absorption
`6 log(1+log t) ≤ ε log t + Oε(1)`. State and prove the full inequalities only
with `ArchimedeanPeriodData ℚ W` as the remaining realization hypothesis.

**Checks.** Full bounded build/audits; theorem names distinguish unconditional
algebra from certified height comparisons; no claim says the `ℚ` case removes
the archimedean input.

**Gate.** Reviewer identifies the largest unconditional theorem and verifies the
blueprint labels all remaining hypotheses.

### P8 — Feasibility gate: unconditional realization

**Scope.** Investigate, without promising implementation, whether every
`W/K` can be supplied with the two certificates from existing mathlib plus
tractable additions. Produce compiling micro-prototypes and a written gap
report for:

* assembling local minimal exponents into an ideal;
* constructing complex periods and a lattice quotient;
* identifying algebraic and modular `j`;
* relating the formula-defined height to a future Arakelov/Hodge-bundle
  Faltings height.

**Decision.** The finite branch, the formula-level archimedean branch, and its
algebraic realization are GO and complete. The latter combines modular-`j`
surjectivity with same-`j` classification over `ℂ`. Point-level arbitrary-curve
analytic uniformization, integration of invariant differentials, and Arakelov
identification remain STOP as separate mathlib-scale projects.

**Checks.** Gap report cites exact failed/successful APIs and contains no
noncompiling tracked Lean experiments.

**Gate.** Owner/orchestrator and adversarial reviewer explicitly choose `GO` or
`STOP`. `STOP` is a successful honest project outcome, not a failed gate.

### P9 — Unconditional instantiation (only after a P8 `GO`)

**Scope.** Construct both formula-level certificates for every elliptic `W/K`
and derive the unconditional formula-defined Proposition 2.1 and semistable
specialization. This is now complete. No independent formal Faltings-height
object has been constructed, so no Arakelov relationship is stated.

**Checks.** Full bounded build, blueprint, comparator, trust, and all-public axiom
audits; remove every “certified” hypothesis only via an existence theorem.

**Gate.** Final adversarial mathematical and honesty review. No unconditional
Faltings-height wording is accepted unless an actual Hodge-bundle/Arakelov
height or a formally justified equivalent has been connected to the formula.

## 6. Review log

| Phase | Commit | Reviewer | Verdict | Date | Notes |
|---|---|---|---|---|---|
| P0 | 0e77dc1 | orchestrator |  | 2026-07-20 | scaffold + reference extract only, no formalization code |
| P0 spec (round 1) | (superseded before commit) | pi | CHANGES REQUESTED | 2026-07-20 | `EisensteinSeries.E₄`/`E₆` do not exist (real names `ModularForm.E₄`/`E₆`, `EisensteinSeries/Basic.lean:51,54`); `IsIntegralAt`/`GlobalMinimalDiscriminantData`/`ArchimedeanPeriodData`/`ReducedPrincipalIdealData` signatures in §2.2 do not compile as written (missing scoped namespaces, `VariableChange` vs `WeierstrassCurve.VariableChange`, wrong `FractionalIdeal.spanSingleton` argument shape — it takes an explicit submonoid `S` before `x`). Mathematical content, sign conventions, and honesty boundary otherwise held up under review.
| P0 spec (round 2) | `bf8109e` | pi | ACCEPTED | 2026-07-20 | Both round-1 findings fixed and independently re-verified (orchestrator and reviewer both elaborated the corrected §2.2 declarations and `modularJ` under `import Mathlib`, `sorry`-holed). No regressions outside the two findings' scope. P0 gate closed.
| P1 (round 1) | (uncommitted) | pi | CHANGES REQUESTED | 2026-07-20 | (1) headline comparator target takes `Δmin = D * γ` as a free hypothesis instead of deriving `γ` from permitted certificate data, weakening it relative to the spec's `unstableMinimalDiscriminant m r` construction; (2) `audit_trust.sh`'s `if path == registry: continue` skips ALL checks (not just the machine-path exemption) for `scripts/trust-exceptions.tsv`, so a real or fake credential pasted into that file would never be caught; (3) `AuditAxioms.lean` only inspects the `import Heights`/`import Solution` transitive closure, so a tracked but never-imported `.lean` file's declarations would be invisible to both the compiled-manifest and visited-declaration checks, silently bypassing the audit; (4) no CI workflow / aggregate bounded-check script, though spec P1 scope lists "CI/bounded-build scripts." All four independently reproduced by the orchestrator.
