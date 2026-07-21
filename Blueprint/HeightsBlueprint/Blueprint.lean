import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Heights

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Weil and Silverman Height Comparisons" =>

# Scope, privacy, and honesty boundary

## PRIVATE COPYRIGHTED SOURCES — NOT FOR PUBLIC RELEASE

> `references/arithmetic_geometry.pdf` and
> `references/silverman-heights.txt` are private, non-redistributable reference
> material. They must be removed from history or otherwise excluded before any
> public release. This blueprint does not reproduce substantial source text.

This blueprint tracks the program specified in `Plans/HeightsSpec.md`. There
are two deliberately separate kinds of result:

* *Unconditional targets* are to be proved from mathlib without elliptic
  uniformization certificates.
* *Certificate-level targets* assume explicit local-minimal-model and
  archimedean-period realization data. Reduced principal-ideal data is now
  constructed unconditionally and is no longer one of these hypotheses. The
  remaining interfaces are not known to exist for every elliptic curve, and
  they do not give an unconditional construction of the Faltings height.

Status is derived from the attached Lean declarations where proofs now exist.
Unlinked items remain targets rather than claims.

# Normalizations

:::definition "def:normalized-log-height" (lean := "Heights.normalizedLogHeight")
Mathlib's `logHeight₁` is the relative height: its local sum is naturally
scaled by $`[K:\mathbb Q]`. Dividing by the degree produces the absolute height
used in Silverman's comparison and makes the normalization insensitive to the
field over which an algebraic number is viewed. Nonnegativity descends from the
nonnegative relative height.

*Status: `Heights.normalizedLogHeight` and
`Heights.normalizedLogHeight_nonneg` are formalized unconditionally.*
:::

:::definition "def:log-ideal-norm" (lean := "Heights.logIdealNorm, Heights.absNorm_pos_of_ne_bot, Heights.logIdealNorm_nonneg")
For a nonzero integral ideal $`I`, $`\log N(I)` is defined using
`Ideal.absNorm`. The accompanying lemmas prove strict positivity of the norm
and nonnegativity of its logarithm from $`I\ne 0`.

*Status: formalized unconditionally.*
:::

:::definition "def:silverman-modular-discriminant" (lean := "Heights.silvermanModularDiscriminant, Heights.silvermanModularDiscriminant_ne_zero")
Mathlib normalizes the discriminant as $`\eta^{24}=q\prod_{n\ge1}(1-q^n)^{24}`,
whereas the discriminant in the archimedean metric formula carries the factor
$`(2\pi)^{12}`. Retaining this factor gives the exact Proposition 1.1
normalization rather than merely a height differing by an additive constant;
nonvanishing follows from nonvanishing of both factors.

*Status: `Heights.silvermanModularDiscriminant` and its nonvanishing theorem are
formalized unconditionally.*
:::

:::definition "def:modular-j" (lean := "Heights.modularJ, Heights.modularJ_mul_discriminant, Heights.modularJ_eq_zero_iff, Heights.modularJ_smul, Heights.exists_mem_fd_modularJ_eq_of_surjective")
The quotient $`E_4^3/\Delta` has leading term $`q^{-1}` and is therefore the
$`q^{-1}+744+\cdots` modular invariant used in the height estimates, with no
extra factor of $`1728`. The $`E_4,E_6,\Delta` identity checks this convention,
while modular invariance permits a preimage to be moved into the standard
fundamental domain.

*Status: `Heights.modularJ` and the linked normalization/invariance lemmas are
formalized unconditionally; `prop:modular-estimates` proves the required global
bounds.*
:::

# Unconditional mathematics

:::proposition "prop:rational-height-arithmetic" (uses := "def:normalized-log-height") (lean := "Heights.normalizedLogHeight_rat, Heights.ratHeight_scaled_denominator")
For a reduced rational $`a/b`, the local definition collapses to
$`h(a/b)=\log\max(|a|,b)`. The proof starts from mathlib's exact rational-height
formula; multiplying numerator and denominator by the same positive integer
then pulls that factor through `max` and the logarithm. The zero rational is
kept in the argument rather than removed by a nonzero hypothesis.

*Status: `Heights.normalizedLogHeight_rat` and
`Heights.ratHeight_scaled_denominator` are proved unconditionally.*
:::

:::proposition "prop:epsilon-absorption" (lean := "Heights.six_logOneAdd_log_le_epsilon_log_add, Heights.six_logOneAdd_log_epsilon_absorption")
For every $`\varepsilon>0`, there is a nonnegative constant $`C_\varepsilon`
such that, uniformly for $`t\ge 1`,
$`6\log(1+\log t)\le \varepsilon\log t+C_\varepsilon`.
An explicit valid choice is $`C_\varepsilon=6\log(1+6/\varepsilon)`.

*Status: proved unconditionally.*
:::

:::proposition "prop:reduced-principal-ideals" (uses := "def:log-ideal-norm") (lean := "Heights.exists_reducedPrincipalIdealData, Heights.reducedPrincipalIdealData, Heights.ReducedPrincipalIdealData.logHeight_eq_logIdealNorm_add_infinitePlace")
Every number-field element has coprime numerator and denominator ideals for its
principal fractional ideal, including the required $`x=0` convention. A
canonical choice is fixed, and the finite-plus-archimedean relative-height
identity is proved.

*Status: proved unconditionally.*
:::

:::proposition "prop:modular-estimates" (uses := "def:silverman-modular-discriminant, def:modular-j") (lean := "Heights.modularDeltaJ_fd_comparison, Heights.modularIm_logLogJ_fd_comparison")
There are absolute-constant bounds on the standard fundamental domain comparing
$`-\log|\Delta_{\mathrm{Silv}}|` with $`\log\max(|j|,1)`, and comparing
$`\log\operatorname{Im}(\tau)` with
$`\log\log\max(|j|,e)`. The proofs use the actual modular functions, their cusp
limits and product expansion, and truncated-fundamental-domain compactness.

*Status: proved unconditionally.*
:::

:::proposition "prop:lattice-eisenstein-normalization" (uses := "def:modular-j") (lean := "Heights.periodPairOfUpperHalfPlane, Heights.periodPair_G_eq_tsum_eisSummand, Heights.periodPair_G_eq_two_mul_riemannZeta_mul_E, Heights.periodPair_G_four, Heights.periodPair_G_six, Heights.periodPair_invariant_discriminant, Heights.periodPair_invariant_discriminant_ne_zero")
For $`\tau\in\mathfrak H`, the basis $`(\tau,1)` defines the usual lattice
$`\mathbb Z+\mathbb Z\tau`. Its full lattice sums satisfy the exact
normalizations
$`G_4=\pi^4E_4/45` and $`G_6=2\pi^6E_6/945`. Consequently
$`g_2=4\pi^4E_4/3`, $`g_3=8\pi^6E_6/27`, and
$`g_2^3-27g_3^2=4096\pi^{12}\Delta`, which is nonzero. The proof transports
`PeriodPair.G` through the lattice basis equivalence and then uses mathlib's
full-pair Eisenstein-sum theorem and exact zeta values.

This is only a lattice-series normalization. It does not construct a quotient
torus, descend $`\wp`, or uniformize an algebraic elliptic curve.

*Status: proved unconditionally.*
:::

:::proposition "prop:lattice-weierstrass-curve" (uses := "prop:lattice-eisenstein-normalization, def:modular-j") (lean := "Heights.deriv_derivWeierstrassP, Heights.latticeWeierstrassCurve, Heights.weierstrassP_on_latticeWeierstrassCurve, Heights.latticeWeierstrassCurve_c4, Heights.latticeWeierstrassCurve_discriminant, Heights.latticeWeierstrassCurve_discriminant_eq_modularDiscriminant, Heights.latticeWeierstrassCurve_j")
Differentiating the cubic Weierstrass relation and using analytic
no-zero-divisors on the connected lattice complement gives the second-order
identity $`\wp''=6\wp^2-g_2/2`; the order-two pole excludes the spurious case
that $`\wp'` vanishes identically.

The lattice invariants define the short Weierstrass curve
$`y^2=x^3-g_2x/4-g_3/4`. Away from the lattice, the differential equation for
$`\wp` proves that $`(\wp(z),\wp'(z)/2)` lies on this curve. Its algebraic
invariants satisfy
$`c_4=12g_2` and
$`\Delta_W=g_2^3-27g_3^2=4096\pi^{12}\Delta(\tau)`, so it is elliptic, and
its algebraic $`j`-invariant is exactly $`j_{\mathrm{mod}}(\tau)`.

This does not descend $`\wp` through $`\mathbb C/L`, handle the lattice points
as projective points at infinity, or prove an arbitrary complex elliptic curve
is uniformized by a lattice.

*Status: proved unconditionally for the explicit curve attached to each
$`\tau\in\mathfrak H`.*
:::

:::proposition "prop:lattice-affine-point-map" (uses := "prop:lattice-weierstrass-curve") (lean := "Heights.LatticeComplement, Heights.LatticeComplement.translate, Heights.latticeAffinePoint, Heights.latticeAffinePoint_pointEquiv, Heights.latticeAffinePointMap, Heights.latticeAffinePointMap_pointEquiv, Heights.add_lattice_notMem_iff, Heights.latticeAffinePoint_add_lattice, Heights.latticeAffinePointMap_translate")
On the complement of the period lattice, $`(\wp(z),\wp'(z)/2)` is packaged as
an actual affine point of the explicit lattice curve. Translation by any
lattice element preserves this pole-free domain, and periodicity of $`\wp` and
$`\wp'` proves that it leaves the packaged point unchanged.

By itself this is not a map on all of $`\mathbb C`, because the lattice points
have not been assigned the point at infinity. The successor construction in
`prop:lattice-quotient-point-map` supplies that set-theoretic extension, but no
analytic or group-theoretic conclusion.

*Status: proved unconditionally on the complement of the lattice.*
:::

:::proposition "prop:lattice-quotient-point-map" (uses := "prop:lattice-affine-point-map") (lean := "Heights.latticePointMap, Heights.latticePointMap_of_mem, Heights.latticePointMap_of_notMem, Heights.latticePointMap_add_lattice, Heights.LatticeQuotient, Heights.latticeQuotientPointMap, Heights.latticeQuotientPointMap_mk, Heights.latticePointMap_zero, Heights.latticePointMap_neg, Heights.latticeQuotientPointMap_zero, Heights.latticeQuotientPointMap_neg")
The point-valued Weierstrass map is extended to all of $`\mathbb C`: lattice
elements are sent to the distinguished point at infinity and non-lattice
elements retain the point $`(\wp(z),\wp'(z)/2)`. The total map is invariant
under lattice translation, so quotient lifting gives a well-defined function
$`\mathbb C/L\to E_\tau(\mathbb C)` that computes as the total map on every
representative. Evenness of $`\wp` and oddness of $`\wp'` also prove that the
origin maps to infinity and complex negation agrees with elliptic-curve
negation, before and after descent.

The descent is not yet a group homomorphism: compatibility with addition has
not been proved. No claim of bijectivity, complex-torus equivalence, or
uniformization of arbitrary curves is made here.

*Status: total extension, set-theoretic quotient descent, and zero/negation
compatibility are proved unconditionally for the explicit lattice curve.*
:::

:::proposition "prop:lattice-quotient-topology" (uses := "prop:lattice-quotient-point-map") (lean := "Heights.latticeQuotientMk, Heights.continuous_latticeQuotientMk, Heights.isOpenMap_latticeQuotientMk, Heights.isQuotientMap_latticeQuotientMk, Heights.latticeQuotientT1Space, Heights.latticeQuotient_nhds_mk")
The additive quotient $`\mathbb C/L` carries mathlib's standard quotient
topology. Its canonical projection from $`\mathbb C` is continuous, open, and
a quotient map. Since the period lattice is closed, the quotient is a
$`T_1` topological additive group. Neighborhoods of a quotient class are the
images of neighborhoods of any chosen representative.

These facts topologize only the source of the descended point map. They do not
put a topology on the algebraic elliptic-curve point type or prove that the
point map is continuous or analytic at its poles, a group homomorphism, a
bijection, or an analytic equivalence.

*Status: the source quotient topology is packaged unconditionally; analytic
uniformization remains open.*
:::

:::proposition "prop:lattice-quotient-compactness" (uses := "prop:lattice-quotient-topology") (lean := "Heights.isCompact_range_latticeQuotientMk, Heights.isCompact_univ_latticeQuotient, Heights.latticeQuotientCompactSpace")
The period lattice is a full $`\mathbb Z`-lattice in the real vector space
$`\mathbb C`. Mathlib's compact-range theorem for continuous lattice-periodic
maps applies to the canonical projection; because that projection is
surjective, its compact range is the whole quotient $`\mathbb C/L`.

This compactness concerns only the source topology. It does not establish
injectivity or bijectivity of the descended point map, compatibility with
addition, a homeomorphism, analyticity, or uniformization.

*Status: the explicit complex lattice quotient is proved compact
unconditionally.*
:::

:::proposition "prop:lattice-curve-topology" (uses := "prop:lattice-weierstrass-curve, prop:lattice-quotient-topology") (lean := "Heights.LatticeCurveAffine, Heights.LatticeCurvePoint, Heights.latticeCurvePointEquiv, Heights.latticeCurvePointHomeomorph, Heights.latticeCurvePointInfinity, Heights.latticeCurvePointOfAffine, Heights.latticeCurvePointHomeomorph_infinity, Heights.latticeCurvePointHomeomorph_affine, Heights.isOpenEmbedding_latticeCurvePointOfAffine, Heights.isClosed_latticeCurveAffine, Heights.latticeCurveAffineLocallyCompactSpace, Heights.latticeCurvePointCompactSpace, Heights.latticeCurvePointT1Space, Heights.latticeCurvePointT4Space")
For the explicit lattice curve only, a named wrapper around the algebraic point
type is given the topology transported from the one-point compactification of
its affine equation locus. The algebraic point equivalence becomes a
homeomorphism, carrying the distinguished point to infinity and affine points
to the open affine chart. The affine Weierstrass equation cuts out a closed,
hence locally compact, subspace of $`\mathbb C^2`. Consequently the wrapped
point space is compact and $`T_4` (in particular Hausdorff and regular), and
its affine chart is an open embedding.

No topology is installed on arbitrary elliptic-curve point types. In
particular, this does not prove continuity or analyticity of the descended
Weierstrass point map at the pole, continuity of the group law, a homeomorphism
$`\mathbb C/L\simeq E_\tau(\mathbb C)`, or arbitrary-curve uniformization.

*Status: the conservative compact Hausdorff target topology is packaged
unconditionally for the explicit lattice curve; analytic uniformization
remains open.*
:::

:::proposition "prop:lattice-affine-point-continuity" (uses := "prop:lattice-affine-point-map, prop:lattice-curve-topology") (lean := "Heights.latticeAffineCoordinateMap, Heights.latticeAffineCurvePointMap, Heights.latticeAffineCoordinateMap_val, Heights.latticeAffineCurvePointMap_eq, Heights.latticeAffineCurvePointMap_homeomorph, Heights.continuous_latticeAffineCoordinateMap, Heights.continuous_latticeAffineCurvePointMap")
On the complement of the period lattice, the explicit point map factors through
the affine equation locus as $`z\mapsto(\wp(z),\wp'(z)/2)`. Differentiability
of both coordinate functions away from the lattice proves continuity of this
coordinate map and hence continuity into the one-point-compactified curve-point
space through its open affine chart.

This is continuity only on the pole-free domain. It does not establish the
limit at a lattice point, continuity of the total or descended map, analytic
extension across infinity, group-law compatibility, bijectivity, or
uniformization.

*Status: pole-free continuity is proved unconditionally for the explicit
lattice curve; the successor `prop:lattice-point-map-continuity` supplies
continuity at infinity.*
:::

:::proposition "prop:lattice-point-map-continuity" (uses := "prop:lattice-affine-point-continuity, prop:lattice-quotient-topology") (lean := "Heights.latticeCurvePointMap, Heights.latticeCurvePointMap_eq, Heights.tendsto_weierstrassP_cocompact_at_lattice, Heights.tendsto_latticeCurvePointMap_homeomorph_at_lattice, Heights.continuousAt_latticeCurvePointMap_of_mem, Heights.continuous_latticeCurvePointMap, Heights.latticeQuotientCurvePointMap, Heights.latticeQuotientCurvePointMap_mk, Heights.continuous_latticeQuotientCurvePointMap")
At each period-lattice point, the order-two pole theorem for $`\wp` shows that
its first coordinate leaves every compact subset of $`\mathbb C`. The first-
coordinate image of a compact subset of the affine equation locus is compact,
so the affine point map leaves every compact subset of that locus and therefore
converges to infinity in its one-point compactification. Together with pole-free
continuity, this proves the total map $`\mathbb C\to E_\tau(\mathbb C)` is
continuous. The quotient-map criterion then proves continuity of its descent
$`\mathbb C/L\to E_\tau(\mathbb C)`.

This is a topological result for the explicit lattice curve. It does not prove
analyticity across infinity, compatibility with addition, bijectivity, a
complex-torus equivalence, or uniformization of arbitrary algebraic curves.

*Status: continuity of the total and descended explicit lattice point maps is
proved unconditionally; the remaining uniformization properties remain open.*
:::

:::proposition "prop:weighted-log-log" (lean := "Heights.weightedLogOneAdd_le, Heights.infinitePlaceWeightedLogOneAdd_bounds, Heights.infinitePlacePosLogAverage_le_normalizedLogHeight, Heights.infinitePlaceLogLogMax_bounds")
The proof isolates Silverman's arithmetic-geometric-mean step as weighted
Jensen for the concave function $`\log(1+x)`. The infinite-place
multiplicities are the weights and sum to $`[K:\mathbb Q]`; positivity of the
finite-place terms lets the archimedean average be bounded by the full
normalized Weil height. Applying the local cutoff identity then gives equation
(11), including its lower bound.

*Status: `Heights.weightedLogOneAdd_le` and the linked infinite-place
specializations are proved unconditionally.*
:::

# Realization interfaces

These interfaces may package missing geometry and arithmetic, but none may
contain a height comparison, a complete height formula for a free real, or
one of the desired inequalities.

:::definition "def:integral-at" (lean := "Heights.IsIntegralAt")
A coefficient lies in the local valuation ring exactly when its multiplicative
valuation is at most $`1`; imposing this on all five Weierstrass coefficients
records that one equation is integral at the chosen prime. This local predicate
lets minimality be discussed without pretending that one equation is globally
minimal.

*Status: the honest local interface `Heights.IsIntegralAt` is formalized; no
existence claim is packaged in it.*
:::

:::definition "def:local-minimal-discriminant-exponent" (uses := "def:integral-at") (lean := "Heights.IsLocalMinimalDiscriminantExponent")
Local minimality is represented by an integral change of variables whose
discriminant valuation is $`\exp(-n)`. Because the valuation is multiplicative,
minimizing the usual additive exponent means maximizing this value among all
integral changes; the maximality field records precisely that condition and no
height inequality.

*Status: the local realization interface
`Heights.IsLocalMinimalDiscriminantExponent` is formalized; its fields do not
assert global existence.*
:::

:::definition "def:global-minimal-discriminant-data" (uses := "def:local-minimal-discriminant-exponent") (lean := "Heights.GlobalMinimalDiscriminantData, Heights.exists_integralModel_change, Heights.nonempty_globalMinimalDiscriminantData, Heights.globalMinimalDiscriminantData")
The minimal-discriminant ideal packages the finite contribution to the height
formula by requiring each prime multiplicity to equal its local minimal
exponent; it need not arise from one globally minimal equation. A product of
localization denominators makes the original equation globally integral over
the ring of integers. Its discriminant bounds every local minimum, so mathlib's
DVR minimal-model theorem and Dedekind ideal factorization assemble the required
ideal. Neither denominator divisibility nor a comparison estimate is stored in
the interface.

*Status: formalized and constructed for every elliptic Weierstrass curve over
every number field.*
:::

:::definition "def:archimedean-period-data" (uses := "def:modular-j") (lean := "Heights.ArchimedeanPeriodData, Heights.nonempty_archimedeanPeriodData_of_modularJ_surjective")
A period ratio is chosen in the standard fundamental domain so that the
$`\mathrm{SL}_2(\mathbb Z)` ambiguity is removed and the uniform modular bounds
apply directly. Equality of modular and embedded algebraic $`j` is exactly the
compatibility needed by the present height formula, but is deliberately weaker
than constructing an analytic torus isomorphism. Modular invariance reduces
existence of this data to surjectivity of `modularJ`.

*Status: `Heights.ArchimedeanPeriodData` and
`Heights.nonempty_archimedeanPeriodData_of_modularJ_surjective` formalize the
interface and reduction; modular-$`j` surjectivity remains open.*
:::

:::definition "def:reduced-principal-ideal-data" (lean := "Heights.ReducedPrincipalIdealData, Heights.exists_reducedPrincipalIdealData, Heights.reducedPrincipalIdealData")
Factoring the principal fractional ideal separates positive prime exponents
into a numerator and negative exponents into a coprime denominator. This is the
finite-place input to Silverman's equation (10); the $`x=0` convention uses
numerator $`0` and unit denominator so that curves with $`j=0` remain covered.
The structure stores only this factorization, while the height identity is a
separate theorem.

*Status: `Heights.exists_reducedPrincipalIdealData` proves unconditional
existence and `Heights.reducedPrincipalIdealData` fixes a canonical choice.*
:::

# Certificate-level height and comparisons

:::definition "def:silverman-height" (uses := "def:silverman-modular-discriminant, def:global-minimal-discriminant-data, def:archimedean-period-data") (lean := "Heights.silvermanHeight, Heights.silvermanHeightOfPeriods, Heights.silvermanHeight_archimedean_log_arg_pos, Heights.silvermanHeight_denominator_pos")
Silverman's formula balances the finite bad-reduction contribution
$`\log N(\Delta_{\min})` against the archimedean norm of the discriminant
differential, $`\log(|\Delta_{\mathrm{Silv}}(\tau)|\operatorname{Im}(\tau)^6)`.
The factor $`12[K:\mathbb Q]` reflects use of the twelfth tensor power of the
invariant-differential line. Here this expression is defined only from genuine
minimal-ideal and period certificates, not renamed as an independently
constructed Arakelov height.

*Status: `Heights.silvermanHeight` is formalized at certificate level and
`Heights.silvermanHeightOfPeriods` supplies its now-constructed finite data;
positivity of every logarithm argument and denominator is proved, but no
Arakelov identification is claimed.*
:::

:::proposition "prop:proposition-1-1-certified" (uses := "def:silverman-height")
With genuine minimal-discriminant and period certificates, the preceding
formula is the elliptic-curve height formula corresponding to Proposition
1.1. The finite data is now constructed; this node does not assert
unconditional period existence or an Arakelov/Hodge-bundle construction.

*Status: not started (conditional/certificate-level target).*
:::

:::definition "def:certified-semistability" (uses := "def:global-minimal-discriminant-data") (lean := "Heights.IsSemistable, Heights.denominator_dvd_minimalDiscriminant, Heights.unstableMinimalDiscriminant_eq_top_of_semistable")
Semistability is defined place by place as good or multiplicative reduction for
a certified minimal local model. The unconditionally constructed reduced
$`j`-denominator is proved to divide the minimal-discriminant ideal, defining
its canonical complement without a reduced-ideal hypothesis, and semistability
is proved to make that complement the unit ideal.

*Status: formalized and proved; global minimal-discriminant realization data
is now constructed over every number field.*
:::

:::theorem "thm:proposition-2-1-certified" (uses := "prop:rational-height-arithmetic, prop:reduced-principal-ideals, prop:modular-estimates, prop:weighted-log-log, def:silverman-height") (lean := "Heights.comparisonExpression_eq_archimedeanAverage, Heights.correctedComparison_bounds_of_modular_estimates, Heights.proposition_2_1_certified, Heights.proposition_2_1_of_periods")
One pair of absolute modular-estimate constants, quantified before the number
field, curve, and remaining realization data, gives Silverman's two-sided
Proposition 2.1 estimate for normalized $`j`-height, the canonical unstable
ideal, and `silvermanHeight`. The theorem no longer assumes reduced
principal-ideal data or analytic estimates: the unconditional fundamental-
domain theorems supply the two absolute constants directly.

*Status: proved. `Heights.proposition_2_1_of_periods` instantiates the
constructed minimal-discriminant data over every number field, leaving only
compatible periods; this is not an all-curves Arakelov Faltings-height theorem.*
:::

:::theorem "thm:proposition-2-1-semistable-certified" (uses := "thm:proposition-2-1-certified, def:certified-semistability") (lean := "Heights.semistable_abs_comparison_of_corrected_bounds, Heights.proposition_2_1_semistable_certified, Heights.proposition_2_1_semistable_of_periods")
After proving certified semistability makes the unstable ideal trivial, derive
the absolute-value specialization comparing normalized $`j`-height with
$`12\,\mathrm{silvermanHeight}`.

*Status: proved with the constructed minimal-discriminant data, compatible
periods, and certified semistability; no analytic estimate remains as a
hypothesis.*
:::

The repository does not presently claim period construction, complex
uniformization, an Arakelov Faltings height, or unconditional all-curves
Proposition 2.1. Global minimal-discriminant data is unconditional over every
number field, so `ArchimedeanPeriodData` is the sole remaining realization
input. The precise archimedean feasibility findings are recorded in
`Plans/ArchimedeanUniformizationFeasibility.md`.

{blueprint_graph}
{blueprint_summary}
