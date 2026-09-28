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

## Source and copyright boundary

> Copyrighted source scans and OCR extracts are excluded from this public
> repository and its history. This blueprint cites the published literature and
> does not reproduce substantial source text.

This blueprint tracks the program specified in `Plans/HeightsSpec.md`. There
are two deliberately separate layers:

* *Unconditional results* are proved from mathlib without externally supplied
  elliptic-uniformization certificates.
* *Certificate interfaces* expose explicit local-minimal-model and
  archimedean-parameter realization data. Reduced principal-ideal, global
  minimal, and archimedean data are now all constructed unconditionally. The
  archimedean data algebraically realizes every embedded curve, but these
  interfaces still do not construct an Arakelov Faltings height.

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

:::definition "def:modular-j" (lean := "Heights.modularJ, Heights.modularJ_mul_discriminant, Heights.modularJ_eq_zero_iff, Heights.modularJ_smul, Heights.exists_mem_fd_modularJ_eq_of_surjective, Heights.exists_smul_eq_of_modularJ_eq, Heights.silvermanModularDiscriminant_norm_mul_im_pow_eq_of_modularJ_eq")
The quotient $`E_4^3/\Delta` has leading term $`q^{-1}` and is therefore the
$`q^{-1}+744+\cdots` modular invariant used in the height estimates, with no
extra factor of $`1728`. The $`E_4,E_6,\Delta` identity checks this convention,
while modular invariance permits a preimage to be moved into the standard
fundamental domain.

*Status: formalized unconditionally. Surjectivity is complemented by a proof
that equal values lie in one $`\mathrm{SL}_2(\mathbb Z)` orbit; the latter uses
homothety and rigidity of the associated period lattices. Consequently the
Petersson-normalized absolute discriminant depends only on $`j`.
`prop:modular-estimates` proves the required global bounds.*
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

:::proposition "prop:weierstrass-principal-parts" (lean := "Heights.tendsto_weierstrassP_sub_inv_sq_zero, Heights.tendsto_derivWeierstrassP_add_two_div_cube_zero, Heights.tendsto_sq_mul_weierstrassP_zero, Heights.tendsto_cube_mul_derivWeierstrassP_zero, Heights.tendsto_sq_mul_weierstrassP_at_lattice, Heights.tendsto_cube_mul_derivWeierstrassP_at_lattice, Heights.tendsto_weierstrass_secant_addX_zero, Heights.tendsto_weierstrass_secant_addY_zero")
For every complex period pair and every period $`l`, the singular summands in
mathlib's definitions give the normalized principal-part limits
$`
  (z-l)^2\wp(z)\longrightarrow 1,
  \qquad
  (z-l)^3\wp'(z)\longrightarrow -2.
`
At the origin, the regular remainders
$`\wp(z)-z^{-2}` and $`\wp'(z)+2z^{-3}` tend to zero.

These cancellations also show that for arbitrary $`a,b\in\mathbb C` both
secant-formula coordinate candidates extend across $`z=0` with values $`a`
and $`b/2`. These are the local coordinate cancellations required at the
point at infinity. This proposition alone is not the global Weierstrass
addition theorem; that theorem is proved in the later addition node.

*Status: proved unconditionally.*
:::

:::proposition "prop:weierstrass-secant-differential" (uses := "prop:weierstrass-principal-parts, prop:lattice-weierstrass-curve") (lean := "Heights.weierstrassSecantSlope, Heights.weierstrassSecantAddX, Heights.weierstrassSecantAddY, Heights.hasDerivAt_weierstrassSecantSlope, Heights.hasDerivAt_weierstrassSecantAddX, Heights.hasDerivAt_weierstrassSecantAddY, Heights.weierstrassSecantAddXAtZero, Heights.weierstrassSecantAddYAtZero, Heights.analyticAt_weierstrassSecantAddXAtZero, Heights.analyticAt_weierstrassSecantAddYAtZero")
Suppose $`b^2=4a^3-g_2a-g_3`, and let $`X,Y` be the two secant-law
candidates for adding $`(\wp(z),\wp'(z)/2)` to $`(a,b/2)`. Away from the
period lattice and vertical secants, direct differentiation gives
$`
  X'=2Y, \qquad Y'=3X^2-g_2/4.
`
Consequently $`(X,2Y)` satisfies the same polynomial first-order ODE as
$`(\wp,\wp')`. Installing the preceding limiting values at zero makes both
candidates analytic there. This is the local ODE input used by the later
addition theorem, where ODE uniqueness and global analytic continuation do
identify $`X,Y` with the coordinates at $`z+w`.

*Status: proved on the pole-free, nonvertical secant domain.*
:::

:::proposition "prop:lattice-weierstrass-curve" (uses := "prop:lattice-eisenstein-normalization, prop:weierstrass-principal-parts, def:modular-j") (lean := "Heights.deriv_derivWeierstrassP, Heights.latticeWeierstrassCurve, Heights.weierstrassP_on_latticeWeierstrassCurve, Heights.latticeWeierstrassCurve_c4, Heights.latticeWeierstrassCurve_discriminant, Heights.latticeWeierstrassCurve_discriminant_eq_modularDiscriminant, Heights.latticeWeierstrassCurve_j")
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

:::proposition "prop:weierstrass-fibers" (uses := "prop:lattice-weierstrass-curve") (lean := "Heights.sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq, Heights.weierstrassP_eq_iff_sub_mem_or_add_mem, Heights.weierstrassP_deriv_eq_iff_sub_mem")
The second-order equation makes $`(\wp,\wp')` a solution of a locally
Lipschitz first-order system. Real ODE uniqueness and the complex identity
theorem show that two equal phase-space values have equal translates. The
order-two pole then forces the translation difference to be a period.
Consequently
$`\wp(z)=\wp(w)` exactly when $`z\equiv w` or $`z\equiv-w\pmod L`, and the
ordered pair $`(\wp,\wp')` separates classes modulo $`L`.

This is the injective half of the analytic parameterization, not the
Weierstrass addition theorem. The successor Liouville argument proves the
complementary value-existence and curve-point surjectivity statements.

*Status: proved unconditionally away from the period lattice.*
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

:::proposition "prop:lattice-quotient-point-map" (uses := "prop:lattice-affine-point-map, prop:weierstrass-fibers") (lean := "Heights.latticePointMap, Heights.latticePointMap_of_mem, Heights.latticePointMap_of_notMem, Heights.latticePointMap_add_lattice, Heights.LatticeQuotient, Heights.latticeQuotientPointMap, Heights.latticeQuotientPointMap_mk, Heights.latticePointMap_zero, Heights.latticePointMap_neg, Heights.latticeQuotientPointMap_zero, Heights.latticeQuotientPointMap_neg, Heights.latticePointMap_eq_iff_sub_mem, Heights.latticeQuotientPointMap_injective, Heights.exists_notMem_lattice_weierstrassP_eq, Heights.weierstrassP_surjective, Heights.latticePointMap_surjective, Heights.latticeQuotientPointMap_surjective, Heights.latticePointMap_add, Heights.latticeQuotientPointMapAddEquiv")
The point-valued Weierstrass map is extended to all of $`\mathbb C`: lattice
elements are sent to the distinguished point at infinity and non-lattice
elements retain the point $`(\wp(z),\wp'(z)/2)`. The total map is invariant
under lattice translation, so quotient lifting gives a well-defined function
$`\mathbb C/L\to E_\tau(\mathbb C)` that computes as the total map on every
representative. Evenness of $`\wp` and oddness of $`\wp'` also prove that the
origin maps to infinity and complex negation agrees with elliptic-curve
negation, before and after descent. The fiber theorem further proves that the
total map identifies exactly points differing by a period, so the descended
map is injective. For surjectivity, if `℘` omitted a finite value `a`, then
`1/(℘-a)`, extended by zero at the lattice, would be an entire doubly-periodic
function. Compactness of a fundamental parallelogram and Liouville's theorem
make it constant, contradicting its nonzero value away from the lattice. Thus
`℘` attains every finite value away from its poles. The curve equation and the
two possible signs of `℘′` then prove that both the total and descended point
maps are surjective.

The global addition theorem proves that this descent is also a group
homomorphism and packages it as an additive equivalence. A later
variable-change theorem transports it to every embedded input curve. Analytic
equivalence remains open.

*Status: total extension, quotient descent, zero/negation compatibility,
bijectivity, and (in the later addition node) additivity are proved
unconditionally for the explicit lattice curve.*
:::

:::proposition "prop:lattice-quotient-topology" (uses := "prop:lattice-quotient-point-map") (lean := "Heights.latticeQuotientMk, Heights.continuous_latticeQuotientMk, Heights.isOpenMap_latticeQuotientMk, Heights.isQuotientMap_latticeQuotientMk, Heights.isAddQuotientCoveringMap_latticeQuotientMk, Heights.isCoveringMap_latticeQuotientMk, Heights.latticeQuotientT1Space, Heights.latticeQuotient_nhds_mk")
The additive quotient $`\mathbb C/L` carries mathlib's standard quotient
topology. Its canonical projection from $`\mathbb C` is continuous, open, and
a quotient map. Discreteness of the period lattice further makes it the
quotient covering map for lattice translations. Since the period lattice is
closed, the quotient is a $`T_1` topological additive group. Neighborhoods of
a quotient class are the images of neighborhoods of any chosen representative.

These facts alone topologize only the source of the descended point map. Later
nodes prove continuity, bijectivity, and additivity after separately
constructing the explicit target topology. The next node adds a complex atlas
to this source topology; no intrinsic analytic equivalence with the curve
follows from the topology alone.

*Status: the source quotient topology and covering map are packaged
unconditionally.*
:::

:::proposition "prop:lattice-quotient-manifold" (uses := "prop:lattice-quotient-topology") (lean := "Heights.latticeQuotientChartedSpace, Heights.latticeQuotientComplexManifold, Heights.latticeQuotientLocalInverse_mem_maximalAtlas, Heights.isLocalDiffeomorph_latticeQuotientMk, Heights.contMDiff_latticeQuotientMk")
The covering-local-inverse charts equip $`\mathbb C/L` with a one-dimensional
complex-manifold structure on its existing quotient topology. On an overlap,
two lifted coordinates differ locally by a fixed lattice element, so every
transition map is locally a complex translation. Every local inverse supplied
by the covering belongs to the resulting holomorphic maximal atlas.

The canonical projection $`\mathbb C\to\mathbb C/L` is therefore a local
complex-analytic diffeomorphism, in particular a holomorphic map. This
construction is intrinsic to the lattice quotient: it does not transport an
atlas from a curve uniformization. It does not yet package the descended form
$`dz` or prove that the Weierstrass point map is analytic.

*Status: the source complex-manifold structure and locally biholomorphic
quotient projection are proved unconditionally.*
:::

:::proposition "prop:lattice-quotient-compactness" (uses := "prop:lattice-quotient-topology") (lean := "Heights.isCompact_range_latticeQuotientMk, Heights.isCompact_univ_latticeQuotient, Heights.latticeQuotientCompactSpace")
The period lattice is a full $`\mathbb Z`-lattice in the real vector space
$`\mathbb C`. Mathlib's compact-range theorem for continuous lattice-periodic
maps applies to the canonical projection; because that projection is
surjective, its compact range is the whole quotient $`\mathbb C/L`.

This compactness concerns only the source topology. Later results combine it
with continuity and bijectivity to obtain a homeomorphism and prove
compatibility with addition. The target topology is now constructed directly
from every nonsingular complex Weierstrass equation in the next node.
Analyticity remains separate.

*Status: the explicit complex lattice quotient is proved compact
unconditionally.*
:::

:::proposition "prop:complex-weierstrass-topology" (lean := "Heights.ComplexWeierstrassAffine, Heights.ComplexWeierstrassPoint, Heights.complexWeierstrassPointEquiv, Heights.complexWeierstrassPointHomeomorph, Heights.complexWeierstrassPointInfinity, Heights.complexWeierstrassPointOfAffine, Heights.complexWeierstrassPointHomeomorph_infinity, Heights.complexWeierstrassPointHomeomorph_affine, Heights.isOpenEmbedding_complexWeierstrassPointOfAffine, Heights.isClosed_complexWeierstrassAffine, Heights.complexWeierstrassAffineLocallyCompactSpace, Heights.complexWeierstrassPointCompactSpace, Heights.complexWeierstrassPointT1Space, Heights.complexWeierstrassPointT4Space, Heights.variableChangeAffineLocusHomeomorph, Heights.onePointHomeomorph, Heights.variableChangePointHomeomorph, Heights.variableChangePointHomeomorph_apply, Heights.variableChangePointHomeomorph_symm_apply")
For every nonsingular complex Weierstrass equation, a named wrapper around its
algebraic point type is topologized directly from the one-point
compactification of its affine equation locus. The equation locus is closed
and locally compact in $`\mathbb C^2`, so the point space is compact and
$`T_4`, with an open affine chart.

An admissible variable change gives mutually inverse polynomial homeomorphisms
of the two affine loci. Extending them by fixing infinity proves that its
existing algebraic point map is a homeomorphism between the two point
topologies. These topologies are independently equation-defined; they are not
transported from a selected lattice uniformization.

*Status: intrinsic compact Hausdorff topology and variable-change invariance
are proved for every nonsingular complex Weierstrass equation. No complex
atlas on the compact point type or curve-level analyticity is claimed.*
:::

:::proposition "prop:complex-weierstrass-finite-manifold" (uses := "prop:complex-weierstrass-topology") (lean := "Heights.complexWeierstrassEquation, Heights.complexWeierstrassAffine_derivative_ne_zero, Heights.complexWeierstrassImplicitYChart, Heights.complexWeierstrassImplicitXChart, Heights.contDiffAt_complexWeierstrassImplicitYChart_symm_coe_of_mem, Heights.contDiffAt_complexWeierstrassImplicitXChart_symm_coe_of_mem, Heights.contDiffOn_complexWeierstrassImplicitYChart_transition, Heights.contDiffOn_complexWeierstrassImplicitYChart_ImplicitXChart_transition, Heights.contDiffOn_complexWeierstrassImplicitXChart_ImplicitYChart_transition, Heights.contDiffOn_complexWeierstrassImplicitXChart_transition, Heights.complexWeierstrassAffineChartAt, Heights.complexWeierstrassAffineChartedSpace, Heights.complexWeierstrassAffineIsManifold, Heights.contMDiff_complexWeierstrassAffine_coe, Heights.contMDiff_complexWeierstrassAffine_of_contMDiff_coe")
At every point of a nonsingular affine complex Weierstrass equation, at least
one equation partial derivative is nonzero. Restricting the corresponding
ambient implicit-function neighborhood to that noncritical locus gives a chart
whose coordinate is $`x` or $`y`. Its inverse is holomorphic at every point of
the chart target.

Transitions between charts using the same coordinate are identities. The two
mixed transitions are the appropriate component of an analytic chart inverse.
Thus all transitions are holomorphic on their whole overlaps, and these charts
equip the affine equation locus with a one-dimensional complex-manifold
structure on its existing subtype topology. No lattice parameter or transported
atlas enters the construction.

*Status: the finite affine complex atlas and manifold are proved
unconditionally. The separate projective analytic branch at infinity is now
also constructed, but its gluing to the compact point topology remains open.*
:::

:::proposition "prop:complex-weierstrass-infinity-branch" (uses := "prop:complex-weierstrass-topology, prop:complex-weierstrass-finite-manifold") (lean := "Heights.complexWeierstrassInfinityEquation, Heights.complexWeierstrassInfinityImplicitV, Heights.contDiffAt_complexWeierstrassInfinityImplicitV, Heights.complexWeierstrassInfinityAmbientHomeomorph, Heights.complexWeierstrassInfinityBranchChart, Heights.complexWeierstrassInfinityBranchOrigin_mem_chart_source, Heights.complexWeierstrassInfinityBranchChart_symm_coe_of_mem, Heights.contDiffAt_complexWeierstrassInfinityBranchChart_symm_coe_of_mem, Heights.complexWeierstrassInfinityBranch_snd_eq_zero_iff, Heights.complexWeierstrassInfinityPuncturedHomeomorph, Heights.complexWeierstrassInfinityBranchToOnePoint, Heights.continuousAt_complexWeierstrassInfinityBranchToOnePoint_origin, Heights.contDiffOn_complexWeierstrassInfinity_toAffine")
In the projective chart $`Y\ne0`, put $`u=X/Y` and $`v=Z/Y`. The homogenized
Weierstrass equation has $`v`-derivative one at the point at infinity
$`(u,v)=(0,0)`. The complex implicit-function theorem therefore gives a local
holomorphic branch $`v=v(u)`. Restricting the ambient inverse-function
neighborhood to the equation's zero fiber packages this branch as an explicit
open partial homeomorphism with coordinate $`u` and holomorphic inverse.

The origin is the only branch point with $`v=0`. On the punctured branch, the
formulas $`(x,y)=(u/v,1/v)` give a homeomorphism to the $`y\ne0` affine locus,
with holomorphic rational overlap maps in both directions. Sending the branch
origin to infinity and using this overlap elsewhere defines a map to the
one-point compactification. It is continuous at the origin because compact
affine subsets have bounded $`y`-coordinate whereas $`y=1/v` diverges.

*Status: the independent projective analytic germ, its affine overlap, and one
direction of the topology comparison are proved. Proving local openness (and
hence a homeomorphism onto a neighborhood of infinity), then assembling the
compact atlas, remain open; no compact-curve manifold is claimed.*
:::

:::proposition "prop:variable-change-ambient-biholomorph" (uses := "prop:complex-weierstrass-topology, prop:complex-weierstrass-finite-manifold") (lean := "Heights.variableChangeAffineAmbientEquiv, Heights.variableChangeAffineAmbientBiholomorph, Heights.variableChangeAffineAmbientBiholomorph_apply, Heights.variableChangeAffineAmbientBiholomorph_symm_apply, Heights.variableChangeAffineLocusHomeomorph_coe, Heights.variableChangeAffineLocusHomeomorph_symm_coe, Heights.contMDiff_variableChangeAffineLocusHomeomorph, Heights.contMDiff_variableChangeAffineLocusHomeomorph_symm, Heights.variableChangeAffineLocusBiholomorph")
For every admissible complex change of Weierstrass variables, the forward
coordinate polynomial
$`(x,y)\mapsto(u^2x+r,u^3y+u^2sx+t)` and its explicit inverse form a global
biholomorphism of $`\mathbb C^2`. The affine-locus homeomorphism between the
changed equations is exactly the restriction of this ambient biholomorphism,
in both directions.

The intrinsic finite manifold embeds analytically in its ambient coordinate
plane, and maps into the equation subtype are analytic whenever both ambient
coordinates are. Applying this criterion packages the affine-locus
homeomorphism and its inverse as a biholomorphism for the independently
constructed implicit-function atlases. This node does not extend that result
through the point at infinity.

*Status: the affine variable change is proved biholomorphic both ambiently and
between the intrinsic finite manifolds; the infinity argument remains open.*
:::

:::proposition "prop:lattice-curve-topology" (uses := "prop:lattice-weierstrass-curve, prop:lattice-quotient-topology, prop:complex-weierstrass-topology") (lean := "Heights.LatticeCurveAffine, Heights.LatticeCurvePoint, Heights.latticeCurvePointEquiv, Heights.latticeCurvePointHomeomorph, Heights.latticeCurvePointInfinity, Heights.latticeCurvePointOfAffine, Heights.latticeCurvePointHomeomorph_infinity, Heights.latticeCurvePointHomeomorph_affine, Heights.isOpenEmbedding_latticeCurvePointOfAffine, Heights.isClosed_latticeCurveAffine, Heights.latticeCurveAffineLocallyCompactSpace, Heights.latticeCurvePointCompactSpace, Heights.latticeCurvePointT1Space, Heights.latticeCurvePointT4Space")
The earlier lattice-specific topology API is retained as the specialization of
the arbitrary-equation construction to the explicit lattice curve. Its point
space is compact and $`T_4`, and the affine chart is an open embedding. The
later point-map theorem combines this topology with bijectivity to obtain the
explicit topological uniformization.

*Status: the legacy lattice topology is recovered from the general intrinsic
topology. Analytic uniformization remains open.*
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

:::proposition "prop:lattice-point-map-continuity" (uses := "prop:lattice-affine-point-continuity, prop:lattice-quotient-topology, prop:lattice-quotient-compactness, prop:lattice-quotient-point-map") (lean := "Heights.latticeCurvePointMap, Heights.latticeCurvePointMap_eq, Heights.tendsto_weierstrassP_cocompact_at_lattice, Heights.tendsto_latticeCurvePointMap_homeomorph_at_lattice, Heights.continuousAt_latticeCurvePointMap_of_mem, Heights.continuous_latticeCurvePointMap, Heights.latticeQuotientCurvePointMap, Heights.latticeQuotientCurvePointMap_mk, Heights.continuous_latticeQuotientCurvePointMap, Heights.isClosedEmbedding_latticeQuotientCurvePointMap, Heights.latticeQuotientCurvePointHomeomorph, Heights.latticeQuotientCurvePointHomeomorph_apply")
At each period-lattice point, the order-two pole theorem for $`\wp` shows that
its first coordinate leaves every compact subset of $`\mathbb C`. The first-
coordinate image of a compact subset of the affine equation locus is compact,
so the affine point map leaves every compact subset of that locus and therefore
converges to infinity in its one-point compactification. Together with pole-free
continuity, this proves the total map $`\mathbb C\to E_\tau(\mathbb C)` is
continuous. The quotient-map criterion then proves continuity of its descent
$`\mathbb C/L\to E_\tau(\mathbb C)`. Since the fiber theorem makes this descent
injective, compactness of the source and Hausdorffness of the target strengthen
it to a closed topological embedding. The Liouville surjectivity theorem then
makes this embedding onto, yielding a homeomorphism
$`\mathbb C/L\simeq E_\tau(\mathbb C)` for the explicitly attached curve.

This is a topological result for the explicit lattice curve. It does not prove
analyticity across infinity or compatibility with addition. Later algebraic
results prove addition compatibility and transport the resulting additive
equivalence to arbitrary embedded complex elliptic curves. Those target curves
now carry independently equation-defined topologies, and admissible variable
changes are homeomorphisms for them, but no complex analyticity is proved.

*Status: continuity, bijectivity, closed-embedding status, and the resulting
topological equivalence are proved unconditionally for the descended explicit
lattice point map. Group compatibility is proved separately; analyticity
remains open.*
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

:::definition "def:archimedean-period-data" (uses := "def:modular-j") (lean := "Heights.ArchimedeanPeriodData, Heights.modularJ_surjective, Heights.nonempty_archimedeanPeriodData, Heights.archimedeanPeriodData")
A period ratio is chosen in the standard fundamental domain so that the
$`\mathrm{SL}_2(\mathbb Z)` ambiguity is removed and the uniform modular bounds
apply directly. Equality of modular and embedded algebraic $`j` is exactly the
compatibility needed by the present height formula. Modular invariance reduces
existence of this minimal data to surjectivity of `modularJ`.

*Status: formalized and constructed for every elliptic curve over a number
field. `Heights.modularJ_surjective` proves the analytic input by an
open-and-closed image argument. The data does not store an integration
construction, but the next node proves it algebraically realizes the embedded
curve.*
:::

:::proposition "prop:archimedean-algebraic-realization" (uses := "def:archimedean-period-data, prop:lattice-weierstrass-curve, prop:lattice-quotient-point-map, prop:variable-change-ambient-biholomorph") (lean := "Heights.variableChange_invariantDifferentialDenominator, Heights.variableChange_invariantDifferentialCoefficient, Heights.ArchimedeanPeriodData.exists_variableChange_to_latticeCurve, Heights.ArchimedeanPeriodData.variableChangeToLatticeCurve, Heights.ArchimedeanPeriodData.variableChangeToLatticeCurve_smul, Heights.ArchimedeanPeriodData.variableChangeToLatticeCurve_differentialDenominator, Heights.ArchimedeanPeriodData.variableChangeToLatticeCurve_differentialCoefficient, Heights.ArchimedeanPeriodData.latticeCurvePointAddEquiv, Heights.ArchimedeanPeriodData.latticeQuotientToEmbeddedPointAddEquiv")
Over the separably closed field $`\mathbb C`, elliptic Weierstrass curves with
the same $`j`-invariant differ by an admissible change of variables. Therefore
each selected lattice curve is algebraically isomorphic to the base change of
the input curve along the corresponding infinite-place embedding: twists do
not survive this base change. The coordinate calculation also shows that
$`2y+a_1x+a_3` scales by $`u^3`; together with the $`u^2` scaling of the
x-coordinate derivative, this is the usual $`u^{-1}` invariant-differential
factor. The documented coordinate map is proved to preserve mathlib's affine
group law and is packaged as an additive equivalence. Composing it with the
explicit lattice equivalence gives
$`\mathbb C/L\simeq E(\mathbb C)` as additive groups for every embedded input
curve represented by the period data.

*Status: proved. This is an actual algebraic variable change and point-level
additive equivalence, not merely an abstract equality of invariants. The
arbitrary target now has its independently equation-defined compact Hausdorff
topology, variable changes are homeomorphisms, and their ambient affine
coordinate maps are biholomorphic. A complex curve atlas, analyticity through
infinity, invariant-differential integration, and an Arakelov metric are not
yet formalized.*
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

# Formula-defined height and comparisons

:::definition "def:silverman-height" (uses := "def:silverman-modular-discriminant, def:global-minimal-discriminant-data, prop:archimedean-algebraic-realization") (lean := "Heights.silvermanHeight, Heights.silvermanHeight_periodData_independent, Heights.silvermanHeightOfPeriods, Heights.silvermanHeightOfCurve, Heights.silvermanHeightOfPeriods_eq_silvermanHeightOfCurve, Heights.silvermanHeight_archimedean_log_arg_pos, Heights.silvermanHeight_denominator_pos")
Silverman's formula balances the finite bad-reduction contribution
$`\log N(\Delta_{\min})` against the archimedean norm of the discriminant
differential, $`\log(|\Delta_{\mathrm{Silv}}(\tau)|\operatorname{Im}(\tau)^6)`.
The factor $`12[K:\mathbb Q]` reflects use of the twelfth tensor power of the
invariant-differential line. Here this expression is defined only from genuine
minimal-ideal and period certificates, not renamed as an independently
constructed Arakelov height.

*Status: formalized. `Heights.silvermanHeightOfCurve` supplies the constructed
finite and archimedean data. Equal modular $`j`-values are proved to lie in one
$`\mathrm{SL}_2(\mathbb Z)` orbit, so the Petersson-normalized discriminant and
hence the formula are independent of that choice. The parameter algebraically
realizes the embedded curve, and every logarithm argument and denominator is
positive. Period integration and an Arakelov identification remain unproved.*
:::

:::proposition "prop:proposition-1-1-certified" (uses := "def:silverman-height")
The preceding expression is the formula corresponding to Proposition 1.1.
Both formula-level data interfaces are constructed, and the selected parameter
has an algebraic/additive realization. A stronger theorem would identify this
expression with an independently constructed Arakelov/Hodge-bundle height; no
such object is yet available.

*Status: formula instantiated for every curve; independent Arakelov
identification remains beyond the current formalization.*
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

:::theorem "thm:proposition-2-1-certified" (uses := "prop:rational-height-arithmetic, prop:reduced-principal-ideals, prop:modular-estimates, prop:weighted-log-log, def:silverman-height") (lean := "Heights.comparisonExpression_eq_archimedeanAverage, Heights.correctedComparison_bounds_of_modular_estimates, Heights.proposition_2_1_certified, Heights.proposition_2_1_of_periods, Heights.proposition_2_1")
One pair of absolute modular-estimate constants, quantified before the number
field, curve, and (in the certified form) realization data, gives Silverman's
two-sided Proposition 2.1 estimate for normalized $`j`-height, the canonical
unstable ideal, and `silvermanHeight`. The theorem no longer assumes reduced
principal-ideal data or analytic estimates: the unconditional fundamental-
domain theorems supply the two absolute constants directly.

*Status: proved. `Heights.proposition_2_1` instantiates both constructed data
interfaces over every number field and curve for `silvermanHeightOfCurve`.
This is still not an Arakelov Faltings-height theorem.*
:::

:::theorem "thm:proposition-2-1-semistable-certified" (uses := "thm:proposition-2-1-certified, def:certified-semistability") (lean := "Heights.semistable_abs_comparison_of_corrected_bounds, Heights.proposition_2_1_semistable_certified, Heights.proposition_2_1_semistable_of_periods, Heights.proposition_2_1_semistable")
After proving certified semistability makes the unstable ideal trivial, derive
the absolute-value specialization comparing normalized $`j`-height with
$`12\,\mathrm{silvermanHeight}`.

*Status: proved with both constructed formula-level data interfaces and
certified semistability; no analytic estimate or realization certificate
remains as a theorem argument.*
:::

:::theorem "thm:velu-product" (lean := "Heights.Velu.xOf_add_add_xOf_sub, Heights.Velu.xOf_add_half_sum, Heights.Velu.prod_mul_sum_sub_sum")
For a Weierstrass curve over a field of characteristic $`\neq 2` and a finite
subgroup $`H` without points of order $`2`, Vélu's $`x`-map
$`P \mapsto \sum_{Q\in H} x(P+Q) - \sum_{Q\in H\setminus 0} x(Q)` depends on
$`x(P)` only (the pair identity), and for $`P, R \notin H` with $`2R \notin H`,
$`\prod_{Q\in H\setminus0}(x(P)-x(Q))\,(\sum_{Q\in H}x(P+Q)-\sum_{Q\in H}x(R+Q))
= \prod_{Q\in H}(x(P)-x(R+Q))`.

*Status: proved (identities between coordinates of points; no quotient curve is
constructed).*
:::

:::theorem "thm:torsion-x-bound" (uses := "prop:archimedean-algebraic-realization") (lean := "Heights.norm_weierstrassP_le, Heights.norm_weierstrassP_torsion_le, Heights.norm_x_sub_r_le, Heights.exists_torsion_x_bound")
For an elliptic curve $`W` over $`\mathbb{C}` and an affine $`N`-torsion point
$`(x,y)`, $`\|x + b_2/12\|^6 \le A\,\|\Delta_W\|\max(\|j_W\|,1)
(2N^2 + B(\log\max(\|j_W\|,e)+1)^2)^6` with absolute constants $`A, B`.

*Status: proved from the lattice uniformization, the lattice-sum bound for
$`\wp` on the fundamental parallelogram, and the fundamental-domain
comparisons for $`\Delta` and $`\operatorname{Im}\tau`.*
:::

The repository proves modular-$`j` surjectivity, constructs
`ArchimedeanPeriodData`, and obtains an all-curves comparison for the
formula-defined `silvermanHeightOfCurve`. It also gives topological and
additive uniformization of each explicit lattice curve. Same-$`j`
classification now supplies an actual algebraic variable change from that
lattice curve to every embedded input curve, eliminating the twisting caveat;
the induced point map is packaged as an additive equivalence and composed with
the lattice quotient equivalence. It does not topologize the arbitrary target
or package this as an analytic point equivalence, define periods by integrating
an invariant differential, or construct an Arakelov Faltings height. The precise
archimedean findings are recorded in
`Plans/ArchimedeanUniformizationFeasibility.md` and the focused follow-up
`Plans/AnalyticPeriodFeasibility.md`.

{blueprint_graph}
{blueprint_summary}
