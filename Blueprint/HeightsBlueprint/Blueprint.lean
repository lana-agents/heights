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
For a number field $`K`, the absolute logarithmic height is defined by
$`h_K(x)=\operatorname{logHeight}_1(x)/[K:\mathbb Q]`. The division by the
field degree is essential. Its nonnegativity is proved in
`Heights.normalizedLogHeight_nonneg`.

*Status: formalized unconditionally.*
:::

:::definition "def:log-ideal-norm" (lean := "Heights.logIdealNorm, Heights.absNorm_pos_of_ne_bot, Heights.logIdealNorm_nonneg")
For a nonzero integral ideal $`I`, $`\log N(I)` is defined using
`Ideal.absNorm`. The accompanying lemmas prove strict positivity of the norm
and nonnegativity of its logarithm from $`I\ne 0`.

*Status: formalized unconditionally.*
:::

:::definition "def:silverman-modular-discriminant" (lean := "Heights.silvermanModularDiscriminant, Heights.silvermanModularDiscriminant_ne_zero")
Silverman's analytic normalization is
$`\Delta_{\mathrm{Silv}}(\tau)=(2\pi)^{12}\Delta_{\mathrm{mathlib}}(\tau)`.
The factor is retained explicitly, and the function is proved nonvanishing.

*Status: formalized unconditionally.*
:::

:::definition "def:modular-j" (lean := "Heights.modularJ, Heights.modularJ_mul_discriminant, Heights.modularJ_eq_zero_iff, Heights.modularJ_smul, Heights.exists_mem_fd_modularJ_eq_of_surjective")
Define $`j_{\mathrm{mod}}(\tau)=E_4(\tau)^3/\Delta_{\mathrm{mathlib}}(\tau)`.
This is the $`q^{-1}+744+\cdots` normalization, without a factor of 1728.
The denominator is proved nonzero and the normalization is checked against the
$`E_4,E_6,\Delta` identity.

*Status: formalized unconditionally; the required global analytic bounds are proved in `prop:modular-estimates`.*
:::

# Unconditional mathematics

:::proposition "prop:rational-height-arithmetic" (uses := "def:normalized-log-height") (lean := "Heights.normalizedLogHeight_rat, Heights.ratHeight_scaled_denominator")
The exact numerator/denominator formula for rational logarithmic height and its
positive-integer scaled variant hold, including for the zero rational.

*Status: proved unconditionally.*
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

:::proposition "prop:lattice-weierstrass-curve" (uses := "prop:lattice-eisenstein-normalization, def:modular-j") (lean := "Heights.latticeWeierstrassCurve, Heights.weierstrassP_on_latticeWeierstrassCurve, Heights.latticeWeierstrassCurve_c4, Heights.latticeWeierstrassCurve_discriminant, Heights.latticeWeierstrassCurve_discriminant_eq_modularDiscriminant, Heights.latticeWeierstrassCurve_j")
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

:::proposition "prop:weighted-log-log" (lean := "Heights.weightedLogOneAdd_le, Heights.infinitePlaceWeightedLogOneAdd_bounds, Heights.infinitePlacePosLogAverage_le_normalizedLogHeight, Heights.infinitePlaceLogLogMax_bounds")
The finite weighted Jensen estimate for $`\log(1+x)` holds for arbitrary
nonnegative real weights and inputs. Specializing the weights to infinite-place
multiplicities, bounding the omitted finite-place height terms by positivity,
and applying the local log-log cutoff estimate proves equation (11):
$`0 \le \sum_v n_v \log\log\max(|z|_v,e)
\le [K:\mathbb Q]\log(1+h(z))` for the actual normalized Weil height.

*Status: proved unconditionally.*
:::

# Realization interfaces

These interfaces may package missing geometry and arithmetic, but none may
contain a height comparison, a complete height formula for a free real, or
one of the desired inequalities.

:::definition "def:integral-at" (lean := "Heights.IsIntegralAt")
`IsIntegralAt` records coefficient integrality at one number-field prime via
its multiplicative valuation.

*Status: interface formalized; no existence claim.*
:::

:::definition "def:local-minimal-discriminant-exponent" (uses := "def:integral-at") (lean := "Heights.IsLocalMinimalDiscriminantExponent")
`IsLocalMinimalDiscriminantExponent` stores an integral variable change, its
discriminant exponent, and maximality among integral changes.

*Status: interface formalized; no existence claim.*
:::

:::definition "def:global-minimal-discriminant-data" (uses := "def:local-minimal-discriminant-exponent") (lean := "Heights.GlobalMinimalDiscriminantData, Heights.globalMinimalDiscriminantDataRat")
`GlobalMinimalDiscriminantData` supplies a nonzero integral ideal and proves
that every prime multiplicity realizes the corresponding local minimum. It
does not supply denominator divisibility or a comparison inequality. Mathlib's
DVR minimal-model theorem can be assembled globally over $`\mathbb Q`, where a
single integral equation bounds all local exponents; this produces
`globalMinimalDiscriminantDataRat` for every elliptic rational curve.

*Status: interface formalized and existence proved over $`\mathbb Q`; general
number-field existence remains open.*
:::

:::definition "def:archimedean-period-data" (uses := "def:modular-j") (lean := "Heights.ArchimedeanPeriodData, Heights.nonempty_archimedeanPeriodData_of_modularJ_surjective")
`ArchimedeanPeriodData` supplies a fundamental-domain period ratio at each
infinite place and identifies its modular $`j` with the embedded algebraic
$`j`. It contains no analytic bound or target comparison. Modular invariance
shows that surjectivity of `modularJ` would construct this interface at every
place; that surjectivity theorem remains the concrete analytic gap.

*Status: interface and surjectivity reduction formalized; unconditional
existence for every curve is not claimed.*
:::

:::definition "def:reduced-principal-ideal-data" (lean := "Heights.ReducedPrincipalIdealData, Heights.exists_reducedPrincipalIdealData, Heights.reducedPrincipalIdealData")
`ReducedPrincipalIdealData` packages coprime numerator and denominator ideals,
their fractional-ideal equality, and the explicit zero normalization. It does
not package the height identity or any comparison. Such data is constructed
unconditionally for every number-field element, and `reducedPrincipalIdealData`
fixes a canonical choice for downstream statements.

*Status: interface and unconditional construction formalized.*
:::

# Certificate-level height and comparisons

:::definition "def:silverman-height" (uses := "def:silverman-modular-discriminant, def:global-minimal-discriminant-data, def:archimedean-period-data") (lean := "Heights.silvermanHeight, Heights.silvermanHeight_archimedean_log_arg_pos, Heights.silvermanHeight_denominator_pos")
`silvermanHeight` is the displayed finite minimal-discriminant term minus the
archimedean $`\log(|\Delta_{\mathrm{Silv}}(\tau)|\operatorname{Im}(\tau)^6)`
term, divided by $`12[K:\mathbb Q]`. It is formula-defined and is not a free
real called “Faltings height.” Every logarithm argument and the denominator are
proved strictly positive.

*Status: certificate-level definition formalized; no Arakelov identification is claimed.*
:::

:::proposition "prop:proposition-1-1-certified" (uses := "def:silverman-height")
With genuine minimal-discriminant and period certificates, the preceding
formula is the elliptic-curve height formula corresponding to Proposition
1.1. This node does not assert unconditional existence of those data or an
Arakelov/Hodge-bundle construction.

*Status: not started (conditional/certificate-level target).*
:::

:::definition "def:certified-semistability" (uses := "def:global-minimal-discriminant-data") (lean := "Heights.IsSemistable, Heights.denominator_dvd_minimalDiscriminant, Heights.unstableMinimalDiscriminant_eq_top_of_semistable")
Semistability is defined place by place as good or multiplicative reduction for
a certified minimal local model. The unconditionally constructed reduced
$`j`-denominator is proved to divide the minimal-discriminant ideal, defining
its canonical complement without a reduced-ideal hypothesis, and semistability
is proved to make that complement the unit ideal.

*Status: formalized and proved conditionally only on global minimal-
discriminant realization data.*
:::

:::theorem "thm:proposition-2-1-certified" (uses := "prop:rational-height-arithmetic, prop:reduced-principal-ideals, prop:modular-estimates, prop:weighted-log-log, def:silverman-height") (lean := "Heights.comparisonExpression_eq_archimedeanAverage, Heights.correctedComparison_bounds_of_modular_estimates, Heights.proposition_2_1_certified")
One pair of absolute modular-estimate constants, quantified before the number
field, curve, and remaining realization data, gives Silverman's two-sided
Proposition 2.1 estimate for normalized $`j`-height, the canonical unstable
ideal, and `silvermanHeight`. The theorem no longer assumes reduced
principal-ideal data or analytic estimates: the unconditional fundamental-
domain theorems supply the two absolute constants directly.

*Status: proved conditional only on minimal-discriminant and period realization
data; this is not an all-curves Arakelov Faltings-height theorem.*
:::

:::theorem "thm:proposition-2-1-semistable-certified" (uses := "thm:proposition-2-1-certified, def:certified-semistability") (lean := "Heights.semistable_abs_comparison_of_corrected_bounds, Heights.proposition_2_1_semistable_certified")
After proving certified semistability makes the unstable ideal trivial, derive
the absolute-value specialization comparing normalized $`j`-height with
$`12\,\mathrm{silvermanHeight}`.

*Status: proved conditional only on minimal-discriminant and period realization
data and certified semistability; no analytic estimate remains as a hypothesis.*
:::

The repository does not presently claim period construction, global minimal-
discriminant construction over every number field, complex uniformization, an
Arakelov Faltings height, or unconditional all-curves Proposition 2.1. Over
$`\mathbb Q` the global minimal-discriminant certificate is unconditional, so
`ArchimedeanPeriodData` is the sole remaining realization input. The precise
archimedean feasibility findings are recorded in
`Plans/ArchimedeanUniformizationFeasibility.md`.

{blueprint_graph}
{blueprint_summary}
