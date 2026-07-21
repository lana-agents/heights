import Heights.WeilHeight
import Heights.ModularJ
import Heights.LatticeEisenstein
import Heights.WeierstrassPrincipalPart
import Heights.WeierstrassDifferential
import Heights.PeriodPairScaling
import Heights.WeierstrassAdditionDifferential
import Heights.WeierstrassAddition
import Heights.WeierstrassFibers
import Heights.LatticeWeierstrass
import Heights.ModularJFibers
import Heights.LatticeAffinePoint
import Heights.LatticeQuotientPoint
import Heights.LatticeQuotientTopology
import Heights.LatticeQuotientManifold
import Heights.LatticeQuotientCompact
import Heights.WeierstrassCurveTopology
import Heights.VariableChangeAnalytic
import Heights.WeierstrassFiniteAnalytic
import Heights.WeierstrassFiniteManifold
import Heights.LatticeCurveTopology
import Heights.LatticeAffinePointTopology
import Heights.LatticePointMapTopology
import Heights.LatticePointMapNegation
import Heights.LatticePointMapInjectivity
import Heights.LatticePointMapAddition
import Heights.WeierstrassSurjectivity
import Heights.Certificates
import Heights.ArchimedeanAlgebraicRealization
import Heights.SilvermanHeight
import Heights.IdealFactorization

/-!
# Heights

Formalization of the comparison between (logarithmic) Weil heights and
Silverman's formula-defined elliptic-curve height (cf. [Silv], Proposition
2.1). See `Plans/HeightsSpec.md` for the honesty boundary.

The public API contains the unconditional Weil-height and modular estimates,
constructed formula-level realization data, Silverman's formula-defined
height, and certified and all-curves forms of Proposition 2.1. The
archimedean construction uses surjectivity of modular `j` to choose a matching
fundamental-domain parameter. Same-`j` classification over `ℂ` then supplies an
actual algebraic variable change between the embedded input curve and the
explicit lattice curve, eliminating the complex twisting objection. Its
coordinate map transports the lattice quotient uniformization to the embedded
input curve as an additive equivalence. The source quotient now has an
independently constructed complex-manifold structure for which its projection
from `ℂ` is locally biholomorphic. Every nonsingular complex target has an
equation-defined compact Hausdorff topology, invariant under admissible
variable changes. The affine coordinate change and its inverse are moreover
packaged as an ambient biholomorphism of `ℂ × ℂ`. At every finite curve point,
the two equation derivatives are computed, the complex implicit-function
theorem supplies an analytic graph germ in one coordinate direction, and its
zero-fiber neighborhood gives an open topological chart. Their transition
maps are holomorphic on whole overlaps, giving the affine equation locus an
intrinsic one-dimensional complex-manifold structure. The project still does
not construct the chart at infinity or a complex atlas on the compact curve,
prove the uniformization analytic, formalize periods by integration, or
construct an Arakelov Faltings height.
-/
