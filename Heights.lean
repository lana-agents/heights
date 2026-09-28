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
import Heights.WeierstrassInfinityAnalytic
import Heights.WeierstrassCompactCharts
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
import Heights.Absolute.Extension
import Heights.Absolute.Basic
import Heights.Absolute.RootBound
import Heights.Absolute.Northcott
import Heights.Different.QuotientBasis
import Heights.Different.SerreCore
import Heights.Different.SerreBound
import Heights.Different.NumberField
import Heights.Different.Bounds
import Heights.Different.Unramified
import Heights.Different.Places
import Heights.Different.Conductor
import Heights.Different.Kummer
import Heights.Local.Compactness
import Heights.Local.PlaceEmbedding
import Heights.Local.LimitPlace
import Heights.Curve.TupleHeight
import Heights.Curve.Integrality
import Heights.Curve.LinearEquiv
import Heights.Curve.Conductor
import Heights.Curve.CondHeight
import Heights.Curve.DivisorHeight
import Heights.Curve.Pullback
import Heights.Curve.Compactness
import Heights.Local.Bounded
import Heights.Curve.ModelChange
import Heights.Curve.CondDivisor
import Heights.Curve.KummerPoint

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
intrinsic one-dimensional complex-manifold structure. Its ambient coordinate
inclusion is analytic, and every admissible affine variable change is a
biholomorphism for these independently constructed structures. In the
projective `Y ≠ 0` chart at infinity, the homogenized equation now has an
explicit implicit-function branch chart with holomorphic inverse, and its
punctured branch is identified with the affine curve by the rational overlap
formulas. An explicit cubic properness estimate proves that the whole branch
is homeomorphic to the open compact-curve neighborhood obtained by deleting
the affine `y = 0` locus. Lifting the finite and infinity charts through their
open embeddings, and proving both rational mixed transitions holomorphic,
gives the independently topologized compact curve a one-dimensional complex-
analytic `IsManifold` structure. The project still does not prove the explicit
uniformization analytic for this intrinsic structure, formalize periods by
integration, or construct an Arakelov Faltings height.
-/
