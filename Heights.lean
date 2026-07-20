import Heights.WeilHeight
import Heights.ModularJ
import Heights.LatticeEisenstein
import Heights.LatticeWeierstrass
import Heights.LatticeAffinePoint
import Heights.LatticeQuotientPoint
import Heights.LatticeQuotientTopology
import Heights.LatticeCurveTopology
import Heights.LatticeAffinePointTopology
import Heights.Certificates
import Heights.SilvermanHeight
import Heights.IdealFactorization

/-!
# Heights

Formalization of the comparison between (logarithmic) Weil heights and
Silverman's formula-defined elliptic-curve height (cf. [Silv], Proposition
2.1). See `Plans/HeightsSpec.md` for the honesty boundary.

The public API contains the unconditional Weil-height and modular estimates,
explicit interfaces for missing realization data, Silverman's formula-defined
certificate-level height, and certified forms of Proposition 2.1. Global
minimal-discriminant data is constructed unconditionally over `ℚ`; compatible
archimedean period data remains an input even there. The project does not claim
an Arakelov Faltings height or an unconditional all-curves comparison theorem.
-/
