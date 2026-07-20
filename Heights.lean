import Heights.WeilHeight
import Heights.ModularJ
import Heights.Certificates
import Heights.SilvermanHeight

/-!
# Heights

Formalization of the comparison between (logarithmic) Weil heights and
Silverman's formula-defined elliptic-curve height (cf. [Silv], Proposition
2.1). See `Plans/HeightsSpec.md` for the honesty boundary.

The current public API contains the unconditional Weil-height normalization,
rational and weighted height arithmetic, and the correctly normalized modular
functions, explicit interfaces for missing realization data, and Silverman's
formula-defined certificate-level height. It does not claim an Arakelov
Faltings height or a comparison theorem.
-/
