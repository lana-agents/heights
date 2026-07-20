import Heights.WeilHeight
import Heights.ModularJ
import Heights.Certificates

/-!
# Heights

Formalization of the comparison between (logarithmic) Weil heights and
Silverman's formula-defined elliptic-curve height (cf. [Silv], Proposition
2.1). See `Plans/HeightsSpec.md` for the honesty boundary.

The current public API contains the unconditional Weil-height normalization,
rational and weighted height arithmetic, and the correctly normalized modular
functions, together with explicit interfaces for missing realization data. It
does not yet define or claim a Faltings height comparison.
-/
