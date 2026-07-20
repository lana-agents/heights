import Heights.WeilHeight
import Heights.ModularJ

/-!
# Heights

Formalization of the comparison between (logarithmic) Weil heights and
Silverman's formula-defined elliptic-curve height (cf. [Silv], Proposition
2.1). See `Plans/HeightsSpec.md` for the honesty boundary.

The current public API contains the unconditional Weil-height normalization,
rational and weighted height arithmetic, and the correctly normalized modular
functions. It does not yet define or claim a Faltings height comparison.
-/
