import Heights

/-!
# Heights comparator solution

This module re-exports only challenge targets for which a project proof exists.
`Comparator/config.json` lists the same proved targets.
-/

namespace Heights

/-- Comparator export of the proved rational-height scaling identity. -/
theorem rat_height_scaled_denominator (q : ℚ) (n : ℕ) (hn : 0 < n) :
    Height.logHeight₁ q + Real.log (n : ℝ) =
      Real.log ((max (q.num.natAbs * n) (q.den * n) : ℕ) : ℝ) :=
  ratHeight_scaled_denominator q n hn

end Heights
