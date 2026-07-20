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

/-- Comparator export of the proved weighted Jensen inequality. -/
theorem weighted_log_one_add_average
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) (d : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hd : ∑ i, w i = d) (hd_pos : 0 < d) :
    ∑ i, w i * Real.log (1 + x i) ≤
      d * Real.log (1 + (∑ i, w i * x i) / d) :=
  weightedLogOneAdd_le w x d hw hx hd hd_pos

end Heights
