import Mathlib

set_option linter.style.header false

/-!
# Absolute logarithmic Weil heights

This file fixes the normalization of logarithmic heights used in the comparison
with Silverman's elliptic-curve height.  Mathlib's `Height.logHeight₁` over a
number field is the relative height, so the absolute height divides by the
field degree.
-/

namespace Heights

/-- The absolute logarithmic Weil height of a number-field element.

Mathlib's `Height.logHeight₁` is relative to the ambient number field.  Dividing
by `[K : ℚ]` makes this normalization invariant under extension of number
fields, as in Silverman's Proposition 2.1. -/
noncomputable def normalizedLogHeight
    (K : Type*) [Field K] [NumberField K] (x : K) : ℝ :=
  Height.logHeight₁ x / (Module.finrank ℚ K : ℝ)

/-- The degree occurring in `normalizedLogHeight` is positive. -/
theorem numberFieldDegree_pos
    (K : Type*) [Field K] [NumberField K] :
    (0 : ℝ) < Module.finrank ℚ K := by
  exact_mod_cast Module.finrank_pos

/-- Absolute logarithmic Weil height is nonnegative. -/
theorem normalizedLogHeight_nonneg
    (K : Type*) [Field K] [NumberField K] (x : K) :
    0 ≤ normalizedLogHeight K x := by
  exact div_nonneg (Height.zero_le_logHeight₁ x) (numberFieldDegree_pos K).le

/-- Over `ℚ`, the normalized logarithmic height is the logarithm of the maximum
of the absolute numerator and the positive denominator. -/
theorem normalizedLogHeight_rat (q : ℚ) :
    normalizedLogHeight ℚ q =
      Real.log ((max q.num.natAbs q.den : ℕ) : ℝ) := by
  simp [normalizedLogHeight, Rat.logHeight₁_eq_log_max]

/-- Scaling both entries in the rational numerator/denominator maximum by a
positive natural number adds its logarithm. -/
theorem ratHeight_scaled_denominator (q : ℚ) (n : ℕ) (hn : 0 < n) :
    Height.logHeight₁ q + Real.log (n : ℝ) =
      Real.log ((max (q.num.natAbs * n) (q.den * n) : ℕ) : ℝ) := by
  rw [Rat.logHeight₁_eq_log_max]
  calc
    Real.log ((max q.num.natAbs q.den : ℕ) : ℝ) + Real.log (n : ℝ) =
        Real.log (((max q.num.natAbs q.den : ℕ) : ℝ) * (n : ℝ)) :=
      (Real.log_mul (by positivity) (by positivity)).symm
    _ = Real.log ((max (q.num.natAbs * n) (q.den * n) : ℕ) : ℝ) := by
      congr 1
      norm_cast
      exact max_mul_of_nonneg _ _ (Nat.zero_le n)

end Heights
