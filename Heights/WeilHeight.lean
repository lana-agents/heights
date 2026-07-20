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

/-- Weighted Jensen's inequality for `log (1 + x)`, with the total weight
kept explicit. This is the abstract concavity estimate used for the weighted
infinite-place sum in Silverman's equation (11). -/
theorem weightedLogOneAdd_le
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) (d : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hd : ∑ i, w i = d) (hd_pos : 0 < d) :
    ∑ i, w i * Real.log (1 + x i) ≤
      d * Real.log (1 + (∑ i, w i * x i) / d) := by
  classical
  have hweights : ∑ i, w i / d = 1 := by
    rw [← Finset.sum_div, hd, div_self hd_pos.ne']
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun i => w i / d) (p := fun i => 1 + x i)
    (fun i _ => div_nonneg (hw i) hd_pos.le) hweights
    (fun i _ => by simp only [Set.mem_Ioi]; linarith [hx i])
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ i, w i / d * (1 + x i) =
      1 + (∑ i, w i * x i) / d := by
    calc
      ∑ i, w i / d * (1 + x i) =
          ∑ i, (w i / d + (w i * x i) / d) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, w i / d) + ∑ i, (w i * x i) / d :=
        Finset.sum_add_distrib
      _ = 1 + (∑ i, w i * x i) / d := by
        rw [hweights, Finset.sum_div]
  rw [hsum] at hJ
  calc
    ∑ i, w i * Real.log (1 + x i) =
        d * ∑ i, w i / d * Real.log (1 + x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ d * Real.log (1 + (∑ i, w i * x i) / d) :=
      mul_le_mul_of_nonneg_left hJ hd_pos.le

/-- The weighted logarithmic sum in `weightedLogOneAdd_le` is nonnegative. -/
theorem weightedLogOneAdd_nonneg
    {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ ∑ i, w i * Real.log (1 + x i) := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw i) (Real.log_nonneg (by linarith [hx i]))

open NumberField in
/-- Equation (11)'s weighted concavity bounds, specialized to infinite-place
multiplicities. The right side retains the weighted average explicitly; a later
height decomposition will bound that average by the normalized `j`-height. -/
theorem infinitePlaceWeightedLogOneAdd_bounds
    (K : Type*) [Field K] [NumberField K]
    (x : InfinitePlace K → ℝ) (hx : ∀ v, 0 ≤ x v) :
    0 ≤ ∑ v, (v.mult : ℝ) * Real.log (1 + x v) ∧
      ∑ v, (v.mult : ℝ) * Real.log (1 + x v) ≤
        (Module.finrank ℚ K : ℝ) *
          Real.log (1 +
            (∑ v, (v.mult : ℝ) * x v) / (Module.finrank ℚ K : ℝ)) := by
  constructor
  · exact weightedLogOneAdd_nonneg (fun v : InfinitePlace K => (v.mult : ℝ)) x
      (fun _ => by positivity) hx
  · apply weightedLogOneAdd_le (fun v : InfinitePlace K => (v.mult : ℝ)) x
      (Module.finrank ℚ K : ℝ)
    · intro v
      positivity
    · exact hx
    · exact_mod_cast InfinitePlace.sum_mult_eq (K := K)
    · exact numberFieldDegree_pos K

end Heights
