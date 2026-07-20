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

open NumberField in
/-- The normalized infinite-place contribution is bounded by the full absolute
logarithmic height. The omitted finite-place terms are all nonnegative. -/
theorem infinitePlacePosLogAverage_le_normalizedLogHeight
    (K : Type*) [Field K] [NumberField K] (z : K) :
    (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v z)) /
        (Module.finrank ℚ K : ℝ) ≤ normalizedLogHeight K z := by
  have hfin : 0 ≤ ∑ᶠ v : FinitePlace K, Real.posLog (v z) :=
    finsum_nonneg fun _ => Real.posLog_nonneg
  rw [normalizedLogHeight, NumberField.logHeight₁_eq]
  apply div_le_div_of_nonneg_right _ (numberFieldDegree_pos K).le
  exact le_add_of_nonneg_right hfin

open NumberField in
/-- Jensen's bound at the infinite places, now with its weighted average
bounded by the actual normalized height of the number-field element. -/
theorem infinitePlaceWeightedLogOneAdd_posLog_bounds
    (K : Type*) [Field K] [NumberField K] (z : K) :
    0 ≤ ∑ v : InfinitePlace K,
        (v.mult : ℝ) * Real.log (1 + Real.posLog (v z)) ∧
      ∑ v : InfinitePlace K,
          (v.mult : ℝ) * Real.log (1 + Real.posLog (v z)) ≤
        (Module.finrank ℚ K : ℝ) *
          Real.log (1 + normalizedLogHeight K z) := by
  have h := infinitePlaceWeightedLogOneAdd_bounds K
    (fun v : InfinitePlace K => Real.posLog (v z))
    (fun _ => Real.posLog_nonneg)
  refine ⟨h.1, h.2.trans ?_⟩
  have harch : 0 ≤
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v z)) /
        (Module.finrank ℚ K : ℝ) := by
    apply div_nonneg _ (numberFieldDegree_pos K).le
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (by positivity) Real.posLog_nonneg
  apply mul_le_mul_of_nonneg_left _ (numberFieldDegree_pos K).le
  apply Real.strictMonoOn_log.monotoneOn
  · exact Set.mem_Ioi.mpr (by linarith)
  · exact Set.mem_Ioi.mpr (by linarith [normalizedLogHeight_nonneg K z])
  · gcongr
    exact infinitePlacePosLogAverage_le_normalizedLogHeight K z

/-- A local log-log term is nonnegative and is bounded by the `log (1 + log⁺)`
term to which weighted Jensen applies. The cutoff `exp 1` is the precise
formal version of the conventional `e` in `log log max (a, e)`. -/
theorem logLogMaxExpOne_bounds (a : ℝ) :
    0 ≤ Real.log (Real.log (max a (Real.exp 1))) ∧
      Real.log (Real.log (max a (Real.exp 1))) ≤
        Real.log (1 + Real.posLog a) := by
  by_cases h : a ≤ Real.exp 1
  · have hmax : max a (Real.exp 1) = Real.exp 1 := max_eq_right h
    rw [hmax, Real.log_exp, Real.log_one]
    refine ⟨le_rfl, Real.log_nonneg ?_⟩
    linarith [Real.posLog_nonneg (x := a)]
  · have hea : Real.exp 1 ≤ a := le_of_not_ge h
    have ha_pos : 0 < a := (Real.exp_pos 1).trans_le hea
    have hlog_one : 1 ≤ Real.log a := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) ha_pos hea
    have hposlog : Real.posLog a = Real.log a := by
      apply Real.posLog_eq_log
      rw [abs_of_pos ha_pos]
      exact le_trans (Real.one_le_exp (by norm_num)) hea
    rw [max_eq_left hea, hposlog]
    constructor
    · exact Real.log_nonneg hlog_one
    · apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (lt_of_lt_of_le (by norm_num) hlog_one)
      · exact Set.mem_Ioi.mpr (by linarith)
      · linarith

open NumberField in
/-- Silverman's equation (11): the weighted archimedean log-log sum is between
zero and the degree times `log (1 + h(z))`, where `h` is the actual absolute
normalized Weil height. -/
theorem infinitePlaceLogLogMax_bounds
    (K : Type*) [Field K] [NumberField K] (z : K) :
    0 ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) *
        Real.log (Real.log (max (v z) (Real.exp 1))) ∧
      ∑ v : InfinitePlace K, (v.mult : ℝ) *
          Real.log (Real.log (max (v z) (Real.exp 1))) ≤
        (Module.finrank ℚ K : ℝ) *
          Real.log (1 + normalizedLogHeight K z) := by
  constructor
  · apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (by positivity) (logLogMaxExpOne_bounds (v z)).1
  · calc
      ∑ v : InfinitePlace K, (v.mult : ℝ) *
          Real.log (Real.log (max (v z) (Real.exp 1))) ≤
          ∑ v : InfinitePlace K, (v.mult : ℝ) *
            Real.log (1 + Real.posLog (v z)) := by
        apply Finset.sum_le_sum
        intro v _
        exact mul_le_mul_of_nonneg_left (logLogMaxExpOne_bounds (v z)).2 (by positivity)
      _ ≤ (Module.finrank ℚ K : ℝ) *
          Real.log (1 + normalizedLogHeight K z) :=
        (infinitePlaceWeightedLogOneAdd_posLog_bounds K z).2

/-- An explicit `ε`-absorption estimate for the log-log error. This is the
elementary analytic inequality used in the rational specialization of
Silverman's Corollary 2.3. -/
theorem six_logOneAdd_log_le_epsilon_log_add
    (ε t : ℝ) (hε : 0 < ε) (ht : 1 ≤ t) :
    6 * Real.log (1 + Real.log t) ≤
      ε * Real.log t + 6 * Real.log (1 + 6 / ε) := by
  let x := Real.log t
  let δ := ε / 6
  let A := 1 + 6 / ε
  have hx : 0 ≤ x := Real.log_nonneg ht
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hA : 1 ≤ A := by
    dsimp [A]
    have : 0 < 6 / ε := div_pos (by norm_num) hε
    linarith
  have hA_pos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hinner : 0 < 1 + δ * x := by positivity
  have hscale : 1 + x ≤ A * (1 + δ * x) := by
    have hAδ : A * δ = 1 + δ := by
      dsimp [A, δ]
      field_simp
      ring
    rw [mul_add, mul_one, ← mul_assoc, hAδ]
    nlinarith [mul_nonneg hδ.le hx]
  have hlogscale : Real.log (1 + x) ≤
      Real.log A + Real.log (1 + δ * x) := by
    rw [← Real.log_mul hA_pos.ne' hinner.ne']
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by linarith))
      (Set.mem_Ioi.mpr (mul_pos hA_pos hinner)) hscale
  have hloginner : Real.log (1 + δ * x) ≤ δ * x := by
    have := Real.log_le_sub_one_of_pos hinner
    linarith
  dsimp [x, δ, A] at hlogscale hloginner ⊢
  nlinarith

/-- Big-`O_ε` form of `six_logOneAdd_log_le_epsilon_log_add`: for every
positive `ε`, one nonnegative constant works uniformly for every `t ≥ 1`. -/
theorem six_logOneAdd_log_epsilon_absorption (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      6 * Real.log (1 + Real.log t) ≤ ε * Real.log t + C := by
  refine ⟨6 * Real.log (1 + 6 / ε), ?_, ?_⟩
  · apply mul_nonneg (by norm_num) (Real.log_nonneg ?_)
    have : 0 < 6 / ε := div_pos (by norm_num) hε
    linarith
  · intro t ht
    exact six_logOneAdd_log_le_epsilon_log_add ε t hε ht

end Heights
