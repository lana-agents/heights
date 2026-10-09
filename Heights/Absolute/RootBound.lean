/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

set_option linter.style.header false

/-!
# Local bounds for roots of monic polynomials

Let `F` be a field with an absolute value `v : AbsoluteValue F ℝ`, and let `z` be a root of a
monic polynomial `p = X^n + c_{n-1} X^{n-1} + ⋯ + c_0` over `F`.

* If `v` is nonarchimedean and `v c_i ≤ B` for all `i < n`, where `1 ≤ B`, then `v z ≤ B`
  (`Heights.Absolute.apply_le_of_isNonarchimedean`).  In particular, if all coefficients satisfy
  `v c_i ≤ 1`, then `v z ≤ 1`, and in general `v z ≤ max 1 (max_i v c_i)`.
* For an arbitrary absolute value we have the Cauchy bound
  `v z ≤ max 1 (∑_{i < n} v c_i) ≤ 1 + ∑_{i < n} v c_i`
  (`Heights.Absolute.apply_le_max_one_sum`, `Heights.Absolute.apply_le_one_add_sum`).
-/

namespace Heights.Absolute

open Polynomial Finset

variable {F : Type*} [Field F] (v : AbsoluteValue F ℝ)

/-- For a root `z` of a monic `p` of degree `n`, `z^n = -∑_{i<n} c_i z^i`. -/
lemma pow_natDegree_eq_neg_sum {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) :
    z ^ p.natDegree = -∑ i ∈ range p.natDegree, p.coeff i * z ^ i := by
  have h := congrArg (eval z) hp.as_sum
  rw [hz, eval_add, eval_pow, eval_X, eval_finsetSum] at h
  simp only [eval_mul, eval_C, eval_pow, eval_X] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- A root of a monic polynomial has positive degree. -/
lemma natDegree_pos_of_root {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) :
    0 < p.natDegree := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · have := pow_natDegree_eq_neg_sum hp hz
    rw [h] at this
    simp at this
  · exact h

/-- In a nonarchimedean absolute value, a finite sum of terms of size `≤ M` has size `≤ M`. -/
lemma apply_sum_le_of_isNonarchimedean (hv : ∀ a b, v (a + b) ≤ max (v a) (v b))
    {ι : Type*} (s : Finset ι) (f : ι → F) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ i ∈ s, v (f i) ≤ M) :
    v (∑ i ∈ s, f i) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (hv _ _).trans (max_le (hf a (Finset.mem_insert_self a s)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

/-- **Nonarchimedean root bound**: if `v` is nonarchimedean, `1 ≤ B` and every non-leading
coefficient of the monic polynomial `p` has `v c_i ≤ B`, then every root `z` of `p` satisfies
`v z ≤ B`. -/
theorem apply_le_of_isNonarchimedean (hv : ∀ a b, v (a + b) ≤ max (v a) (v b))
    {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) {B : ℝ} (hB : 1 ≤ B)
    (hc : ∀ i < p.natDegree, v (p.coeff i) ≤ B) : v z ≤ B := by
  by_contra hlt
  push Not at hlt
  set n := p.natDegree
  have hn : 0 < n := natDegree_pos_of_root hp hz
  have hz1 : 1 < v z := lt_of_le_of_lt hB hlt
  have hz0 : 0 < v z := zero_lt_one.trans hz1
  have hsum : v (∑ i ∈ range n, p.coeff i * z ^ i) ≤ B * v z ^ (n - 1) := by
    refine apply_sum_le_of_isNonarchimedean v hv _ _ (by positivity) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [map_mul, map_pow]
    refine mul_le_mul (hc i hi') (pow_le_pow_right₀ hz1.le (by omega)) (by positivity)
      (by linarith)
  have heq := congrArg v (pow_natDegree_eq_neg_sum hp hz)
  rw [map_pow, AbsoluteValue.map_neg] at heq
  rw [← heq] at hsum
  have : v z ^ n = v z * v z ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [this] at hsum
  have hpos : 0 < v z ^ (n - 1) := by positivity
  have := le_of_mul_le_mul_right hsum hpos
  linarith

/-- If `v` is nonarchimedean and all non-leading coefficients of the monic `p` have
`v c_i ≤ 1`, then every root of `p` has `v z ≤ 1`. -/
theorem apply_le_one_of_isNonarchimedean (hv : ∀ a b, v (a + b) ≤ max (v a) (v b))
    {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0)
    (hc : ∀ i < p.natDegree, v (p.coeff i) ≤ 1) : v z ≤ 1 :=
  apply_le_of_isNonarchimedean v hv hp hz le_rfl hc

/-- **Nonarchimedean root bound**, maximum form: `v z ≤ max 1 (max_{i < n} v c_i)`. -/
theorem apply_le_max_one_iSup_of_isNonarchimedean (hv : ∀ a b, v (a + b) ≤ max (v a) (v b))
    {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) :
    v z ≤ max 1 (⨆ i : Fin p.natDegree, v (p.coeff i)) := by
  refine apply_le_of_isNonarchimedean v hv hp hz (le_max_left _ _) fun i hi => ?_
  exact le_max_of_le_right (Finite.le_ciSup_of_le (⟨i, hi⟩ : Fin p.natDegree) le_rfl)

/-- **Cauchy's root bound** for an arbitrary absolute value:
`v z ≤ max 1 (∑_{i < n} v c_i)`. -/
theorem apply_le_max_one_sum {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) :
    v z ≤ max 1 (∑ i ∈ range p.natDegree, v (p.coeff i)) := by
  rcases le_or_gt (v z) 1 with h | h
  · exact le_max_of_le_left h
  refine le_max_of_le_right ?_
  set n := p.natDegree
  have hn : 0 < n := natDegree_pos_of_root hp hz
  have hz0 : 0 < v z := zero_lt_one.trans h
  have heq := congrArg v (pow_natDegree_eq_neg_sum hp hz)
  rw [map_pow, AbsoluteValue.map_neg] at heq
  have hsum : v (∑ i ∈ range n, p.coeff i * z ^ i) ≤
      (∑ i ∈ range n, v (p.coeff i)) * v z ^ (n - 1) := by
    refine (AbsoluteValue.sum_le v _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [map_mul, map_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.le (by omega)) (v.nonneg _)
  rw [← heq] at hsum
  have : v z ^ n = v z * v z ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [this] at hsum
  exact le_of_mul_le_mul_right hsum (by positivity)

/-- **Cauchy's root bound**: `v z ≤ 1 + ∑_{i < n} v c_i`. -/
theorem apply_le_one_add_sum {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) :
    v z ≤ 1 + ∑ i ∈ range p.natDegree, v (p.coeff i) := by
  refine (apply_le_max_one_sum v hp hz).trans (max_le ?_ ?_)
  · linarith [Finset.sum_nonneg fun i (_ : i ∈ range p.natDegree) => v.nonneg (p.coeff i)]
  · linarith

/-- Cauchy's bound in terms of a uniform bound on the coefficients:
if `v c_i ≤ B` for all `i < n`, then `v z ≤ max 1 (n * B)`. -/
theorem apply_le_max_one_mul {p : F[X]} (hp : p.Monic) {z : F} (hz : p.eval z = 0) {B : ℝ}
    (hc : ∀ i < p.natDegree, v (p.coeff i) ≤ B) : v z ≤ max 1 (p.natDegree * B) := by
  refine (apply_le_max_one_sum v hp hz).trans (max_le_max le_rfl ?_)
  calc ∑ i ∈ range p.natDegree, v (p.coeff i) ≤ ∑ _i ∈ range p.natDegree, B :=
        Finset.sum_le_sum fun i hi => hc i (Finset.mem_range.mp hi)
    _ = p.natDegree * B := by simp

end Heights.Absolute
