/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Heights.Curve.DivisorHeight
import Belyi.CurveField.Fundamental

/-!
# Functoriality of heights under finite maps of curves

A finite extension of function fields `K ⊆ L` is a finite map of curves `π : Y → X`. Points of
`Y` restrict to points of `X` (`Belyi.CurveField.QbarPoint.restrict`), divisors pull back
(`Heights.Curve.pullback`: `(π^*D)(Q) = e(Q|P) · D(P)` for `P = Q|_K`), and heights are
functorial ([GenEll], Definition 1.1 (ii) and Proposition 1.4):

* `tupleHeight_algebraMap`: `h_{π^* s}(y) = h_s(π(y))` exactly;
* `divHeight_pullback`: `ht_{π^*D} ≈ ht_D ∘ π`;
* `deg_pullback`: `deg π^*D = [L : K] · deg D`.
-/

namespace Heights.Curve

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Absolute
open scoped Classical

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L] [IsCurveField K]
  [IsCurveField L] [Algebra K L] [FiniteDimensional K L]

variable {ι : Type*} [Fintype ι]

/-- Minimal orders pull back with the ramification index. -/
theorem minOrd_algebraMap {s : ι → K} (hs : ∃ i, s i ≠ 0) (Q : Place L) :
    minOrd Q (fun i => algebraMap K L (s i)) = Q.ramificationIdx K * minOrd (Q.restrict K) s := by
  have hs' : ∃ i, algebraMap K L (s i) ≠ 0 := by
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  have he : (0 : ℤ) < Q.ramificationIdx K := by exact_mod_cast Q.ramificationIdx_pos
  apply le_antisymm
  · have := minOrd_le (P := Q) hs' (j := normIdx (Q.restrict K) s hs)
      ((map_ne_zero _).mpr (normIdx_ne_zero hs))
    rw [Q.ord_algebraMap_eq_mul, ← minOrd_eq hs] at this
    exact this
  · rw [minOrd_eq hs']
    set i := normIdx Q (fun i => algebraMap K L (s i)) hs'
    have hi : s i ≠ 0 := fun h => normIdx_ne_zero hs' (by
      change algebraMap K L (s i) = 0
      rw [h, map_zero])
    rw [Q.ord_algebraMap_eq_mul]
    exact mul_le_mul_of_nonneg_left (minOrd_le hs hi) he.le

/-- **Heights of tuples are compatible with finite maps**: `h_{π^* s}(y) = h_s(π(y))`. -/
theorem tupleHeight_algebraMap (s : ι → K) (y : QbarPoint L) :
    tupleHeight (fun i => algebraMap K L (s i)) y = tupleHeight s (y.restrict K) := by
  by_cases hs : ∃ i, s i ≠ 0
  · have hs' : ∃ i, algebraMap K L (s i) ≠ 0 := by
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, (map_ne_zero _).mpr hi⟩
    set x := y.restrict K
    set i₀ := normIdx x.P s hs
    have hs₀ : s i₀ ≠ 0 := normIdx_ne_zero hs
    have hmemK : ∀ i, s i / s i₀ ∈ x.P.1 := div_normIdx_mem hs
    have hmem : ∀ i, algebraMap K L (s i) * (algebraMap K L (s i₀))⁻¹ ∈ y.P.1 := fun i => by
      rw [← map_inv₀, ← map_mul, ← div_eq_mul_inv]
      exact hmemK i
    have hval : ∀ i, y.eval (algebraMap K L (s i) * (algebraMap K L (s i₀))⁻¹) (hmem i) =
        x.eval (s i / s i₀) (hmemK i) := fun i => by
      rw [QbarPoint.eval_restrict]
      exact y.eval_congr (by rw [map_div₀, div_eq_mul_inv]) _
    have hne : ∃ i, y.eval (algebraMap K L (s i) * (algebraMap K L (s i₀))⁻¹) (hmem i) ≠ 0 := by
      refine ⟨i₀, ?_⟩
      rw [hval, x.eval_congr (div_self hs₀), x.eval_one]
      exact one_ne_zero
    rw [tupleHeight_eq_of_mul hs' y _ hmem hne, tupleHeight_def hs]
    congr 1
    funext i
    exact hval i
  · have hs' : ¬ ∃ i, algebraMap K L (s i) ≠ 0 := by
      push Not at hs ⊢
      intro i
      rw [hs i, map_zero]
    simp [tupleHeight, hs, hs']

variable (K) in
/-- **Pull-back of divisors** along the finite map `π : Y → X` given by `K ⊆ L`:
`(π^*D)(Q) = e(Q|P) · D(P)` with `P = Q|_K`. -/
noncomputable def pullback (D : Divisor K) : Divisor L :=
  Finsupp.ofSupportFinite (fun Q : Place L => (Q.ramificationIdx K : ℤ) * D (Q.restrict K)) (by
    refine (Set.Finite.biUnion D.support.finite_toSet
      fun P _ => Place.finite_setOf_restrict_eq K P).subset fun Q hQ => ?_
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hQ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      exists_prop]
    exact ⟨_, hQ.2, rfl⟩)

theorem pullback_apply (D : Divisor K) (Q : Place L) :
    pullback K D Q = (Q.ramificationIdx K : ℤ) * D (Q.restrict K) := rfl

theorem pullback_add (D₁ D₂ : Divisor K) :
    (pullback K (D₁ + D₂) : Divisor L) = pullback K D₁ + pullback K D₂ := by
  ext Q
  simp [pullback_apply, mul_add]

theorem pullback_sub (D₁ D₂ : Divisor K) :
    (pullback K (D₁ - D₂) : Divisor L) = pullback K D₁ - pullback K D₂ := by
  ext Q
  simp [pullback_apply, mul_sub]

theorem pullback_div (f : K) : pullback K (div f) = div (algebraMap K L f) := by
  ext Q
  rw [pullback_apply, div_apply, div_apply, Q.ord_algebraMap_eq_mul]

theorem pullback_polarDivisor (f : K) :
    pullback K (polarDivisor f) = polarDivisor (algebraMap K L f) := by
  ext Q
  rw [pullback_apply, polarDivisor_apply, polarDivisor_apply, Q.ord_algebraMap_eq_mul]
  have he : (0 : ℤ) ≤ Q.ramificationIdx K := Nat.cast_nonneg _
  rw [← mul_neg, mul_max_of_nonneg _ _ he, mul_zero]

/-- **Heights of pulled-back divisors**: `ht_{π^*D} ≈ ht_D ∘ π`. -/
theorem divHeight_pullback (D : Divisor K) :
    ∃ C, ∀ y : QbarPoint L, |divHeight (pullback K D) y - divHeight D (y.restrict K)| ≤ C := by
  set f := (polarRep D).1
  set g := (polarRep D).2
  obtain ⟨C, hC⟩ := divHeight_approx (pullback K D)
    (s := ![1, algebraMap K L f]) (s' := ![1, algebraMap K L g])
    (exists_ne_zero_pair_one _) (exists_ne_zero_pair_one _) one_ne_zero fun Q => by
      rw [minOrd_pair_one, minOrd_pair_one, Place.ord_one, add_zero,
        ← pullback_polarDivisor, ← pullback_polarDivisor]
      have := congrArg (fun E => (pullback K E : Divisor L) Q) (polarRep_spec D)
      simp only [pullback_sub, Finsupp.coe_sub, Pi.sub_apply] at this
      linarith
  refine ⟨C, fun y => ?_⟩
  have h := hC y
  have h1 : tupleHeight ![1, algebraMap K L f] y = tupleHeight ![1, f] (y.restrict K) := by
    rw [← tupleHeight_algebraMap]
    congr 1
    funext i
    fin_cases i <;> simp
  have h2 : tupleHeight ![1, algebraMap K L g] y = tupleHeight ![1, g] (y.restrict K) := by
    rw [← tupleHeight_algebraMap]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [h1, h2] at h
  exact h

/-- **Degrees of pulled-back divisors**: `deg π^*D = [L : K] · deg D`. -/
theorem deg_pullback (D : Divisor K) :
    (pullback K D : Divisor L).deg = Module.finrank K L * D.deg := by
  induction D using Finsupp.induction_linear with
  | zero =>
    have : (pullback K (0 : Divisor K) : Divisor L) = (0 : Divisor L) := by
      ext Q
      simp [pullback_apply]
    rw [this, deg_zero, deg_zero, mul_zero]
  | add D₁ D₂ h₁ h₂ => rw [pullback_add, deg_add, deg_add, h₁, h₂, mul_add]
  | single P n =>
    set S := (Place.finite_setOf_restrict_eq (L := L) K P).toFinset with hS
    have hsupp : (pullback K (Finsupp.single P n) : Divisor L).support ⊆ S := by
      intro Q hQ
      rw [Finsupp.mem_support_iff, pullback_apply] at hQ
      rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      by_contra hne
      apply hQ
      rw [Finsupp.single_eq_of_ne hne, mul_zero]
    rw [deg_eq_sum_of_support_subset _ hsupp, deg_single]
    have hsum := Place.sum_ramificationIdx_mul_deg (L := L) P
    have : ∀ Q ∈ S, (pullback K (Finsupp.single P n) : Divisor L) Q * (Q.deg : ℤ) =
        n * ((Q.ramificationIdx K * Q.deg : ℕ) : ℤ) := by
      intro Q hQ
      rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hQ
      rw [pullback_apply, hQ, Finsupp.single_eq_same]
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Nat.cast_sum, hsum]
    push_cast
    ring

end Heights.Curve
