/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.LinearEquiv
import Belyi.CurveField.Riemann

/-!
# Heights attached to divisors on curves (the Weil height machine)

By Riemann's theorem every divisor `D` of a curve is a difference of polar divisors,
`D = (f)_∞ − (g)_∞` (`Belyi.CurveField.Divisor.exists_eq_polarDivisor_sub_polarDivisor`), and
`(f)_∞ = A_{(1,f)}` is the divisor of the tuple `(1, f)`. We define

`divHeight D x = h([1 : f(x)]) − h([1 : g(x)])`

for a chosen such representation. By the comparison theorem for tuples
(`Heights.Curve.abs_tupleHeight_sub_sub_le`), whenever `D + div r = A_s − A_{s'}` for tuples
`s`, `s'`, the function `divHeight D` differs from `h_s − h_{s'}` by a bounded amount
(`Heights.Curve.divHeight_approx`); hence the BD-class of `divHeight D` is independent of all
choices and depends only on the linear equivalence class of `D`. This is the height
`ht_{𝒪(D)}` of [GenEll], Definition 1.2 (i), up to bounded discrepancy (Proposition 1.4 (iii),
Remark 1.4.1).

## Main results

* `divHeight_approx`: the BD-class of `divHeight D` is that of `h_s − h_{s'}` for any tuples
  with `D ~ A_s − A_{s'}`;
* `divHeight_add`, `divHeight_div`, `divHeight_polar`, `divHeight_nsmul`, `divHeight_sub_div`:
  additivity, principal divisors, polar divisors, multiples, linear equivalence
  ([GenEll], Proposition 1.4 (i), (iii));
* `divHeight_bddBelow`: a divisor of positive degree has height bounded below
  ([GenEll], Proposition 1.4 (ii));
* `divHeight_le_mul`: if `deg A < q · deg B` with `deg B > 0`, then
  `ht_A ≲ q · ht_B`.
-/

namespace Heights.Curve

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Absolute
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-! ### Divisors of small tuples -/

theorem exists_ne_zero_pair_one (f : K) : ∃ i, (![1, f] : Fin 2 → K) i ≠ 0 := ⟨0, by simp⟩

/-- The divisor of the tuple `(1, f)` is the polar divisor of `f`. -/
theorem minOrd_pair_one (f : K) (P : Place K) : minOrd P ![1, f] = -polarDivisor f P := by
  rw [polarDivisor_apply]
  have hs := exists_ne_zero_pair_one f
  have hle0 : minOrd P ![1, f] ≤ 0 := by
    have := minOrd_le (P := P) hs (j := 0) (by simp)
    simpa using this
  obtain ⟨j, hj, hmin⟩ : ∃ j, (![1, f] : Fin 2 → K) j ≠ 0 ∧
      minOrd P ![1, f] = P.ord ((![1, f] : Fin 2 → K) j) :=
    ⟨normIdx P ![1, f] hs, normIdx_ne_zero hs, minOrd_eq hs⟩
  rcases eq_or_ne f 0 with hf | hf
  · subst hf
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Place.ord_one] at hmin
      simp [hmin]
    · simp at hj
  · have hlef : minOrd P ![1, f] ≤ P.ord f := by
      have := minOrd_le (P := P) hs (j := 1) (by simpa using hf)
      simpa using this
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Place.ord_one] at hmin
      rw [hmin] at hlef ⊢
      omega
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hmin
      rw [hmin] at hle0 ⊢
      omega

/-- A one-entry tuple `(r)` has divisor `−div r`. -/
theorem minOrd_single {r : K} (hr : r ≠ 0) (P : Place K) : minOrd P ![r] = P.ord r := by
  have hs : ∃ i, (![r] : Fin 1 → K) i ≠ 0 := ⟨0, by simpa using hr⟩
  rw [minOrd_eq hs]
  have : normIdx P ![r] hs = 0 := Subsingleton.elim _ _
  rw [this]
  rfl

/-- The height of a point of `ℙ⁰` is `0`. -/
theorem tupleHeight_single {r : K} (hr : r ≠ 0) (x : QbarPoint K) : tupleHeight ![r] x = 0 := by
  have hs : ∃ i, (![r] : Fin 1 → K) i ≠ 0 := ⟨0, by simpa using hr⟩
  rw [tupleHeight_def hs, Heights.Absolute.logHeight, Height.logHeight_eq_zero_of_subsingleton,
    zero_div]

/-! ### The height of a divisor -/

/-- A chosen representation `D = (f)_∞ − (g)_∞`. -/
noncomputable def polarRep (D : Divisor K) : K × K :=
  ((exists_eq_polarDivisor_sub_polarDivisor D).choose,
    (exists_eq_polarDivisor_sub_polarDivisor D).choose_spec.choose)

theorem polarRep_spec (D : Divisor K) :
    D = polarDivisor (polarRep D).1 - polarDivisor (polarRep D).2 :=
  (exists_eq_polarDivisor_sub_polarDivisor D).choose_spec.choose_spec

/-- **The height attached to a divisor** `D` on the curve with function field `K`:
`divHeight D x = h([1 : f(x)]) − h([1 : g(x)])` for the chosen representation
`D = (f)_∞ − (g)_∞`. Its BD-class is the height `ht_{𝒪(D)}` of [GenEll], Definition 1.2 (i). -/
noncomputable def divHeight (D : Divisor K) (x : QbarPoint K) : ℝ :=
  tupleHeight ![1, (polarRep D).1] x - tupleHeight ![1, (polarRep D).2] x

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The height of a divisor is the height of any representation by tuples**: if
`D + div r = A_s − A_{s'}`, then `divHeight D ≈ h_s − h_{s'}`. -/
theorem divHeight_approx (D : Divisor K) {s : ι → K} {s' : κ → K} (hs : ∃ i, s i ≠ 0)
    (hs' : ∃ i, s' i ≠ 0) {r : K} (hr : r ≠ 0)
    (hD : ∀ P : Place K, D P + P.ord r = minOrd P s' - minOrd P s) :
    ∃ C, ∀ x : QbarPoint K, |divHeight D x - (tupleHeight s x - tupleHeight s' x)| ≤ C := by
  have hrep := polarRep_spec D
  refine abs_tupleHeight_sub_sub_le (exists_ne_zero_pair_one _) (exists_ne_zero_pair_one _)
    hs hs' hr fun P => ?_
  have h1 := congrArg (fun E : Divisor K => E P) hrep
  simp only [Finsupp.coe_sub, Pi.sub_apply] at h1
  rw [minOrd_pair_one, minOrd_pair_one]
  have := hD P
  linarith

/-- The height of a principal divisor is bounded. -/
theorem divHeight_div {r : K} (hr : r ≠ 0) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (div r) x| ≤ C := by
  have h1 : ∃ i, (![1] : Fin 1 → K) i ≠ 0 := ⟨0, by simp⟩
  obtain ⟨C, hC⟩ := divHeight_approx (div r) h1 h1 (inv_ne_zero hr) fun P => by
    rw [div_apply, Place.ord_inv]
    ring
  exact ⟨C, fun x => by simpa using hC x⟩

/-- The height of a polar divisor is the height of the values. -/
theorem divHeight_polar (f : K) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (polarDivisor f) x - tupleHeight ![1, f] x| ≤ C := by
  have h1 : ∃ i, (![1] : Fin 1 → K) i ≠ 0 := ⟨0, by simp⟩
  obtain ⟨C, hC⟩ := divHeight_approx (polarDivisor f) (exists_ne_zero_pair_one f) h1 one_ne_zero
    fun P => by
      rw [minOrd_pair_one, minOrd_single one_ne_zero, Place.ord_one]
      ring
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rwa [tupleHeight_single one_ne_zero, sub_zero] at this

/-- **Additivity** ([GenEll], Proposition 1.4 (i)). -/
theorem divHeight_add (D₁ D₂ : Divisor K) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (D₁ + D₂) x - (divHeight D₁ x + divHeight D₂ x)| ≤ C := by
  set f₁ := (polarRep D₁).1
  set g₁ := (polarRep D₁).2
  set f₂ := (polarRep D₂).1
  set g₂ := (polarRep D₂).2
  have hS := exists_ne_zero_pair_one f₁
  obtain ⟨C, hC⟩ := divHeight_approx (D₁ + D₂)
    (s := fun p : Fin 2 × Fin 2 => (![1, f₁] : Fin 2 → K) p.1 * (![1, f₂] : Fin 2 → K) p.2)
    (s' := fun p : Fin 2 × Fin 2 => (![1, g₁] : Fin 2 → K) p.1 * (![1, g₂] : Fin 2 → K) p.2)
    ⟨(0, 0), by simp⟩ ⟨(0, 0), by simp⟩ one_ne_zero fun P => by
      rw [minOrd_mul (exists_ne_zero_pair_one _) (exists_ne_zero_pair_one _),
        minOrd_mul (exists_ne_zero_pair_one _) (exists_ne_zero_pair_one _),
        minOrd_pair_one, minOrd_pair_one, minOrd_pair_one, minOrd_pair_one, Place.ord_one]
      have h1 := congrArg (fun E : Divisor K => E P) (polarRep_spec D₁)
      have h2 := congrArg (fun E : Divisor K => E P) (polarRep_spec D₂)
      simp only [Finsupp.coe_sub, Pi.sub_apply] at h1 h2
      simp only [Finsupp.coe_add, Pi.add_apply]
      linarith
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rw [tupleHeight_mul (exists_ne_zero_pair_one _) (exists_ne_zero_pair_one _),
    tupleHeight_mul (exists_ne_zero_pair_one _) (exists_ne_zero_pair_one _)] at this
  calc |divHeight (D₁ + D₂) x - (divHeight D₁ x + divHeight D₂ x)|
      = |divHeight (D₁ + D₂) x - ((tupleHeight ![1, f₁] x + tupleHeight ![1, f₂] x) -
          (tupleHeight ![1, g₁] x + tupleHeight ![1, g₂] x))| := by
        congr 2
        simp only [divHeight]
        ring
    _ ≤ C := this

/-- The height of the zero divisor is bounded. -/
theorem divHeight_zero : ∃ C, ∀ x : QbarPoint K, |divHeight (0 : Divisor K) x| ≤ C := by
  have := divHeight_div (K := K) one_ne_zero
  simpa using this

/-- **Linear equivalence** ([GenEll], Proposition 1.4 (iii)): `D ~ D'` implies
`divHeight D ≈ divHeight D'`. -/
theorem divHeight_add_div (D : Divisor K) {r : K} (hr : r ≠ 0) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (D + div r) x - divHeight D x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := divHeight_add D (div r)
  obtain ⟨C₂, hC₂⟩ := divHeight_div hr
  refine ⟨C₁ + C₂, fun x => ?_⟩
  have h1 := hC₁ x
  have h2 := hC₂ x
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

/-- Heights of multiples. -/
theorem divHeight_nsmul (D : Divisor K) (n : ℕ) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (n • D) x - n * divHeight D x| ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := divHeight_zero (K := K)
    exact ⟨C, fun x => by simpa using hC x⟩
  | succ n ih =>
    obtain ⟨C₁, hC₁⟩ := ih
    obtain ⟨C₂, hC₂⟩ := divHeight_add (n • D) D
    refine ⟨C₁ + C₂, fun x => ?_⟩
    have h1 := hC₁ x
    have h2 := hC₂ x
    rw [succ_nsmul]
    push_cast
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith

/-- Heights of differences. -/
theorem divHeight_sub (D₁ D₂ : Divisor K) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (D₁ - D₂) x - (divHeight D₁ x - divHeight D₂ x)| ≤ C := by
  obtain ⟨C, hC⟩ := divHeight_add (D₁ - D₂) D₂
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rw [sub_add_cancel] at this
  rw [abs_le] at this ⊢
  constructor <;> linarith

/-- Heights of integer multiples. -/
theorem divHeight_zsmul' (D : Divisor K) (n : ℤ) :
    ∃ C, ∀ x : QbarPoint K, |divHeight (n • D) x - n * divHeight D x| ≤ C := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · obtain ⟨C, hC⟩ := divHeight_nsmul D m
    exact ⟨C, fun x => by simpa [natCast_zsmul] using hC x⟩
  · obtain ⟨C₁, hC₁⟩ := divHeight_nsmul D m
    obtain ⟨C₂, hC₂⟩ := divHeight_sub 0 ((m : ℤ) • D)
    obtain ⟨C₃, hC₃⟩ := divHeight_zero (K := K)
    refine ⟨C₁ + C₂ + C₃, fun x => ?_⟩
    have h1 := hC₁ x
    have h2 := hC₂ x
    have h3 := hC₃ x
    rw [zero_sub, ← neg_zsmul] at h2
    rw [natCast_zsmul] at h2
    push_cast
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> linarith

/-- **Positivity** ([GenEll], Proposition 1.4 (ii)): a divisor of positive degree has height
bounded below. -/
theorem divHeight_bddBelow {A : Divisor K} (hA : 0 < A.deg) :
    ∃ C, ∀ x : QbarPoint K, -C ≤ divHeight A x := by
  obtain ⟨n, hn, f, r, hr, hf⟩ := exists_polarDivisor_eq_nsmul_add_div hA
  obtain ⟨C₁, hC₁⟩ := divHeight_polar (K := K) f
  obtain ⟨C₂, hC₂⟩ := divHeight_add_div (n • A) hr
  obtain ⟨C₃, hC₃⟩ := divHeight_nsmul A n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨(C₁ + C₂ + C₃) / n, fun x => ?_⟩
  have h1 := hC₁ x
  have h2 := hC₂ x
  have h3 := hC₃ x
  rw [← hf] at h2
  rw [abs_le] at h1 h2 h3
  have h0 := tupleHeight_nonneg ![1, f] x
  rw [neg_le, le_div_iff₀ hnpos]
  nlinarith

/-- **Comparison of heights of divisors by degree**: if `deg B > 0` and `deg A < q · deg B`,
then `ht_A ≲ q · ht_B`. -/
theorem divHeight_le_mul {A B : Divisor K} (hB : 0 < B.deg) {q : ℝ}
    (hq : (A.deg : ℝ) < q * B.deg) :
    ∃ C, ∀ x : QbarPoint K, divHeight A x ≤ q * divHeight B x + C := by
  have hBR : (0 : ℝ) < B.deg := by exact_mod_cast hB
  -- a rational `a / b` with `deg A / deg B < a / b < q`
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (show (A.deg : ℝ) / B.deg < q by
    rw [div_lt_iff₀ hBR]; exact hq)
  set a : ℤ := ρ.num
  set b : ℕ := ρ.den
  have hb : (0 : ℝ) < b := by exact_mod_cast ρ.den_pos
  have hρ : (ρ : ℝ) = a / b := by
    rw [Rat.cast_def]
  -- `a • B − b • A` has positive degree
  set D : Divisor K := a • B - (b : ℤ) • A
  have hD : 0 < D.deg := by
    have h1 : (A.deg : ℝ) * b < a * B.deg := by
      rw [hρ, lt_div_iff₀ hb] at hρ1
      have := mul_lt_mul_of_pos_right hρ1 hBR
      have h2 : (A.deg : ℝ) / B.deg * b * B.deg = A.deg * b := by
        field_simp
      linarith
    simp only [D, deg_sub, deg_zsmul]
    have : ((b : ℤ) * A.deg : ℝ) < a * B.deg := by push_cast; linarith
    exact_mod_cast (by linarith : (0 : ℝ) < a * B.deg - b * A.deg)
  obtain ⟨C₁, hC₁⟩ := divHeight_bddBelow hD
  obtain ⟨C₂, hC₂⟩ := divHeight_sub (a • B) ((b : ℤ) • A)
  obtain ⟨C₃, hC₃⟩ := divHeight_zsmul' B a
  obtain ⟨C₄, hC₄⟩ := divHeight_zsmul' A b
  obtain ⟨C₅, hC₅⟩ := divHeight_bddBelow hB
  have hqρ : (0 : ℝ) < q - a / b := by rw [← hρ]; linarith
  refine ⟨(C₁ + C₂ + C₃ + C₄) / b + (q - a / b) * C₅, fun x => ?_⟩
  have h1 := hC₁ x
  have h2 := hC₂ x
  have h3 := hC₃ x
  have h4 := hC₄ x
  have h5 := hC₅ x
  rw [abs_le] at h2 h3 h4
  -- `b · ht_A ≤ a · ht_B + const`
  have key : (b : ℝ) * divHeight A x ≤ a * divHeight B x + (C₁ + C₂ + C₃ + C₄) := by
    push_cast at h4
    linarith
  have key' : divHeight A x ≤ (a / b) * divHeight B x + (C₁ + C₂ + C₃ + C₄) / b := by
    rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hb]
    linarith
  have : (a / b : ℝ) * divHeight B x ≤ q * divHeight B x + (q - a / b) * C₅ := by
    nlinarith
  linarith

end Heights.Curve
