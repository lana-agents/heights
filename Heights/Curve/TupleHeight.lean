/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.CurveField.Point
import Belyi.CurveField.ZerosPoles
import Heights.Absolute.Basic

/-!
# Heights of tuples of functions on a curve

Let `K` be the function field of a curve over a number field (`Belyi.CurveField`), and
`s : ι → K` a finite tuple of functions, not all zero. For an algebraic point `x` of the curve
(`Belyi.CurveField.QbarPoint K`: a place `P` of `K` with an embedding of its residue field
into `ℚ̄`), the tuple defines a point of `ℙ^ι(ℚ̄)`: divide by an entry `s i₀` of minimal
order at `P`, so that all quotients are regular at `P`, and evaluate. Its absolute logarithmic
Weil height is the *height of the tuple at `x`*,

`tupleHeight s x = h([s₀ : ⋯ : s_n](x))`.

This is the height attached to the divisor `A_s = −min_i div(s_i)` by the "linear system"
spanned by the `s_i` (no base-point condition is needed: dividing by an entry of minimal
order removes the base points). This file proves the basic calculus of these heights:

* `tupleHeight_eq_of_mul`: `tupleHeight s x` may be computed after multiplying by any
  `g ∈ K` making all `s_i g` regular at `x` and not all zero there;
* `tupleHeight_smul`: invariance under scaling by `c ∈ K ˣ` (principal divisors);
* `tupleHeight_mul`: the Segre identity `h_{s ⊗ t} = h_s + h_t`;
* `tupleHeight_pair_one`: `h_{(1, f)}(x) = h(f(x))` (the height of the value, `0` at poles).

## References

- [GenEll] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), Definition 1.2, Proposition 1.4.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

section Normalize

variable {ι : Type*} [Fintype ι] (P : Place K) (s : ι → K)

omit [CharZero K] [IsCurveField K] [Fintype ι] in
/-- A tuple is nonzero iff some entry is nonzero. -/
theorem exists_ne_zero_of_ne_zero {s : ι → K} (hs : s ≠ 0) : ∃ i, s i ≠ 0 := by
  by_contra h
  push Not at h
  exact hs (funext h)

omit [CharZero K] [IsCurveField K] in
open Classical in
theorem filter_ne_zero_nonempty {s : ι → K} (hs : ∃ i, s i ≠ 0) :
    (Finset.univ.filter fun i => s i ≠ 0).Nonempty := by
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, by simp [hi]⟩

open Classical in
/-- An index of an entry of minimal order at `P` among the nonzero entries. -/
noncomputable def normIdx (hs : ∃ i, s i ≠ 0) : ι :=
  (Finset.exists_min_image (Finset.univ.filter fun i => s i ≠ 0) (fun i => P.ord (s i))
    (filter_ne_zero_nonempty hs)).choose

variable {P s}

open Classical in
theorem normIdx_ne_zero (hs : ∃ i, s i ≠ 0) : s (normIdx P s hs) ≠ 0 := by
  have := (Finset.exists_min_image (Finset.univ.filter fun i => s i ≠ 0) (fun i => P.ord (s i))
    (filter_ne_zero_nonempty hs)).choose_spec.1
  exact (Finset.mem_filter.mp this).2

open Classical in
theorem ord_normIdx_le (hs : ∃ i, s i ≠ 0) {j : ι} (hj : s j ≠ 0) :
    P.ord (s (normIdx P s hs)) ≤ P.ord (s j) :=
  (Finset.exists_min_image (Finset.univ.filter fun i => s i ≠ 0) (fun i => P.ord (s i))
    (filter_ne_zero_nonempty hs)).choose_spec.2 j (by simp [hj])

open Classical in
/-- The minimal order `min_i ord_P(s_i)` over the nonzero entries (`0` for the zero tuple);
`−minOrd P s` is the multiplicity of `P` in the divisor `A_s`. -/
noncomputable def minOrd (P : Place K) (s : ι → K) : ℤ :=
  if hs : ∃ i, s i ≠ 0 then P.ord (s (normIdx P s hs)) else 0

open Classical in
theorem minOrd_eq (hs : ∃ i, s i ≠ 0) : minOrd P s = P.ord (s (normIdx P s hs)) := by
  simp [minOrd, hs]

theorem minOrd_le (hs : ∃ i, s i ≠ 0) {j : ι} (hj : s j ≠ 0) : minOrd P s ≤ P.ord (s j) := by
  rw [minOrd_eq hs]
  exact ord_normIdx_le hs hj

omit [Fintype ι] in
/-- All quotients by an entry of minimal order are regular. -/
theorem div_mem_of_minimal {i₀ : ι} (hi₀ : s i₀ ≠ 0) (hmin : ∀ j, s j ≠ 0 →
    P.ord (s i₀) ≤ P.ord (s j)) (j : ι) : s j / s i₀ ∈ P.1 := by
  rcases eq_or_ne (s j) 0 with h | h
  · rw [h, zero_div]
    exact zero_mem _
  · apply P.mem_of_ord_nonneg
    rw [P.ord_div h hi₀]
    linarith [hmin j h]

theorem div_normIdx_mem (hs : ∃ i, s i ≠ 0) (j : ι) : s j / s (normIdx P s hs) ∈ P.1 :=
  div_mem_of_minimal (normIdx_ne_zero hs) (fun _ hj => ord_normIdx_le hs hj) j

end Normalize

section Height

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The point `[s_i / s_{i₀}](x)` of `ℙ^ι(ℚ̄)`. -/
noncomputable def evalTuple (x : QbarPoint K) (s : ι → K) (hs : ∃ i, s i ≠ 0) : ι → Qbar :=
  fun j => x.eval (s j / s (normIdx x.P s hs)) (div_normIdx_mem hs j)

open Classical in
/-- **The height of the tuple `s` at the point `x`**: the absolute logarithmic Weil height of
`[s₀ : ⋯ : s_n](x)` (`0` for the zero tuple). -/
noncomputable def tupleHeight (s : ι → K) (x : QbarPoint K) : ℝ :=
  if hs : ∃ i, s i ≠ 0 then logHeight (evalTuple x s hs) else 0

open Classical in
theorem tupleHeight_def {s : ι → K} (hs : ∃ i, s i ≠ 0) (x : QbarPoint K) :
    tupleHeight s x = logHeight (evalTuple x s hs) := by
  simp [tupleHeight, hs]

open Classical in
theorem tupleHeight_nonneg (s : ι → K) (x : QbarPoint K) : 0 ≤ tupleHeight s x := by
  unfold tupleHeight
  split_ifs
  · exact logHeight_nonneg _
  · exact le_rfl

theorem evalTuple_normIdx (x : QbarPoint K) {u : ι → K} (hu : ∃ i, u i ≠ 0) :
    evalTuple x u hu (normIdx x.P u hu) = 1 := by
  simp only [evalTuple]
  rw [x.eval_congr (div_self (normIdx_ne_zero hu)), x.eval_one]

theorem evalTuple_ne_zero (x : QbarPoint K) {u : ι → K} (hu : ∃ i, u i ≠ 0) :
    evalTuple x u hu ≠ 0 := fun h => by
  have := congrFun h (normIdx x.P u hu)
  rw [evalTuple_normIdx] at this
  exact one_ne_zero this

/-- If `g ∈ K` is such that all `s_i g` are regular at `x`, then `ord_x(g s_{i₀}) ≥ 0` for an
entry of minimal order, with equality iff some `(s_i g)(x) ≠ 0`. -/
theorem tupleHeight_eq_of_mul {s : ι → K} (hs : ∃ i, s i ≠ 0) (x : QbarPoint K) (g : K)
    (hmem : ∀ j, s j * g ∈ x.P.1) (hne : ∃ j, x.eval (s j * g) (hmem j) ≠ 0) :
    tupleHeight s x = logHeight (fun j => x.eval (s j * g) (hmem j)) := by
  rw [tupleHeight_def hs]
  set i₀ := normIdx x.P s hs with hi₀
  have hs₀ : s i₀ ≠ 0 := normIdx_ne_zero hs
  have hg : g ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne
    apply hj
    have : x.eval (s j * 0) (hmem j) = x.eval 0 x.P.1.zero_mem :=
      x.eval_congr (by rw [mul_zero]) _
    rw [this, x.eval_zero]
  -- `u = s_{i₀} g` is a unit at `x`
  set u := s i₀ * g with hu
  have hu0 : u ≠ 0 := mul_ne_zero hs₀ hg
  have hfac : ∀ j, s j * g = s j / s i₀ * u := fun j => by
    rw [hu]
    field_simp
  have hord : x.P.ord u = 0 := by
    have h0 : 0 ≤ x.P.ord u := x.P.ord_nonneg_of_mem (hmem i₀)
    by_contra hne0
    have hpos : 0 < x.P.ord u := lt_of_le_of_ne h0 (Ne.symm hne0)
    obtain ⟨j, hj⟩ := hne
    apply hj
    rw [x.eval_eq_zero_iff']
    rcases eq_or_ne (s j) 0 with hsj | hsj
    · left
      rw [hsj, zero_mul]
    · right
      rw [hfac j, x.P.ord_mul (div_ne_zero hsj hs₀) hu0]
      have := x.P.ord_nonneg_of_mem (div_normIdx_mem (P := x.P) hs j)
      linarith
  have humem : u ∈ x.P.1 := hmem i₀
  have hueval : x.eval u humem ≠ 0 := by
    rw [Ne, x.eval_eq_zero_iff humem hu0]
    omega
  have : (fun j => x.eval (s j * g) (hmem j)) = x.eval u humem • evalTuple x s hs := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, evalTuple]
    rw [← x.eval_mul humem (div_normIdx_mem hs j)]
    exact x.eval_congr (by rw [hfac j, mul_comm]) _
  rw [this, logHeight_smul _ hueval]

/-- **Scaling invariance**: `h_{c s} = h_s` for `c ≠ 0` (the divisors `A_{cs} = A_s − div c`
are linearly equivalent). -/
theorem tupleHeight_smul {s : ι → K} (x : QbarPoint K) {c : K} (hc : c ≠ 0) :
    tupleHeight (fun j => c * s j) x = tupleHeight s x := by
  by_cases hs : ∃ i, s i ≠ 0
  · have hcs : ∃ i, c * s i ≠ 0 := by
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, mul_ne_zero hc hi⟩
    set i₀ := normIdx x.P s hs
    have hs₀ : s i₀ ≠ 0 := normIdx_ne_zero hs
    set g := (c * s i₀)⁻¹ with hg
    have hcg : ∀ j, c * s j * g = s j / s i₀ := fun j => by
      rw [hg]
      field_simp
    have hmem : ∀ j, c * s j * g ∈ x.P.1 := fun j => by
      rw [hcg j]
      exact div_normIdx_mem hs j
    have hne : ∃ j, x.eval (c * s j * g) (hmem j) ≠ 0 := by
      refine ⟨i₀, ?_⟩
      have : c * s i₀ * g = 1 := by
        rw [hg]
        exact mul_inv_cancel₀ (mul_ne_zero hc hs₀)
      rw [x.eval_congr this, x.eval_one]
      exact one_ne_zero
    rw [tupleHeight_eq_of_mul hcs x g hmem hne, tupleHeight_def hs]
    congr 1
    funext j
    exact x.eval_congr (hcg j) _
  · simp [tupleHeight, hs]

/-- **The Segre identity**: `h_{(s_i t_j)} = h_s + h_t` (the divisor of the product linear
system is `A_s + A_t`). -/
theorem tupleHeight_mul {s : ι → K} {t : κ → K} (hs : ∃ i, s i ≠ 0) (ht : ∃ j, t j ≠ 0)
    (x : QbarPoint K) :
    tupleHeight (fun p : ι × κ => s p.1 * t p.2) x = tupleHeight s x + tupleHeight t x := by
  set i₀ := normIdx x.P s hs
  set j₀ := normIdx x.P t ht
  have hs₀ : s i₀ ≠ 0 := normIdx_ne_zero hs
  have ht₀ : t j₀ ≠ 0 := normIdx_ne_zero ht
  have hst : ∃ p : ι × κ, s p.1 * t p.2 ≠ 0 := ⟨(i₀, j₀), mul_ne_zero hs₀ ht₀⟩
  set g := (s i₀ * t j₀)⁻¹ with hg
  have hfac : ∀ p : ι × κ, s p.1 * t p.2 * g = s p.1 / s i₀ * (t p.2 / t j₀) := fun p => by
    rw [hg]
    field_simp
  have hmem : ∀ p : ι × κ, s p.1 * t p.2 * g ∈ x.P.1 := fun p => by
    rw [hfac p]
    exact mul_mem (div_normIdx_mem hs p.1) (div_normIdx_mem ht p.2)
  have hval : ∀ p : ι × κ, x.eval (s p.1 * t p.2 * g) (hmem p) =
      evalTuple x s hs p.1 * evalTuple x t ht p.2 := fun p => by
    rw [x.eval_congr (hfac p), x.eval_mul (div_normIdx_mem hs p.1) (div_normIdx_mem ht p.2)]
    rfl
  have hne : ∃ p, x.eval (s p.1 * t p.2 * g) (hmem p) ≠ 0 := by
    refine ⟨(i₀, j₀), ?_⟩
    rw [hval, evalTuple_normIdx x hs, evalTuple_normIdx x ht, one_mul]
    exact one_ne_zero
  rw [tupleHeight_eq_of_mul hst x g hmem hne, tupleHeight_def hs, tupleHeight_def ht]
  simp only [hval]
  exact logHeight_mul_table (evalTuple_ne_zero x hs) (evalTuple_ne_zero x ht)

/-- **Heights of values**: `h_{(1, f)}(x) = h(f(x))` if `f` is regular at `x`. -/
theorem tupleHeight_pair_one_of_mem (x : QbarPoint K) {f : K} (hf : f ∈ x.P.1) :
    tupleHeight ![1, f] x = logHeight ![1, x.eval f hf] := by
  have hs : ∃ i, (![1, f] : Fin 2 → K) i ≠ 0 := ⟨0, by simp⟩
  have hmem : ∀ j, (![1, f] : Fin 2 → K) j * 1 ∈ x.P.1 := fun j => by
    fin_cases j
    · simp
    · simpa using hf
  have hne : ∃ j, x.eval ((![1, f] : Fin 2 → K) j * 1) (hmem j) ≠ 0 := by
    refine ⟨0, ?_⟩
    rw [x.eval_congr (by simp : (![1, f] : Fin 2 → K) 0 * 1 = 1), x.eval_one]
    exact one_ne_zero
  rw [tupleHeight_eq_of_mul hs x 1 hmem hne]
  congr 1
  funext j
  fin_cases j
  · exact (x.eval_congr (by simp) _).trans x.eval_one
  · exact x.eval_congr (by simp) _

/-- At a pole of `f`, `h_{(1, f)}(x) = 0` (the value is `∞ = [0 : 1]`). -/
theorem tupleHeight_pair_one_of_notMem (x : QbarPoint K) {f : K} (hf : f ∉ x.P.1) :
    tupleHeight ![1, f] x = 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ x.P.1.zero_mem)
  have hfi : f⁻¹ ∈ x.P.1 := (x.P.mem_or_inv_mem f).resolve_left hf
  have hs : ∃ i, (![1, f] : Fin 2 → K) i ≠ 0 := ⟨0, by simp⟩
  have hmem : ∀ j, (![1, f] : Fin 2 → K) j * f⁻¹ ∈ x.P.1 := fun j => by
    fin_cases j
    · simpa using hfi
    · simp [hf0]
  have hne : ∃ j, x.eval ((![1, f] : Fin 2 → K) j * f⁻¹) (hmem j) ≠ 0 := by
    refine ⟨1, ?_⟩
    rw [x.eval_congr (by simp [hf0] : (![1, f] : Fin 2 → K) 1 * f⁻¹ = 1), x.eval_one]
    exact one_ne_zero
  rw [tupleHeight_eq_of_mul hs x f⁻¹ hmem hne]
  have h0 : x.eval ((![1, f] : Fin 2 → K) 0 * f⁻¹) (hmem 0) = 0 := by
    rw [x.eval_eq_zero_iff']
    right
    have : (![1, f] : Fin 2 → K) 0 * f⁻¹ = f⁻¹ := by simp
    rw [this, x.P.ord_inv]
    have := (x.P.ord_neg_iff).mpr hf
    omega
  have h1 : x.eval ((![1, f] : Fin 2 → K) 1 * f⁻¹) (hmem 1) = 1 := by
    rw [x.eval_congr (by simp [hf0] : (![1, f] : Fin 2 → K) 1 * f⁻¹ = 1), x.eval_one]
  have : (fun j => x.eval ((![1, f] : Fin 2 → K) j * f⁻¹) (hmem j)) = ![0, 1] := by
    funext j
    fin_cases j
    · exact h0
    · exact h1
  rw [this]
  have hswap : (![0, 1] : Fin 2 → Qbar) = ![1, 0] ∘ Equiv.swap 0 1 := by
    funext j
    fin_cases j <;> rfl
  rw [hswap, logHeight_comp_equiv, logHeight_one_zero]

end Height

end Heights.Curve
