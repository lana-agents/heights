/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.TupleHeight

/-!
# Log-differents and log-conductors of algebraic points

Following [GenEll], Definition 1.5, for an algebraic point `x` of a curve with minimal field of
definition `ℚ(x)` (`Belyi.CurveField.QbarPoint.fieldOf`):

* the **log-different** `log-diff(x) = log |disc ℚ(x)| / [ℚ(x) : ℚ]`
  (`Heights.Curve.logDiff`), the normalised degree of the different of `ℚ(x)`;
* the **log-conductor** of a reduced divisor `D` at `x`: the normalised sum of `log N(w)` over
  the finite places `w` of `ℚ(x)` at which `x` meets `D`. "Meeting `D` at `w`" refers to an
  integral model of `(X, D)`; we use the model given by a finite set `G` of generators of the
  coordinate ring `𝒪(X ∖ D)` (the closure of `X ∖ D ↪ 𝔸^G`): `x` meets `D` at `w` iff
  `|g(x)|_w > 1` for some `g ∈ G` (`Heights.Curve.logCondOf`). Different models give
  log-conductors differing by a bounded amount ([GenEll], Remark 1.5.1).

For the tripod `(ℙ¹, {0, 1, ∞})` with the generators `λ, λ⁻¹, (1 − λ)⁻¹` of
`ℚ[λ, λ⁻¹, (1 − λ)⁻¹]`, the condition "`|g(x)|_w > 1` for some generator" is exactly
"`|λ(x)|_w ≠ 1` or `|λ(x) − 1|_w ≠ 1`" (`Heights.Curve.exists_one_lt_iff_tripod`), the
condition used by `Iut.Tripod.logCond`.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute NumberField
open scoped Classical

/-! ### Number field lemmas -/

section NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- For the three generators of the coordinate ring of the tripod, some generator has
`|·|_w > 1` iff `|z|_w ≠ 1` or `|z − 1|_w ≠ 1`. -/
theorem exists_one_lt_iff_tripod (w : FinitePlace F) {z : F} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (1 < w z ∨ 1 < w z⁻¹ ∨ 1 < w (1 - z)⁻¹) ↔ (w z ≠ 1 ∨ w (z - 1) ≠ 1) := by
  have hwz : 0 < w z := w.pos_iff.mpr hz0
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hwz1 : 0 < w (z - 1) := w.pos_iff.mpr hsub
  have hneg : w (1 - z) = w (z - 1) := by rw [← neg_sub, map_neg_eq_map]
  rw [map_inv₀, map_inv₀, hneg, one_lt_inv₀ hwz, one_lt_inv₀ hwz1]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h.ne'
    · exact Or.inl h.ne
    · exact Or.inr h.ne
  · rintro (h | h)
    · rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
    · rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr (Or.inr h')
      · -- `|z − 1|_w > 1` forces `|z|_w > 1`
        left
        have hle : w (z - 1) ≤ max (w z) (w (-1 : F)) := by
          have := w.add_le z (-1)
          simpa [sub_eq_add_neg] using this
        rw [map_neg_eq_map, map_one] at hle
        rcases le_max_iff.mp hle with h1 | h1
        · linarith
        · linarith

end NumberField

/-! ### Log-differents and log-conductors of points -/

section Points

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- **The log-different** of an algebraic point: `log |disc ℚ(x)| / [ℚ(x) : ℚ]`
([GenEll], Definition 1.5 (iii)). -/
noncomputable def logDiff (x : QbarPoint K) : ℝ :=
  Real.log |(discr x.fieldOf : ℝ)| / x.deg

theorem logDiff_nonneg (x : QbarPoint K) : 0 ≤ logDiff x := by
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (discr_ne_zero x.fieldOf)

/-- The finite places of `ℚ(x)` at which `x` meets the divisor at infinity of the affine model
given by the functions `G`: those `w` with `|g(x)|_w > 1` for some `g ∈ G` (all `g ∈ G` are
assumed regular at `x`, i.e. `x ∈ X ∖ D`). -/
def meetsAt (x : QbarPoint K) (G : Finset K) (hG : ∀ g ∈ G, g ∈ x.P.1) :
    Set (FinitePlace x.fieldOf) :=
  {w | ∃ g, ∃ hg : g ∈ G, 1 < w ⟨x.eval g (hG g hg), x.eval_mem_fieldOf _⟩}

/-- **The log-conductor** of a point with respect to the model given by the generators `G` of
the coordinate ring of `X ∖ D` ([GenEll], Definition 1.5 (iv)); `0` if some `g ∈ G` has a pole
at `x` (i.e. `x ∈ D`). -/
noncomputable def logCondOf (G : Finset K) (x : QbarPoint K) : ℝ :=
  if hG : ∀ g ∈ G, g ∈ x.P.1 then
    (∑ᶠ w : FinitePlace x.fieldOf,
      if w ∈ meetsAt x G hG then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) / x.deg
  else 0

theorem logCondOf_nonneg (G : Finset K) (x : QbarPoint K) : 0 ≤ logCondOf G x := by
  unfold logCondOf
  split_ifs with hG
  · refine div_nonneg (finsum_nonneg fun w => ?_) (Nat.cast_nonneg _)
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast
        (NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal).le)
    · exact le_rfl
  · exact le_rfl

end Points

end Heights.Curve
