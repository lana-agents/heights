/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.CondHeight
import Heights.Curve.DivisorHeight
import Heights.Different.Conductor

/-!
# Log-conductors of effective divisors

* `Heights.Curve.logCondOf_le_divHeight`: **[GenEll], Proposition 1.6 for divisors**: for an
  effective divisor `E` and a finite set `G` of functions regular off `supp E` (e.g. generators
  of `𝒪(X ∖ E)`), `log-cond_G ≲ ht_E` on the points where the `g ∈ G` are regular.
* `Heights.Curve.logCondOf_eq_cond`: the log-conductor of a point with respect to `G` is the
  log-conductor (`Heights.Different.cond`) of the finite set of values `g(x) ∈ ℚ(x)`, `g ∈ G`.
-/

namespace Heights.Curve

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Absolute NumberField
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- The minimal order of `(1, g, f)` is the minimum of those of `(1, g)` and `(1, f)`. -/
theorem minOrd_triple_one (g f : K) (P : Place K) :
    minOrd P ![1, g, f] = min (minOrd P ![1, g]) (minOrd P ![1, f]) := by
  have hs : ∃ i, (![1, g, f] : Fin 3 → K) i ≠ 0 := ⟨0, by simp⟩
  have hg : ![(1 : K), g, f] ∘ ![0, 1] = ![1, g] := by
    funext j; fin_cases j <;> rfl
  have hf : ![(1 : K), g, f] ∘ ![0, 2] = ![1, f] := by
    funext j; fin_cases j <;> rfl
  apply le_antisymm
  · refine le_min ?_ ?_
    · have := minOrd_le_minOrd_comp hs ![0, 1] (by rw [hg]; exact exists_ne_zero_pair_one g) P
      rwa [hg] at this
    · have := minOrd_le_minOrd_comp hs ![0, 2] (by rw [hf]; exact exists_ne_zero_pair_one f) P
      rwa [hf] at this
  · rw [minOrd_eq hs]
    have hne := normIdx_ne_zero (P := P) hs
    generalize normIdx P ![1, g, f] hs = i at hne ⊢
    have hg1 := minOrd_le (P := P) (exists_ne_zero_pair_one g) (j := 0) (by simp)
    have hf1 := minOrd_le (P := P) (exists_ne_zero_pair_one f) (j := 0) (by simp)
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Place.ord_one] at hg1 ⊢
      exact min_le_of_left_le (by simpa using hg1)
    · have hg0 : g ≠ 0 := by simpa using hne
      have := minOrd_le (P := P) (exists_ne_zero_pair_one g) (j := 1) (by simpa using hg0)
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at this ⊢
      exact min_le_of_left_le this
    · have hf0 : f ≠ 0 := by simpa using hne
      have := minOrd_le (P := P) (exists_ne_zero_pair_one f) (j := 1) (by simpa using hf0)
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact min_le_of_right_le this

/-- **[GenEll], Proposition 1.6 for effective divisors**: `log-cond_G ≲ ht_E` for a finite set
`G` of functions regular off the support of the effective divisor `E`. -/
theorem logCondOf_le_divHeight (E : Divisor K) (hE : 0 ≤ E) (G : Finset K)
    (hG : ∀ P : Place K, E P = 0 → ∀ g ∈ G, g ∈ P.1) :
    ∃ C, ∀ x : QbarPoint K, (∀ g ∈ G, g ∈ x.P.1) → logCondOf G x ≤ divHeight E x + C := by
  set f := (polarRep E).1
  set g := (polarRep E).2
  have hrep : E = polarDivisor f - polarDivisor g := polarRep_spec E
  have hEP : ∀ P, E P = polarDivisor f P - polarDivisor g P := fun P => by
    rw [hrep]; rfl
  have hs : ∃ i, (![1, g, f] : Fin 3 → K) i ≠ 0 := ⟨0, by simp⟩
  have hcomp : ![(1 : K), g, f] ∘ ![0, 1] = ![1, g] := by
    funext j; fin_cases j <;> rfl
  have hmin : ∀ P : Place K, minOrd P ![1, g, f] = -polarDivisor f P := fun P => by
    rw [minOrd_triple_one, minOrd_pair_one, minOrd_pair_one]
    have := hEP P
    have := hE P
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  obtain ⟨C₁, hC₁⟩ := logCondOf_le_tupleHeight_sub hs ![0, 1]
    (by rw [hcomp]; exact exists_ne_zero_pair_one g) G fun P hP => by
      rw [hcomp, hmin, minOrd_pair_one] at hP
      exact hG P (by rw [hEP]; omega)
  obtain ⟨C₂, hC₂⟩ := divHeight_approx E hs (exists_ne_zero_pair_one g) one_ne_zero fun P => by
    rw [hmin, minOrd_pair_one, Place.ord_one, hEP]
    ring
  refine ⟨C₁ + C₂, fun x hx => ?_⟩
  have h1 := hC₁ x hx
  have h2 := hC₂ x
  rw [hcomp] at h1
  rw [abs_le] at h2
  linarith [h2.1]

/-- **The log-conductor of a point is the log-conductor of the values**: `log-cond_G(x)` is
`Heights.Different.cond` of the finite set `{g(x) : g ∈ G} ⊆ ℚ(x)`. -/
theorem logCondOf_eq_cond (G : Finset K) (x : QbarPoint K) (hG : ∀ g ∈ G, g ∈ x.P.1) :
    logCondOf G x =
      Heights.Different.cond (G.attach.image fun g => evalF x ⟨g.1, hG g.1 g.2⟩) := by
  unfold logCondOf Heights.Different.cond
  rw [dif_pos hG]
  congr 1
  refine finsum_congr fun w => ?_
  have hiff : w ∈ meetsAt x G hG ↔
      w ∈ Heights.Different.meets (G.attach.image fun g => evalF x ⟨g.1, hG g.1 g.2⟩) := by
    constructor
    · rintro ⟨g, hg, hlt⟩
      exact ⟨_, Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩, hlt⟩
    · rintro ⟨a, ha, hlt⟩
      obtain ⟨⟨g, hg⟩, -, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨g, hg, hlt⟩
  by_cases hw : w ∈ meetsAt x G hG
  · rw [if_pos hw, if_pos (hiff.mp hw)]
    rfl
  · rw [if_neg hw, if_neg (fun h => hw (hiff.mpr h))]

end Heights.Curve
