/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.Integrality

/-!
# Heights of tuples only depend on linear equivalence classes

For a tuple `s` write `A_s = −min_i div(s_i)` (so `A_s(P) = −minOrd P s`). The divisor of
the product tuple `s ⊗ t = (s_i t_j)` is `A_s + A_t`, and that of `r • s` is `A_s − div r`.
Combining this with the comparison theorem `tupleHeight_le_of_minOrd_le` and the Segre
identity, we get the basic invariance of heights attached to divisors: if
`A_s − A_{s'} = A_u − A_{u'} + div r` then `h_s − h_{s'} ≈ h_u − h_{u'}`
(`Heights.Curve.abs_tupleHeight_sub_sub_le`). This is [GenEll], Proposition 1.4 (i), (iii):
the BD-class of the height of a divisor depends only on its linear equivalence class, and is
additive.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] {ι κ ι' κ' : Type*}
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- The minimal order of a product tuple is the sum of the minimal orders. -/
theorem minOrd_mul {s : ι → K} {t : κ → K} (hs : ∃ i, s i ≠ 0) (ht : ∃ j, t j ≠ 0)
    (P : Place K) : minOrd P (fun p : ι × κ => s p.1 * t p.2) = minOrd P s + minOrd P t := by
  have hst : ∃ p : ι × κ, s p.1 * t p.2 ≠ 0 :=
    ⟨(normIdx P s hs, normIdx P t ht), mul_ne_zero (normIdx_ne_zero hs) (normIdx_ne_zero ht)⟩
  apply le_antisymm
  · have := minOrd_le (P := P) hst (j := (normIdx P s hs, normIdx P t ht))
      (mul_ne_zero (normIdx_ne_zero hs) (normIdx_ne_zero ht))
    rw [P.ord_mul (normIdx_ne_zero hs) (normIdx_ne_zero ht), ← minOrd_eq hs,
      ← minOrd_eq ht] at this
    exact this
  · rw [minOrd_eq hst]
    set p := normIdx P (fun p : ι × κ => s p.1 * t p.2) hst
    have hp : s p.1 * t p.2 ≠ 0 := normIdx_ne_zero hst
    rw [P.ord_mul (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)]
    exact add_le_add (minOrd_le hs (left_ne_zero_of_mul hp))
      (minOrd_le ht (right_ne_zero_of_mul hp))

/-- Scaling a tuple by `r ≠ 0` shifts its minimal order by `ord_P r`. -/
theorem minOrd_smul {s : ι → K} (hs : ∃ i, s i ≠ 0) {r : K} (hr : r ≠ 0) (P : Place K) :
    minOrd P (fun i => r * s i) = P.ord r + minOrd P s := by
  have hrs : ∃ i, r * s i ≠ 0 := ⟨normIdx P s hs, mul_ne_zero hr (normIdx_ne_zero hs)⟩
  apply le_antisymm
  · have := minOrd_le (P := P) hrs (j := normIdx P s hs) (mul_ne_zero hr (normIdx_ne_zero hs))
    rw [P.ord_mul hr (normIdx_ne_zero hs), ← minOrd_eq hs] at this
    exact this
  · rw [minOrd_eq hrs]
    set i := normIdx P (fun i => r * s i) hrs
    have hi : r * s i ≠ 0 := normIdx_ne_zero hrs
    rw [P.ord_mul hr (right_ne_zero_of_mul hi)]
    exact add_le_add_right (minOrd_le hs (right_ne_zero_of_mul hi)) _

/-- **Tuples with the same divisor have boundedly different heights.** -/
theorem abs_tupleHeight_sub_le_of_minOrd_eq {s : ι → K} {t : κ → K} (hs : ∃ i, s i ≠ 0)
    (ht : ∃ j, t j ≠ 0) (heq : ∀ P : Place K, minOrd P s = minOrd P t) :
    ∃ C, ∀ x : QbarPoint K, |tupleHeight s x - tupleHeight t x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := tupleHeight_le_of_minOrd_le hs ht fun P => (heq P).ge
  obtain ⟨C₂, hC₂⟩ := tupleHeight_le_of_minOrd_le ht hs fun P => (heq P).le
  refine ⟨max C₁ C₂, fun x => abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith [hC₂ x, le_max_right C₁ C₂]
  · linarith [hC₁ x, le_max_left C₁ C₂]

/-- **Invariance under linear equivalence and additivity**: if
`A_s − A_{s'} = A_u − A_{u'} + div r`, i.e. `minOrd s + minOrd u' = minOrd u + minOrd s' + ord r`
at every place, then `h_s − h_{s'} ≈ h_u − h_{u'}`. -/
theorem abs_tupleHeight_sub_sub_le {s : ι → K} {s' : κ → K} {u : ι' → K} {u' : κ' → K}
    (hs : ∃ i, s i ≠ 0) (hs' : ∃ i, s' i ≠ 0) (hu : ∃ i, u i ≠ 0) (hu' : ∃ i, u' i ≠ 0)
    {r : K} (hr : r ≠ 0)
    (heq : ∀ P : Place K, minOrd P s + minOrd P u' = P.ord r + (minOrd P u + minOrd P s')) :
    ∃ C, ∀ x : QbarPoint K,
      |(tupleHeight s x - tupleHeight s' x) - (tupleHeight u x - tupleHeight u' x)| ≤ C := by
  set S : ι × κ' → K := fun p => s p.1 * u' p.2
  set T₀ : ι' × κ → K := fun p => u p.1 * s' p.2
  set T : ι' × κ → K := fun p => r * T₀ p
  have hS : ∃ p, S p ≠ 0 := ⟨(normIdx (Classical.arbitrary (Place K)) s hs,
    normIdx (Classical.arbitrary (Place K)) u' hu'),
    mul_ne_zero (normIdx_ne_zero hs) (normIdx_ne_zero hu')⟩
  have hT₀ : ∃ p, T₀ p ≠ 0 := ⟨(normIdx (Classical.arbitrary (Place K)) u hu,
    normIdx (Classical.arbitrary (Place K)) s' hs'),
    mul_ne_zero (normIdx_ne_zero hu) (normIdx_ne_zero hs')⟩
  have hT : ∃ p, T p ≠ 0 := by
    obtain ⟨p, hp⟩ := hT₀
    exact ⟨p, mul_ne_zero hr hp⟩
  obtain ⟨C, hC⟩ := abs_tupleHeight_sub_le_of_minOrd_eq hS hT fun P => by
    change minOrd P (fun p : ι × κ' => s p.1 * u' p.2) =
      minOrd P (fun p => r * (fun p : ι' × κ => u p.1 * s' p.2) p)
    rw [minOrd_mul hs hu', minOrd_smul hT₀ hr, minOrd_mul hu hs', heq P]
  refine ⟨C, fun x => ?_⟩
  have h1 : tupleHeight S x = tupleHeight s x + tupleHeight u' x := tupleHeight_mul hs hu' x
  have h2 : tupleHeight T x = tupleHeight u x + tupleHeight s' x := by
    change tupleHeight (fun p => r * T₀ p) x = _
    rw [tupleHeight_smul x hr]
    exact tupleHeight_mul hu hs' x
  have := hC x
  rw [h1, h2] at this
  calc |(tupleHeight s x - tupleHeight s' x) - (tupleHeight u x - tupleHeight u' x)|
      = |(tupleHeight s x + tupleHeight u' x) - (tupleHeight u x + tupleHeight s' x)| := by
        congr 1
        ring
    _ ≤ C := this

end Heights.Curve
