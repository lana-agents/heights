/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Different.Kummer
import Heights.Curve.Conductor

/-!
# Kummer–Fermat extensions of fields of definition

The discriminant bound (W7b, `Heights.Different.logDisc_le_logDisc_add_cond_add_of_adjoin`) in
the form used for points of Kummer–Fermat coverings `y^N = φ`, `z^N = 1 − φ` of curves, where the
number fields are subfields of `ℚ̄`:

* `Heights.Curve.logDisc_le_of_eq_adjoin`: if `F ≤ L ≤ ℚ̄` are number fields and `L = F(a, b)`
  with `a^N = c`, `b^N = 1 − c` for `c ∈ F`, then
  `logDisc L ≤ logDisc F + cond G + kummerConst N` for every finite `G ⊆ F` such that `c`,
  `1 − c` are units at the places not meeting `G`;
* `Heights.Curve.apply_eq_one_of_notMem_meets`: `G = {c, c⁻¹, (1 − c)⁻¹}` has this property.
-/

namespace Heights.Curve

open NumberField Heights.Different Heights.Absolute

/-- The places not meeting `{c, c⁻¹, (1 − c)⁻¹}` are those where `c` and `1 − c` are units. -/
theorem apply_eq_one_of_notMem_meets {F : Type*} [Field F] [NumberField F] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (G : Finset F) (hG : c ∈ G ∧ c⁻¹ ∈ G ∧ (1 - c)⁻¹ ∈ G) (w : FinitePlace F)
    (hw : w ∉ meets G) : w c = 1 ∧ w (1 - c) = 1 := by
  have h : ¬ (1 < w c ∨ 1 < w c⁻¹ ∨ 1 < w (1 - c)⁻¹) := by
    rintro (h | h | h)
    · exact hw ⟨c, hG.1, h⟩
    · exact hw ⟨c⁻¹, hG.2.1, h⟩
    · exact hw ⟨(1 - c)⁻¹, hG.2.2, h⟩
  rw [exists_one_lt_iff_tripod w hc0 hc1] at h
  push Not at h
  refine ⟨h.1, ?_⟩
  rw [← neg_sub, map_neg_eq_map]
  exact h.2

/-- **(W7b) for subfields of `ℚ̄`**: if `F ≤ L` and `L = F(a, b)` with `a^N = c`,
`b^N = 1 − c` (`c ∈ F`), then `logDisc L ≤ logDisc F + cond G + kummerConst N` whenever `c` and
`1 − c` are units at the finite places of `F` not meeting `G`. -/
theorem logDisc_le_of_eq_adjoin {F L : IntermediateField ℚ Qbar} [FiniteDimensional ℚ F]
    [FiniteDimensional ℚ L] (hFL : F ≤ L) {N : ℕ} (hN : 0 < N) {c : F} {a b : Qbar}
    (ha : a ^ N = c) (hb : b ^ N = 1 - c)
    (hL : L = (IntermediateField.adjoin F {a, b}).restrictScalars ℚ) (G : Finset F)
    (hG : ∀ u : FinitePlace F, u ∉ meets G → u c = 1 ∧ u (1 - c) = 1) :
    logDisc L ≤ logDisc F + cond G + kummerConst N := by
  letI : Algebra F L := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  have haL : a ∈ L := by
    rw [hL, IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hbL : b ∈ L := by
    rw [hL, IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  -- the inclusion `L → ℚ̄` as an `F`-algebra map
  let ι : L →ₐ[F] Qbar :=
    { L.val.toRingHom with commutes' := fun _ => rfl }
  have hι : ∀ z : L, ι z = z := fun _ => rfl
  refine logDisc_le_logDisc_add_cond_add_of_adjoin hN (a := ⟨a, haL⟩) (b := ⟨b, hbL⟩)
    (Subtype.ext ha) (Subtype.ext hb) ?_ G hG
  rw [eq_top_iff]
  rintro z -
  have hz : (z : Qbar) ∈ IntermediateField.adjoin F {a, b} := by
    have h1 : (z : Qbar) ∈ L := z.2
    have h2 : ∀ w : Qbar, w ∈ L → w ∈ IntermediateField.adjoin F {a, b} := by
      intro w hw
      rw [hL, IntermediateField.mem_restrictScalars] at hw
      exact hw
    exact h2 _ h1
  have hmap : (IntermediateField.adjoin F {(⟨a, haL⟩ : L), ⟨b, hbL⟩}).map ι =
      IntermediateField.adjoin F {a, b} := by
    rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton, hι, hι]
  rw [← hmap] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  have : w = z := Subtype.ext hwz
  rwa [← this]

end Heights.Curve
