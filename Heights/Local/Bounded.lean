/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Local.PlaceEmbedding

/-!
# Bounds at places from bounds at embeddings

A point of `U_ℙ(ℚ̄)` of degree `d` determines `d` points of `U_ℙ(ℚ̄_v)` for every place `v` of
`ℚ` (its images under the embeddings of its field of definition); compactly bounded subsets
are defined by conditions on these ([GenEll], Example 1.3 (ii)). This file translates such
conditions into conditions on the absolute values of the number field at its places above
`v`, in the normalisation of Mathlib's `NumberField.FinitePlace` / `InfinitePlace`:

* `Heights.Local.abs_log_finitePlace_le`: if `|log ‖τ λ‖| ≤ c` for all `τ : F → ℚ̄_p`, then
  `|log w λ| ≤ [F : ℚ] c` for every finite place `w` of `F` over `p`;
* `Heights.Local.abs_log_infinitePlace_le`: if `|log |σ λ|| ≤ c` for all `σ : F → ℂ`, then
  `|log w λ| ≤ c` for every infinite place `w`.
-/

namespace Heights.Local

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Bounds at all embeddings into `ℚ̄_p` give bounds at all finite places over `p`. -/
theorem abs_log_finitePlace_le {p : ℕ} [Fact p.Prime] {c : ℝ} (hc : 0 ≤ c) {y : F}
    (hy : ∀ τ : F →+* PadicAlgCl p, |Real.log ‖τ y‖| ≤ c) (w : FinitePlace F)
    (hpw : ((p : ℕ) : 𝓞 F) ∈ w.maximalIdeal.asIdeal) :
    |Real.log (w y)| ≤ Module.finrank ℚ F * c := by
  obtain ⟨τ, N, hN, hNle, hw⟩ := exists_ringHom_padicAlgCl_eq_pow w hpw
  rw [hw y, Real.log_pow, abs_mul, Nat.abs_cast]
  exact mul_le_mul (by exact_mod_cast hNle) (hy τ) (abs_nonneg _) (Nat.cast_nonneg _)

/-- Bounds at all complex embeddings give bounds at all infinite places. -/
theorem abs_log_infinitePlace_le {c : ℝ} {y : F} (hy : ∀ σ : F →+* ℂ, |Real.log ‖σ y‖| ≤ c)
    (w : InfinitePlace F) : |Real.log (w y)| ≤ c := by
  rw [← InfinitePlace.norm_embedding_eq w y]
  exact hy _

end Heights.Local
