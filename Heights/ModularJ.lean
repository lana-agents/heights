import Mathlib

set_option linter.style.header false

/-!
# The modular discriminant and modular j-invariant

This file records the two analytic normalizations used in Silverman's height
formula. Mathlib's modular discriminant is `η ^ 24`, whereas Silverman's
analytic discriminant includes the additional factor `(2π) ^ 12`. The modular
`j`-function uses mathlib's normalized discriminant and has no factor of 1728
in front of `E₄ ^ 3 / Δ`.
-/

open scoped UpperHalfPlane

namespace Heights

/-- Silverman's analytic modular discriminant. The `(2π) ^ 12` factor is
essential for the exact height formula, even though it affects asymptotic
comparisons only by an absolute additive constant. -/
noncomputable def silvermanModularDiscriminant (τ : ℍ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ 12 * ModularForm.discriminant τ

/-- The modular `j`-function in the `q⁻¹ + 744 + ⋯` normalization. -/
noncomputable def modularJ (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- Silverman's modular discriminant does not vanish on the upper half-plane. -/
theorem silvermanModularDiscriminant_ne_zero (τ : ℍ) :
    silvermanModularDiscriminant τ ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact ModularForm.discriminant_ne_zero τ

/-- In particular, the norm used as an argument of `Real.log` in the height
formula is strictly positive. -/
theorem silvermanModularDiscriminant_norm_pos (τ : ℍ) :
    0 < ‖silvermanModularDiscriminant τ‖ :=
  norm_pos_iff.mpr (silvermanModularDiscriminant_ne_zero τ)

/-- Clearing the nonzero discriminant denominator recovers `E₄ ^ 3`. -/
theorem modularJ_mul_discriminant (τ : ℍ) :
    modularJ τ * ModularForm.discriminant τ = ModularForm.E₄ τ ^ 3 := by
  exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)

/-- The only zeros of modular `j` on the upper half-plane are the zeros of
`E₄`; the modular discriminant contributes no zeros. -/
theorem modularJ_eq_zero_iff (τ : ℍ) :
    modularJ τ = 0 ↔ ModularForm.E₄ τ = 0 := by
  rw [modularJ, div_eq_zero_iff]
  simp [ModularForm.discriminant_ne_zero τ]

/-- The `q`-product formula with Silverman's normalization kept explicit. -/
theorem silvermanModularDiscriminant_eq_q_prod (τ : ℍ) :
    silvermanModularDiscriminant τ =
      (2 * (Real.pi : ℂ)) ^ 12 *
        (Function.Periodic.qParam 1 τ *
          ∏' n, (1 - ModularForm.eta_q n τ) ^ 24) := by
  rw [silvermanModularDiscriminant, ModularForm.discriminant_eq_q_prod]

/-- The algebraic identity confirming the normalization of the denominator in
`modularJ`. -/
theorem modularJ_denominator_eq_E₄_E₆ (τ : ℍ) :
    ModularForm.discriminant τ =
      (ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2) / 1728 :=
  ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ

end Heights
