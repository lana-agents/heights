import Heights.Certificates
import Heights.WeilHeight

set_option linter.style.header false

/-!
# Silverman's formula-defined elliptic-curve height

This file defines the finite-plus-archimedean expression in Silverman's
Proposition 1.1 from explicit realization certificates. It does not construct
an Arakelov/Faltings height and does not yet prove that the expression agrees
with one. In particular, this is not an arbitrary real supplied by a
certificate.
-/

open scoped NumberField UpperHalfPlane
open NumberField

namespace Heights

/-- The logarithm of the absolute norm of an integral ideal.

Height formulae should use this only together with a proof that the ideal is
not `⊥`; `absNorm_pos_of_ne_bot` records the resulting strict positivity. -/
noncomputable def logIdealNorm
    {K : Type*} [Field K] [NumberField K] (I : Ideal (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm I)

/-- A nonzero integral ideal has strictly positive absolute norm, so its norm
is a legitimate logarithm argument. -/
theorem absNorm_pos_of_ne_bot
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- The logarithmic norm of the unit ideal vanishes. -/
@[simp] theorem logIdealNorm_top
    {K : Type*} [Field K] [NumberField K] :
    logIdealNorm (⊤ : Ideal (𝓞 K)) = 0 := by
  simp [logIdealNorm]

/-- The logarithmic norm of a nonzero integral ideal is nonnegative. -/
theorem logIdealNorm_nonneg
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 ≤ logIdealNorm I := by
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- Silverman's finite-plus-archimedean elliptic-curve height expression.

The finite term is the norm of the certified minimal-discriminant ideal. The
archimedean term uses actual period ratios and the actual modular discriminant,
including `(2π) ^ 12`, and the whole expression is divided by `12 [K : ℚ]`.
This definition is certificate-level: existence of `m` and `p` for every curve
is not claimed. -/
noncomputable def silvermanHeight
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (p : ArchimedeanPeriodData K W) : ℝ :=
  (logIdealNorm m.ideal -
      ∑ v : InfinitePlace K,
        (v.mult : ℝ) * Real.log
          (‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6)) /
    (12 * (Module.finrank ℚ K : ℝ))

/-- Every archimedean logarithm argument in `silvermanHeight` is strictly
positive. -/
theorem silvermanHeight_archimedean_log_arg_pos
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    0 < ‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6 := by
  exact mul_pos (silvermanModularDiscriminant_norm_pos _)
    (pow_pos (p.τ v).im_pos _)

/-- The denominator in `silvermanHeight` is strictly positive. -/
theorem silvermanHeight_denominator_pos
    (K : Type*) [Field K] [NumberField K] :
    (0 : ℝ) < 12 * Module.finrank ℚ K := by
  exact mul_pos (by norm_num) (numberFieldDegree_pos K)

end Heights
