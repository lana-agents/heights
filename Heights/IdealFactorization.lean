import Heights.SilvermanHeight

set_option linter.style.header false

/-!
# Complementary unstable discriminant ideal

Given a proof that the reduced denominator ideal of `j` divides a certified
minimal-discriminant ideal, this file constructs the complementary ideal and
proves its elementary factorization and norm identities. Crucially, denominator
divisibility itself is not assumed in a certificate field and is not proved
here; it remains a finite-place arithmetic target.
-/

open scoped NumberField
open NumberField

namespace Heights

/-- The complementary (unstable) ideal obtained after removing the reduced
`j`-denominator from the minimal-discriminant ideal. -/
noncomputable def unstableMinimalDiscriminant
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hDvd : r.denominator ∣ m.ideal) : Ideal (𝓞 K) :=
  Classical.choose hDvd

/-- The denominator times its chosen complement is the certified
minimal-discriminant ideal. -/
theorem denominator_mul_unstableMinimalDiscriminant
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hDvd : r.denominator ∣ m.ideal) :
    r.denominator * unstableMinimalDiscriminant m r hDvd = m.ideal :=
  (Classical.choose_spec hDvd).symm

/-- The complementary unstable ideal is nonzero. -/
theorem unstableMinimalDiscriminant_ne_bot
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hDvd : r.denominator ∣ m.ideal) :
    unstableMinimalDiscriminant m r hDvd ≠ ⊥ := by
  intro h
  have hm := denominator_mul_unstableMinimalDiscriminant m r hDvd
  rw [h, Ideal.mul_bot] at hm
  exact m.ideal_ne_bot hm.symm

/-- The complement is uniquely determined because the denominator is
nonzero. -/
theorem unstableMinimalDiscriminant_unique
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hDvd : r.denominator ∣ m.ideal)
    (γ : Ideal (𝓞 K)) (hγ : r.denominator * γ = m.ideal) :
    γ = unstableMinimalDiscriminant m r hDvd := by
  apply mul_left_cancel₀ r.denominator_ne_bot
  rw [hγ, denominator_mul_unstableMinimalDiscriminant]

/-- Logarithmic ideal norm turns products of nonzero ideals into sums. -/
theorem logIdealNorm_mul
    {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    logIdealNorm (I * J) = logIdealNorm I + logIdealNorm J := by
  rw [logIdealNorm, logIdealNorm, logIdealNorm, map_mul Ideal.absNorm,
    Nat.cast_mul, Real.log_mul]
  · exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  · exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ

/-- The finite minimal-discriminant term splits into the reduced denominator
term and the unstable term. -/
theorem logIdealNorm_minimal_eq_denominator_add_unstable
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hDvd : r.denominator ∣ m.ideal) :
    logIdealNorm m.ideal = logIdealNorm r.denominator +
      logIdealNorm (unstableMinimalDiscriminant m r hDvd) := by
  rw [← denominator_mul_unstableMinimalDiscriminant m r hDvd,
    logIdealNorm_mul _ _ r.denominator_ne_bot
      (unstableMinimalDiscriminant_ne_bot m r hDvd)]

end Heights
