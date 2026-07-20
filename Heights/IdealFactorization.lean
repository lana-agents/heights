import Heights.SilvermanHeight

set_option linter.style.header false

/-!
# Complementary unstable discriminant ideal

This file proves that the reduced denominator ideal of `j` divides a certified
minimal-discriminant ideal, using the local integrality and minimality data from
the certificate. It then constructs the complementary ideal and proves its
elementary factorization and norm identities. Denominator divisibility is a
theorem here, not a certificate field.
-/

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

namespace Heights

/-- The fractional-ideal multiplicity of a nonzero integral ideal is its usual
natural-number prime multiplicity, cast to `ℤ`. -/
lemma fractionalIdealCount_coe_eq_multiplicity
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) =
      (multiplicity v.asIdeal I : ℤ) := by
  rw [FractionalIdeal.count_coe K v hI]
  norm_cast
  rw [Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    v.count_normalizedFactors_eq_multiplicity hI]

/-- Fractional-ideal multiplicity of a nonzero principal ideal is the negative
of the logarithm of the corresponding multiplicative prime valuation. -/
lemma fractionalIdealCount_spanSingleton
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      -(WithZero.log (v.valuation K x) : ℤ) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ x
  have hn : n ≠ 0 := by
    intro hn
    apply hx
    rw [← hnd, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hd : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hsn : (Ideal.span {n} : Ideal (𝓞 K)) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp hn
  have hsd : (Ideal.span {(d : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp hd
  have hval : v.valuation K x = v.intValuation n / v.intValuation (d : 𝓞 K) := by
    rw [← hnd, v.valuation_of_mk']
  have hcount :
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
        (multiplicity v.asIdeal (Ideal.span {n}) : ℤ) -
          (multiplicity v.asIdeal (Ideal.span {(d : 𝓞 K)}) : ℤ) := by
    rw [← hnd, IsFractionRing.mk'_eq_div,
      ← FractionalIdeal.spanSingleton_div_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_span_singleton,
      div_eq_mul_inv,
      FractionalIdeal.count_mul K v
        (FractionalIdeal.coeIdeal_ne_zero.mpr hsn)
        (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hsd)),
      FractionalIdeal.count_inv,
      fractionalIdealCount_coe_eq_multiplicity v hsn,
      fractionalIdealCount_coe_eq_multiplicity v hsd]
    ring
  rw [hcount, hval,
    v.intValuation_eq_exp_neg_multiplicity hn,
    v.intValuation_eq_exp_neg_multiplicity hd,
    WithZero.log_div WithZero.exp_ne_zero WithZero.exp_ne_zero,
    WithZero.log_exp, WithZero.log_exp]
  omega

/-- The fractional-ideal multiplicity of a reduced representation is numerator
multiplicity minus denominator multiplicity. -/
lemma ReducedPrincipalIdealData.count_spanSingleton
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) (hx : x ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      (multiplicity v.asIdeal r.numerator : ℤ) -
        (multiplicity v.asIdeal r.denominator : ℤ) := by
  have hA := r.numerator_ne_bot hx
  rw [r.span_eq, div_eq_mul_inv,
    FractionalIdeal.count_mul K v
      (FractionalIdeal.coeIdeal_ne_zero.mpr hA)
      (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr r.denominator_ne_bot)),
    FractionalIdeal.count_inv,
    fractionalIdealCount_coe_eq_multiplicity v hA,
    fractionalIdealCount_coe_eq_multiplicity v r.denominator_ne_bot]
  ring

/-- At a prime, a reduced numerator/denominator representation computes the
valuation as `exp (ord_v D - ord_v A)`. -/
lemma ReducedPrincipalIdealData.valuation_eq_exp_sub_multiplicity
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) (hx : x ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K x = WithZero.exp
      ((multiplicity v.asIdeal r.denominator : ℤ) -
        (multiplicity v.asIdeal r.numerator : ℤ)) := by
  have hspan := fractionalIdealCount_spanSingleton v x hx
  rw [r.count_spanSingleton hx v] at hspan
  have hlog : WithZero.log (v.valuation K x) =
      (multiplicity v.asIdeal r.denominator : ℤ) -
        (multiplicity v.asIdeal r.numerator : ℤ) := by
    omega
  rw [← hlog, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)]

/-- Prime by prime, the reduced denominator multiplicity of `j` is at most the
certified minimal-discriminant multiplicity. The zero-`j` normalization is
handled separately; otherwise coprimality removes the numerator multiplicity
at every denominator prime. -/
lemma denominator_multiplicity_le_minimal
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal r.denominator ≤ multiplicity v.asIdeal m.ideal := by
  by_cases hj0 : W.j = 0
  · have hD := (r.zero_normalization hj0).2
    rw [hD]
    have htop : multiplicity v.asIdeal (⊤ : Ideal (𝓞 K)) = 0 :=
      multiplicity_eq_zero.mpr (by
        simpa only [← Ideal.one_eq_top] using v.prime.not_dvd_one)
    rw [htop]
    exact Nat.zero_le _
  have hA := r.numerator_ne_bot hj0
  by_cases hD0 : multiplicity v.asIdeal r.denominator = 0
  · omega
  have htop : multiplicity v.asIdeal (⊤ : Ideal (𝓞 K)) = 0 :=
    multiplicity_eq_zero.mpr (by
      simpa only [← Ideal.one_eq_top] using v.prime.not_dvd_one)
  have hsup := v.multiplicity_sup hA r.denominator_ne_bot
  rw [(Ideal.isCoprime_iff_sup_eq).mp r.coprime, htop] at hsup
  have hA0 : multiplicity v.asIdeal r.numerator = 0 := by
    rcases min_eq_bot.mp hsup.symm with hA0 | hD0'
    · exact hA0
    · exact (hD0 hD0').elim
  have hj := (m.realizes v).valuation_j_le_exp
  rw [r.valuation_eq_exp_sub_multiplicity hj0 v, hA0, Nat.cast_zero, sub_zero,
    WithZero.exp_le_exp] at hj
  exact_mod_cast hj

/-- The reduced denominator ideal of `j` divides the certified global minimal
discriminant ideal. This is the finite-place arithmetic input needed to define
the complementary unstable ideal canonically from the certificates. -/
theorem denominator_dvd_minimalDiscriminant
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j) :
    r.denominator ∣ m.ideal := by
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le
    r.denominator_ne_bot).mpr
  intro p hp
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  have h := denominator_multiplicity_le_minimal m r v
  have hD : FiniteMultiplicity p r.denominator :=
    FiniteMultiplicity.of_prime_left hp r.denominator_ne_bot
  have hm : FiniteMultiplicity p m.ideal :=
    FiniteMultiplicity.of_prime_left hp m.ideal_ne_bot
  rw [hD.emultiplicity_eq_multiplicity, hm.emultiplicity_eq_multiplicity]
  exact_mod_cast h

/-- The canonical complementary (unstable) ideal obtained by removing the
reduced `j`-denominator from the minimal-discriminant ideal. Its construction
uses the proved denominator-divisibility theorem, not extra certificate data. -/
noncomputable def unstableMinimalDiscriminant
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j) : Ideal (𝓞 K) :=
  Classical.choose (denominator_dvd_minimalDiscriminant m r)

/-- The denominator times its canonical complement is the certified
minimal-discriminant ideal. -/
theorem denominator_mul_unstableMinimalDiscriminant
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j) :
    r.denominator * unstableMinimalDiscriminant m r = m.ideal :=
  (Classical.choose_spec (denominator_dvd_minimalDiscriminant m r)).symm

/-- The canonical complementary unstable ideal is nonzero. -/
theorem unstableMinimalDiscriminant_ne_bot
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j) :
    unstableMinimalDiscriminant m r ≠ ⊥ := by
  intro h
  have hm := denominator_mul_unstableMinimalDiscriminant m r
  rw [h, Ideal.mul_bot] at hm
  exact m.ideal_ne_bot hm.symm

/-- The complement is uniquely determined because the denominator is
nonzero. -/
theorem unstableMinimalDiscriminant_unique
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (γ : Ideal (𝓞 K)) (hγ : r.denominator * γ = m.ideal) :
    γ = unstableMinimalDiscriminant m r := by
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
    (r : ReducedPrincipalIdealData K W.j) :
    logIdealNorm m.ideal = logIdealNorm r.denominator +
      logIdealNorm (unstableMinimalDiscriminant m r) := by
  rw [← denominator_mul_unstableMinimalDiscriminant m r,
    logIdealNorm_mul _ _ r.denominator_ne_bot
      (unstableMinimalDiscriminant_ne_bot m r)]

/-- Expanding the definition of Silverman's height and splitting the minimal
ideal gives the exact finite-plus-archimedean formula with the reduced
`j`-denominator and unstable ideal displayed separately. -/
theorem twelve_mul_silvermanHeight_eq
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (p : ArchimedeanPeriodData K W) :
    12 * silvermanHeight W m p =
      (logIdealNorm r.denominator +
          logIdealNorm (unstableMinimalDiscriminant m r) -
          ∑ v : InfinitePlace K,
            (v.mult : ℝ) * Real.log
              (‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6)) /
        (Module.finrank ℚ K : ℝ) := by
  rw [silvermanHeight, logIdealNorm_minimal_eq_denominator_add_unstable]
  have hd := (numberFieldDegree_pos K).ne'
  field_simp

/-- The comparison expression from Proposition 2.1 is exactly the normalized
height minus the denominator contribution plus the archimedean metric sum.
This is an identity, not an analytic estimate. -/
theorem comparisonExpression_eq
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (p : ArchimedeanPeriodData K W) :
    normalizedLogHeight K W.j +
          logIdealNorm (unstableMinimalDiscriminant m r) /
            (Module.finrank ℚ K : ℝ) -
        12 * silvermanHeight W m p =
      normalizedLogHeight K W.j -
          logIdealNorm r.denominator / (Module.finrank ℚ K : ℝ) +
          (∑ v : InfinitePlace K,
            (v.mult : ℝ) * Real.log
              (‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6)) /
            (Module.finrank ℚ K : ℝ) := by
  rw [silvermanHeight, logIdealNorm_minimal_eq_denominator_add_unstable]
  have hd := (numberFieldDegree_pos K).ne'
  field_simp
  ring

end Heights
