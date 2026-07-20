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

open scoped NumberField nonZeroDivisors NNReal
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

/-- A reduced numerator/denominator representation gives an explicit formula
for the finite-place absolute value in terms of the prime ideal norm. -/
lemma ReducedPrincipalIdealData.adicAbv_eq_absNorm_zpow_sub_multiplicity
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) (hx : x ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.HeightOneSpectrum.adicAbv K v x =
      ((Ideal.absNorm v.asIdeal : ℝ) : ℝ) ^
        ((multiplicity v.asIdeal r.denominator : ℤ) -
          (multiplicity v.asIdeal r.numerator : ℤ)) := by
  let z : ℤ := (multiplicity v.asIdeal r.denominator : ℤ) -
    (multiplicity v.asIdeal r.numerator : ℤ)
  have hval : v.valuation K x = WithZero.exp z :=
    r.valuation_eq_exp_sub_multiplicity hx v
  rw [NumberField.HeightOneSpectrum.adicAbv_def, hval]
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have hu : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp z ≠ 0) =
      Multiplicative.ofAdd z := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero]
    rfl
  rw [hu, toAdd_ofAdd]
  simp [z]

/-- At each finite place, the positive logarithm of a nonzero element is exactly
its reduced denominator multiplicity times the logarithm of the prime norm. -/
lemma ReducedPrincipalIdealData.finitePlace_posLog_eq
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) (hx : x ≠ 0)
    (w : FinitePlace K) :
    Real.posLog (w x) =
      (multiplicity w.maximalIdeal.asIdeal r.denominator : ℝ) *
        Real.log (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) := by
  let v := w.maximalIdeal
  have habv : w x = ((Ideal.absNorm v.asIdeal : ℝ) : ℝ) ^
      ((multiplicity v.asIdeal r.denominator : ℤ) -
        (multiplicity v.asIdeal r.numerator : ℤ)) := by
    rw [← w.norm_embedding_eq x, FinitePlace.norm_embedding]
    exact r.adicAbv_eq_absNorm_zpow_sub_multiplicity hx v
  have hbase : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  by_cases hD : multiplicity v.asIdeal r.denominator = 0
  · rw [habv, hD, Nat.cast_zero, zero_sub]
    simp only [Nat.cast_zero, zero_mul]
    rw [Real.posLog_eq_zero_iff]
    rw [abs_of_pos (zpow_pos (lt_trans (by norm_num) hbase) _)]
    exact (zpow_le_one_iff_right₀ hbase).mpr
      (neg_nonpos.mpr (Int.natCast_nonneg _))
  have hA := r.numerator_ne_bot hx
  have htop : multiplicity v.asIdeal (⊤ : Ideal (𝓞 K)) = 0 :=
    multiplicity_eq_zero.mpr (by
      simpa only [← Ideal.one_eq_top] using v.prime.not_dvd_one)
  have hsup := v.multiplicity_sup hA r.denominator_ne_bot
  rw [(Ideal.isCoprime_iff_sup_eq).mp r.coprime, htop] at hsup
  have hA0 : multiplicity v.asIdeal r.numerator = 0 := by
    rcases min_eq_bot.mp hsup.symm with hA0 | hD0
    · exact hA0
    · exact (hD hD0).elim
  rw [habv, hA0, Nat.cast_zero, sub_zero]
  have hposbase : (0 : ℝ) < Ideal.absNorm v.asIdeal :=
    lt_trans (by norm_num) hbase
  rw [zpow_natCast, Real.posLog_pow,
    Real.posLog_eq_log (by rw [abs_of_pos hposbase]; exact hbase.le)]

/-- The logarithm of a nonzero ideal norm is the finite sum of its prime
multiplicities weighted by logarithms of prime norms. -/
theorem logIdealNorm_eq_finsum_multiplicity
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    logIdealNorm I =
      ∑ᶠ w : FinitePlace K,
        (multiplicity w.maximalIdeal.asIdeal I : ℝ) *
          Real.log (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) := by
  rw [logIdealNorm]
  let F : Ideal (𝓞 K) := ∏ᶠ (w : FinitePlace K),
    w.maximalIdeal.asIdeal ^ multiplicity w.maximalIdeal.asIdeal I
  have hF : F = I := FinitePlace.finprod_finitePlace_pow_multiplicity hI
  have hmap :
      ((Ideal.absNorm F : ℕ) : ℝ) =
        ∏ᶠ w : FinitePlace K,
          (Ideal.absNorm (w.maximalIdeal.asIdeal ^
            multiplicity w.maximalIdeal.asIdeal I) : ℝ) := by
    change ((Nat.castRingHom ℝ).toMonoidHom.comp
      Ideal.absNorm.toMonoidHom) F = _
    rw [show F = ∏ᶠ (w : FinitePlace K),
      w.maximalIdeal.asIdeal ^ multiplicity w.maximalIdeal.asIdeal I from rfl]
    exact ((Nat.castRingHom ℝ).toMonoidHom.comp
        Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
          (fun (J : Ideal (𝓞 K)) hJ => by
            change (Ideal.absNorm J : ℝ) = 1 at hJ
            have hJ' : Ideal.absNorm J = 1 := by exact_mod_cast hJ
            simpa only [Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp hJ')
          (fun w : FinitePlace K =>
            w.maximalIdeal.asIdeal ^ multiplicity w.maximalIdeal.asIdeal I)
  calc
    Real.log (Ideal.absNorm I : ℝ) = Real.log (Ideal.absNorm F : ℝ) := by rw [hF]
    _ = Real.log (∏ᶠ w : FinitePlace K,
          (Ideal.absNorm (w.maximalIdeal.asIdeal ^
            multiplicity w.maximalIdeal.asIdeal I) : ℝ)) := by rw [hmap]
    _ = ∑ᶠ w : FinitePlace K,
          Real.log (Ideal.absNorm (w.maximalIdeal.asIdeal ^
            multiplicity w.maximalIdeal.asIdeal I) : ℝ) := by
      rw [Real.log_finprod]
      intro w
      have hw : (1 : ℝ) < Ideal.absNorm w.maximalIdeal.asIdeal := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal
      rw [map_pow, Nat.cast_pow]
      exact pow_pos (lt_trans (by norm_num) hw) _
    _ = ∑ᶠ w : FinitePlace K,
        (multiplicity w.maximalIdeal.asIdeal I : ℝ) *
          Real.log (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) := by
      apply finsum_congr
      intro w
      rw [map_pow, Nat.cast_pow, Real.log_pow]

/-- The full finite-place contribution to the relative logarithmic height is
the logarithmic norm of the reduced denominator ideal. -/
theorem ReducedPrincipalIdealData.finsum_finitePlace_posLog_eq
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) (hx : x ≠ 0) :
    ∑ᶠ w : FinitePlace K, Real.posLog (w x) = logIdealNorm r.denominator := by
  calc
    ∑ᶠ w : FinitePlace K, Real.posLog (w x) =
        ∑ᶠ w : FinitePlace K,
          (multiplicity w.maximalIdeal.asIdeal r.denominator : ℝ) *
            Real.log (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) := by
      apply finsum_congr
      exact r.finitePlace_posLog_eq hx
    _ = logIdealNorm r.denominator :=
      (logIdealNorm_eq_finsum_multiplicity
        r.denominator r.denominator_ne_bot).symm

/-- The relative logarithmic Weil height is the denominator norm plus the
weighted infinite-place contribution. This is equation (10) in the project's
normalization, including the zero branch of the reduced representation. -/
theorem ReducedPrincipalIdealData.logHeight_eq_logIdealNorm_add_infinitePlace
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) :
    Height.logHeight₁ x = logIdealNorm r.denominator +
      ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v x) := by
  by_cases hx : x = 0
  · subst x
    have hD := (r.zero_normalization rfl).2
    rw [hD]
    simp
  rw [NumberField.logHeight₁_eq, r.finsum_finitePlace_posLog_eq hx]
  ring

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

/-- A certified local minimal model has good reduction when its discriminant
is a unit. This is the valuation characterization used by mathlib's
`WeierstrassCurve.HasGoodReduction`. -/
def IsLocalMinimalDiscriminantExponent.IsGoodReduction
    {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} {W : WeierstrassCurve K} {n : ℕ}
    (h : IsLocalMinimalDiscriminantExponent K v W n) : Prop :=
  v.valuation K (h.change • W).Δ = 1

/-- A certified local minimal model has multiplicative reduction when its
 discriminant is a nonunit and its `c₄` invariant is a unit. This is the
 valuation characterization used by mathlib's
 `WeierstrassCurve.HasMultiplicativeReduction`. -/
def IsLocalMinimalDiscriminantExponent.IsMultiplicativeReduction
    {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} {W : WeierstrassCurve K} {n : ℕ}
    (h : IsLocalMinimalDiscriminantExponent K v W n) : Prop :=
  v.valuation K (h.change • W).Δ < 1 ∧
    v.valuation K (h.change • W).c₄ = 1

/-- A certified global minimal discriminant is semistable when every supplied
local minimal model has good or multiplicative reduction. -/
def IsSemistable
    (K : Type*) [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K),
    (m.realizes v).IsGoodReduction ∨
      (m.realizes v).IsMultiplicativeReduction

/-- At every finite place of a semistable certified curve, the reduced
`j`-denominator multiplicity equals the minimal-discriminant multiplicity. -/
lemma denominator_multiplicity_eq_minimal_of_semistable
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hs : IsSemistable K W m)
    (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal r.denominator = multiplicity v.asIdeal m.ideal := by
  let h := m.realizes v
  let n := multiplicity v.asIdeal m.ideal
  have hle := denominator_multiplicity_le_minimal m r v
  rcases hs v with hgood | hmult
  · have hexp : WithZero.exp (-(n : ℤ)) = 1 := h.exponent.symm.trans hgood
    have hn : -(n : ℤ) = 0 := WithZero.exp_eq_one.mp hexp
    omega
  · have hval : v.valuation K W.j = WithZero.exp (n : ℤ) := by
      rw [← W.variableChange_j h.change]
      let E := h.change • W
      let ν := v.valuation K
      rw [WeierstrassCurve.j, map_mul, map_pow, Units.val_inv_eq_inv_val,
        map_inv₀, WeierstrassCurve.coe_Δ']
      change (ν E.Δ)⁻¹ * ν E.c₄ ^ 3 = WithZero.exp (n : ℤ)
      rw [h.exponent, hmult.2, one_pow, mul_one, ← WithZero.exp_neg]
      simp [n]
    have hj0 : W.j ≠ 0 := (Valuation.ne_zero_iff _).mp (by
      rw [hval]
      exact WithZero.exp_ne_zero)
    have hexp : WithZero.exp
        ((multiplicity v.asIdeal r.denominator : ℤ) -
          (multiplicity v.asIdeal r.numerator : ℤ)) =
        WithZero.exp (n : ℤ) := by
      rw [← r.valuation_eq_exp_sub_multiplicity hj0 v, hval]
    have hz := WithZero.exp_injective hexp
    omega

/-- For a semistable certified curve, the reduced denominator of `j` is the
entire minimal-discriminant ideal. -/
theorem denominator_eq_minimalDiscriminant_of_semistable
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hs : IsSemistable K W m) :
    r.denominator = m.ideal := by
  apply dvd_antisymm (denominator_dvd_minimalDiscriminant m r)
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le m.ideal_ne_bot).mpr
  intro p hp
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  have heq := denominator_multiplicity_eq_minimal_of_semistable m r hs v
  have hm : FiniteMultiplicity p m.ideal :=
    FiniteMultiplicity.of_prime_left hp m.ideal_ne_bot
  have hD : FiniteMultiplicity p r.denominator :=
    FiniteMultiplicity.of_prime_left hp r.denominator_ne_bot
  rw [hm.emultiplicity_eq_multiplicity, hD.emultiplicity_eq_multiplicity]
  exact_mod_cast heq.symm.le

/-- Semistability kills the complementary unstable minimal-discriminant
ideal. -/
theorem unstableMinimalDiscriminant_eq_top_of_semistable
    {K : Type*} [Field K] [NumberField K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (hs : IsSemistable K W m) :
    unstableMinimalDiscriminant m r = ⊤ := by
  symm
  apply unstableMinimalDiscriminant_unique m r ⊤
  rw [← Ideal.one_eq_top, mul_one,
    denominator_eq_minimalDiscriminant_of_semistable m r hs]

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
  all_goals
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
  all_goals
    have hd := (numberFieldDegree_pos K).ne'
    field_simp
    ring

/-- After removing the reduced denominator contribution, normalized Weil height
is exactly the normalized weighted infinite-place sum. -/
theorem normalizedHeight_sub_denominator_eq_infinitePlace
    {K : Type*} [Field K] [NumberField K]
    {x : K} (r : ReducedPrincipalIdealData K x) :
    normalizedLogHeight K x -
        logIdealNorm r.denominator / (Module.finrank ℚ K : ℝ) =
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v x)) /
        (Module.finrank ℚ K : ℝ) := by
  rw [normalizedLogHeight,
    r.logHeight_eq_logIdealNorm_add_infinitePlace]
  have hd := (numberFieldDegree_pos K).ne'
  field_simp
  ring

/-- Using compatible periods, the entire Proposition 2.1 comparison expression
is a normalized weighted average of an explicit function of the actual modular
`j`, modular discriminant, and imaginary part. Thus all remaining inequalities
are purely archimedean fundamental-domain estimates. -/
theorem comparisonExpression_eq_archimedeanAverage
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (r : ReducedPrincipalIdealData K W.j)
    (p : ArchimedeanPeriodData K W) :
    normalizedLogHeight K W.j +
          logIdealNorm (unstableMinimalDiscriminant m r) /
            (Module.finrank ℚ K : ℝ) -
        12 * silvermanHeight W m p =
      (∑ v : InfinitePlace K, (v.mult : ℝ) *
        (Real.posLog ‖modularJ (p.τ v)‖ +
          Real.log (‖silvermanModularDiscriminant (p.τ v)‖ *
            (p.τ v).im ^ 6))) /
        (Module.finrank ℚ K : ℝ) := by
  rw [comparisonExpression_eq,
    normalizedHeight_sub_denominator_eq_infinitePlace r]
  have hd := (numberFieldDegree_pos K).ne'
  field_simp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [← InfinitePlace.norm_embedding_eq v W.j, p.j_eq]
  ring

end Heights
