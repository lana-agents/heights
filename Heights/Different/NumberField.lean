/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The different of an extension of number fields: tower formula and local decomposition

For number fields `F ⊆ L` with relative different `𝔇 = 𝔇_{𝓞 L/𝓞 F}`:

* `Heights.Different.logDisc K = log |d_K| / [K : ℚ]` (the log-different of `K`);
* `Heights.Different.logDisc_eq_add`, the **tower formula**
  `logDisc L = logDisc F + log N(𝔇)/[L : ℚ]`, from Mathlib's
  `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`;
* `Heights.Different.log_absNorm_eq_finsum`, the **local decomposition**
  `log N(I) = ∑ᶠ P, ord_P(I)·log N(P)` of a nonzero ideal;
* `Heights.Different.diffContrib L 𝔭 = ∑_{P ∣ 𝔭} ord_P(𝔇)·log N(P)/[L : ℚ]`, and
  `Heights.Different.log_absNorm_differentIdeal_div_eq_finsum`, the grouping
  `log N(𝔇)/[L : ℚ] = ∑ᶠ 𝔭, diffContrib L 𝔭` over the primes of `F`.
-/

namespace Heights.Different

open NumberField IsDedekindDomain Module

/-- The log-different of a number field: `log |d_K| / [K : ℚ]`. -/
noncomputable def logDisc (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log |(discr K : ℝ)| / finrank ℚ K

lemma logDisc_nonneg (K : Type*) [Field K] [NumberField K] : 0 ≤ logDisc K :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast Int.one_le_abs (discr_ne_zero K)))
    (by positivity)

section Tower

variable (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-- The different is a nonzero ideal. -/
lemma differentIdeal_ne_bot' : differentIdeal (𝓞 F) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot

lemma absNorm_differentIdeal_pos : 0 < Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot)

/-- `0 ≤ log N(𝔇_{L/F}) / [L : ℚ]`. -/
lemma log_absNorm_differentIdeal_div_nonneg :
    0 ≤ Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast absNorm_differentIdeal_pos F L))
    (by positivity)

/-- **The tower formula**: `logDisc L = logDisc F + log N(𝔇_{L/F}) / [L : ℚ]`. -/
theorem logDisc_eq_add :
    logDisc L = logDisc F +
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := F) (𝒪 := 𝓞 F) (L := L) (𝒪' := 𝓞 L)
  have hD : Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) ≠ 0 :=
    (absNorm_differentIdeal_pos F L).ne'
  have hF : (discr F).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero F)
  have hFL : (finrank F L : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  unfold logDisc
  rw [← Int.cast_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.cast_natAbs, h, Nat.cast_mul,
    Nat.cast_pow, Real.log_mul (by exact_mod_cast hD)
    (by positivity), Real.log_pow, ← finrank_mul_finrank ℚ F L, Nat.cast_mul, add_div,
    add_comm]
  congr 1
  rw [mul_comm ((finrank F L : ℕ) : ℝ), mul_div_mul_right _ _ hFL]

end Tower

/-! ### Multiplicities of prime ideals -/

section Multiplicity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma finiteMultiplicity_of_isPrime {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥) :
    FiniteMultiplicity P I :=
  FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP inferInstance) hI

/-- `P^n ∣ I ↔ n ≤ ord_P(I)` for a nonzero prime `P` and `I ≠ 0`. -/
lemma pow_dvd_iff_le_multiplicity {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥)
    {n : ℕ} : P ^ n ∣ I ↔ n ≤ multiplicity P I :=
  (finiteMultiplicity_of_isPrime hP hI).pow_dvd_iff_le_multiplicity

/-- `ord_P(I) ≤ n` if `P^{n+1} ∤ I`. -/
lemma multiplicity_le_of_not_pow_dvd {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥)
    {n : ℕ} (h : ¬ P ^ (n + 1) ∣ I) : multiplicity P I ≤ n := by
  rw [pow_dvd_iff_le_multiplicity hP hI] at h
  omega

omit [IsDedekindDomain R] in
lemma multiplicity_eq_zero_of_not_dvd {P I : Ideal R} (h : ¬ P ∣ I) : multiplicity P I = 0 :=
  multiplicity_eq_zero.mpr h

end Multiplicity

/-! ### The local decomposition of the norm -/

section Local

variable {K : Type*} [Field K] [NumberField K]

lemma one_lt_absNorm (P : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm P.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm P

lemma log_absNorm_nonneg (I : Ideal (𝓞 K)) : 0 ≤ Real.log (Ideal.absNorm I) :=
  Real.log_natCast_nonneg _

/-- The finitely many primes dividing a nonzero ideal. -/
noncomputable def primeSupport {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors hI).toFinset

lemma mem_primeSupport {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ primeSupport hI ↔ P.asIdeal ∣ I := by
  simp [primeSupport]

/-- **The local decomposition of the norm**: `log N(I) = ∑ᶠ P, ord_P(I)·log N(P)`. -/
theorem log_absNorm_eq_finsum {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Real.log (Ideal.absNorm I) = ∑ᶠ P : HeightOneSpectrum (𝓞 K),
      (multiplicity P.asIdeal I : ℝ) * Real.log (Ideal.absNorm P.asIdeal) := by
  classical
  set s := primeSupport hI
  have hzero : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ s → multiplicity P.asIdeal I = 0 := by
    intro P hP
    exact multiplicity_eq_zero_of_not_dvd (by rwa [mem_primeSupport] at hP)
  have hprod : I = ∏ P ∈ s, P.asIdeal ^ multiplicity P.asIdeal I := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
    refine finprod_eq_prod_of_mulSupport_subset _ fun P hP => ?_
    by_contra h
    exact hP (show P.asIdeal ^ multiplicity P.asIdeal I = 1 by rw [hzero P h, pow_zero])
  rw [finsum_eq_sum_of_support_subset (s := s)]
  · conv_lhs => rw [hprod]
    rw [map_prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun P _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · intro P _
      rw [map_pow, Nat.cast_pow]
      exact pow_ne_zero _ (by exact_mod_cast (one_lt_absNorm P).ne_bot)
  · intro P hP
    by_contra h
    exact hP (by simp [hzero P h])

end Local

/-! ### Grouping by the primes of the base field -/

section Group

variable {F : Type*} [Field F] [NumberField F] (L : Type*) [Field L] [NumberField L]
  [Algebra F L]

/-- The prime of `F` below a prime of `L`. -/
def primeBelow (P : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)

/-- The contribution of the primes of `L` over `𝔭` to `log N(𝔇_{L/F}) / [L : ℚ]`:
`∑_{P ∣ 𝔭} ord_P(𝔇)·log N(P) / [L : ℚ]`. -/
noncomputable def diffContrib (𝔭 : Ideal (𝓞 F)) : ℝ :=
  ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
    (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * Real.log (Ideal.absNorm P) /
      finrank ℚ L

variable {L}

omit [NumberField F] in
lemma diffContrib_nonneg (𝔭 : Ideal (𝓞 F)) : 0 ≤ diffContrib L 𝔭 :=
  Finset.sum_nonneg fun _ _ => div_nonneg (mul_nonneg (by positivity)
    (log_absNorm_nonneg _)) (by positivity)

omit [NumberField F] in
lemma mem_primesOverFinset_iff' {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥)
    {P : Ideal (𝓞 L)} :
    P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L) ↔ P.IsPrime ∧ P.LiesOver 𝔭 := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff h𝔭]
  rfl

variable (F L) in
/-- The summand `ord_P(𝔇)·log N(P)/[L : ℚ]` at a prime `P` of `L`. -/
noncomputable def diffTerm (P : HeightOneSpectrum (𝓞 L)) : ℝ :=
  (multiplicity P.asIdeal (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) *
    Real.log (Ideal.absNorm P.asIdeal) / finrank ℚ L

open scoped Classical in
/-- `diffContrib 𝔭` as a sum over the primes of `L` dividing `𝔇` and lying over `𝔭`. -/
lemma diffContrib_eq_sum_filter (𝔭 : HeightOneSpectrum (𝓞 F)) :
    diffContrib L 𝔭.asIdeal = ∑ P ∈ (primeSupport (differentIdeal_ne_bot' F L)).filter
      (fun P => primeBelow L P = 𝔭), diffTerm F L P := by
  classical
  haveI := 𝔭.isMaximal
  symm
  refine Finset.sum_bij_ne_zero (fun P _ _ => P.asIdeal) ?_ ?_ ?_ ?_
  · intro P hP _
    rw [mem_primesOverFinset_iff' 𝔭.ne_bot]
    refine ⟨P.isPrime, ⟨?_⟩⟩
    have := (Finset.mem_filter.mp hP).2
    rw [← this]
    rfl
  · intro P _ _ Q _ _ h
    exact HeightOneSpectrum.ext h
  · intro Q hQ hne
    rw [mem_primesOverFinset_iff' 𝔭.ne_bot] at hQ
    obtain ⟨hQp, hQl⟩ := hQ
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
    let Q' : HeightOneSpectrum (𝓞 L) := ⟨Q, hQp, hQ0⟩
    have hdvd : Q ∣ differentIdeal (𝓞 F) (𝓞 L) := by
      by_contra h
      apply hne
      rw [multiplicity_eq_zero_of_not_dvd h]
      simp
    refine ⟨Q', ?_, ?_, rfl⟩
    · rw [Finset.mem_filter, mem_primeSupport]
      refine ⟨hdvd, HeightOneSpectrum.ext ?_⟩
      exact (Ideal.LiesOver.over (P := Q) (p := 𝔭.asIdeal)).symm
    · exact hne
  · intro P _ _
    rfl

variable (L) in
/-- **The grouped local decomposition**:
`log N(𝔇_{L/F}) / [L : ℚ] = ∑ᶠ 𝔭, diffContrib 𝔭`. -/
theorem log_absNorm_differentIdeal_div_eq_finsum :
    Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L =
      ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 F), diffContrib L 𝔭.asIdeal := by
  classical
  set s := primeSupport (differentIdeal_ne_bot' F L)
  have hsum : Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L =
      ∑ P ∈ s, diffTerm F L P := by
    rw [log_absNorm_eq_finsum (differentIdeal_ne_bot' F L), finsum_eq_sum_of_support_subset
      (s := s), Finset.sum_div]
    · rfl
    · intro P hP
      rw [Finset.mem_coe, mem_primeSupport]
      by_contra h
      exact hP (by simp [multiplicity_eq_zero_of_not_dvd h])
  rw [hsum, finsum_eq_sum_of_support_subset (s := s.image (primeBelow (F := F) L))]
  · rw [← Finset.sum_fiberwise_of_maps_to (g := primeBelow (F := F) L)
      (t := s.image (primeBelow (F := F) L))
      (fun P hP => Finset.mem_image_of_mem _ hP)]
    exact Finset.sum_congr rfl fun 𝔭 _ => (diffContrib_eq_sum_filter 𝔭).symm
  · intro 𝔭 h𝔭
    rw [Function.mem_support, diffContrib_eq_sum_filter] at h𝔭
    obtain ⟨P, hP, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h𝔭
    rw [Finset.mem_filter] at hP
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨P, hP.1, hP.2⟩

variable (L) in
/-- Only finitely many primes of `F` contribute to the different. -/
theorem diffContrib_support_finite :
    (Function.support fun 𝔭 : HeightOneSpectrum (𝓞 F) =>
      diffContrib L 𝔭.asIdeal).Finite := by
  classical
  refine ((primeSupport (differentIdeal_ne_bot' F L)).image
    (primeBelow (F := F) L)).finite_toSet.subset ?_
  intro 𝔭 h𝔭
  rw [Function.mem_support, diffContrib_eq_sum_filter] at h𝔭
  obtain ⟨P, hP, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h𝔭
  rw [Finset.mem_filter] at hP
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨P, hP.1, hP.2⟩

end Group

end Heights.Different
