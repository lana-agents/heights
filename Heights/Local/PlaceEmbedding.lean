/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Finite places of a number field and embeddings into `ℚ̄_p`

Let `F` be a number field and `p` a prime. Every ring homomorphism `τ : F → ℚ̄_p`
(`ℚ̄_p = PadicAlgCl p`, with its spectral norm) defines a nonarchimedean absolute value
`y ↦ ‖τ y‖` on `F`, and every finite place `w` of `F` over `p` arises in this way up to a
power: there is a `τ` and a natural number `0 < N ≤ [F : ℚ]` with `w y = ‖τ y‖ ^ N`
for all `y ∈ F` (`Heights.Local.exists_ringHom_padicAlgCl_eq_pow`). Here `N = e_w f_w`
is the local degree.

This is used to translate the compactness argument of [GenEll], Theorem 2.1 (which works
with the `[F : ℚ]` points of `U_ℙ(ℚ̄_p)` determined by a point of degree `d`, i.e. with
the embeddings `F → ℚ̄_p`), into bounds at the finite places of `F`, which is how
compactly bounded subsets of the tripod are described in terms of Mathlib's
`NumberField.FinitePlace`.

The proof: `y ↦ ‖τ y‖` is `≤ 1` on `𝓞 F` (ultrametric root bound), so
`𝔭_τ = {y ∈ 𝓞 F | ‖τ y‖ < 1}` is a nonzero prime; the absolute values `w` and
`‖τ ·‖` have the same unit ball (the localisation of `𝓞 F` at `𝔭_τ`), hence are equivalent,
`w = ‖τ ·‖ ^ c` (`AbsoluteValue.isEquiv_iff_exists_rpow_eq`), and evaluating at `p` gives
`c = e f`. Every prime `𝔭 ∣ p` is some `𝔭_τ`: otherwise, by prime avoidance, some `y ∈ 𝔭`
has `‖τ y‖ = 1` for all `τ`, whence `|N_{F/ℚ}(y)|_p = ∏_τ ‖τ y‖ = 1`, contradicting
`p ∣ N(𝔭) ∣ N_{F/ℚ}(y)`.
-/

namespace Heights.Local

open NumberField IsDedekindDomain HeightOneSpectrum Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Ultrametric root bound**: in an ultrametric normed field, a root of a monic polynomial
with coefficients of norm `≤ 1` has norm `≤ 1`. -/
theorem norm_le_one_of_monic_of_eval_eq_zero {E : Type*} [NormedField E] [IsUltrametricDist E]
    {P : E[X]} (hP : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {x : E} (hx : P.eval x = 0) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  set n := P.natDegree with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : P = 1 := hP.natDegree_eq_zero.mp h0
    rw [h1, eval_one] at hx
    exact one_ne_zero hx
  have hsum : P.eval x = x ^ n + ∑ i ∈ Finset.range n, P.coeff i * x ^ i := by
    conv_lhs => rw [hP.as_sum]
    simp [eval_finsetSum, hn]
  rw [hsum, add_eq_zero_iff_eq_neg] at hx
  have hbound : ‖∑ i ∈ Finset.range n, P.coeff i * x ^ i‖ ≤ ‖x‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖P.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
          mul_le_mul (hc i) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (n - 1) := one_mul _
  have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ (n - 1) := by
    rw [← norm_pow, hx, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
  linarith

variable {F : Type*} [Field F] [NumberField F]

/-- The image of an algebraic integer under a ring homomorphism `F → ℚ̄_p` has norm `≤ 1`. -/
theorem norm_ringHom_le_one (τ : F →+* PadicAlgCl p) (y : 𝓞 F) : ‖τ y‖ ≤ 1 := by
  have hint : IsIntegral ℤ y := RingOfIntegers.isIntegral y
  set P := (minpoly ℤ y).map (Int.castRingHom (PadicAlgCl p)) with hP
  refine norm_le_one_of_monic_of_eval_eq_zero (P := P)
    ((minpoly.monic hint).map (Int.castRingHom (PadicAlgCl p))) (fun i => ?_) ?_
  · rw [hP, coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ _
  · rw [hP, eval_map]
    have h0 : eval₂ (algebraMap ℤ (𝓞 F)) y (minpoly ℤ y) = 0 := minpoly.aeval ℤ y
    have h1 := congrArg (τ.comp (algebraMap (𝓞 F) F)) h0
    rw [hom_eval₂, map_zero] at h1
    convert h1 using 2
    all_goals first | exact RingHom.ext_int _ _ | rfl

/-- The absolute value `y ↦ ‖τ y‖` on `F` defined by `τ : F → ℚ̄_p`. -/
noncomputable def ringHomAbv (τ : F →+* PadicAlgCl p) : AbsoluteValue F ℝ :=
  (NormedField.toAbsoluteValue (PadicAlgCl p)).comp τ.injective

@[simp] theorem ringHomAbv_apply (τ : F →+* PadicAlgCl p) (y : F) :
    ringHomAbv τ y = ‖τ y‖ := rfl

/-- `‖τ p‖ = p⁻¹`. -/
theorem norm_ringHom_natCast_p (τ : F →+* PadicAlgCl p) : ‖τ (p : F)‖ = (p : ℝ)⁻¹ := by
  rw [map_natCast]
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    simp
  rw [this, norm_algebraMap', Padic.norm_p]

/-- The prime ideal `𝔭_τ = {y ∈ 𝓞 F | ‖τ y‖ < 1}` defined by `τ : F → ℚ̄_p`. -/
noncomputable def primeOfRingHom (τ : F →+* PadicAlgCl p) : Ideal (𝓞 F) where
  carrier := {y | ‖τ y‖ < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c y hy := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at hy ⊢
    calc ‖τ c‖ * ‖τ y‖ ≤ 1 * ‖τ y‖ :=
          mul_le_mul_of_nonneg_right (norm_ringHom_le_one τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hy

theorem mem_primeOfRingHom {τ : F →+* PadicAlgCl p} {y : 𝓞 F} :
    y ∈ primeOfRingHom τ ↔ ‖τ y‖ < 1 := Iff.rfl

theorem natCast_p_mem_primeOfRingHom (τ : F →+* PadicAlgCl p) :
    ((p : ℕ) : 𝓞 F) ∈ primeOfRingHom τ := by
  rw [mem_primeOfRingHom]
  have : τ (((p : ℕ) : 𝓞 F) : F) = τ (p : F) := by simp
  rw [this, norm_ringHom_natCast_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

instance (τ : F →+* PadicAlgCl p) : (primeOfRingHom τ).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, mem_primeOfRingHom]
    simp
  mem_or_mem' {a b} hab := by
    rw [mem_primeOfRingHom, mem_primeOfRingHom]
    rw [mem_primeOfRingHom] at hab
    simp only [map_mul, norm_mul] at hab
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)
    rw [one_mul] at this
    linarith

theorem primeOfRingHom_ne_bot (τ : F →+* PadicAlgCl p) : primeOfRingHom τ ≠ ⊥ := by
  intro h
  have := natCast_p_mem_primeOfRingHom τ
  rw [h, Ideal.mem_bot] at this
  exact (Nat.cast_ne_zero.mpr hp.out.ne_zero) this

/-- The height one prime `𝔭_τ`. -/
noncomputable def placeOfRingHom (τ : F →+* PadicAlgCl p) : HeightOneSpectrum (𝓞 F) :=
  ⟨primeOfRingHom τ, inferInstance, primeOfRingHom_ne_bot τ⟩

/-- For `d ∉ 𝔭_τ`, `‖τ d‖ = 1`. -/
theorem norm_eq_one_of_notMem {τ : F →+* PadicAlgCl p} {d : 𝓞 F}
    (hd : d ∉ primeOfRingHom τ) : ‖τ d‖ = 1 := by
  rw [mem_primeOfRingHom, not_lt] at hd
  exact le_antisymm (norm_ringHom_le_one τ d) hd

/-- For `y ∈ F` with `v`-adic valuation `≤ 1` there are `n ∈ 𝓞 F` and `d ∉ 𝔭` with
`y d = n`. -/
theorem valuation_le_one_iff_norm_le_one (τ : F →+* PadicAlgCl p) (y : F) :
    (placeOfRingHom τ).valuation F y ≤ 1 ↔ ‖τ y‖ ≤ 1 := by
  set v := placeOfRingHom τ with hv
  constructor
  · intro hy
    obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer v y hy
    have hd : ‖τ (algebraMap (𝓞 F) F d)‖ = 1 := norm_eq_one_of_notMem d.2
    have h := congrArg (fun z => ‖τ z‖) hnd
    simp only [map_mul, norm_mul, hd, mul_one] at h
    rw [h]
    exact norm_ringHom_le_one τ n
  · intro hy
    by_contra hlt
    push Not at hlt
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hlt
    have hinv : v.valuation F y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer v y⁻¹ hinv.le
    have hn : n ∈ v.asIdeal := by
      rw [← intValuation_lt_one_iff_mem, ← valuation_of_algebraMap (K := F)]
      have : v.valuation F (algebraMap (𝓞 F) F n) = v.valuation F y⁻¹ := by
        rw [← hnd, map_mul, valuation_of_algebraMap,
          (intValuation_eq_one_iff_mem_primeCompl v d).mpr d.2, mul_one]
      rw [this]
      exact hinv
    have hn' : ‖τ (algebraMap (𝓞 F) F n)‖ < 1 := hn
    have hd : ‖τ (algebraMap (𝓞 F) F d)‖ = 1 := norm_eq_one_of_notMem d.2
    have h := congrArg (fun z => ‖τ z‖) hnd
    simp only [map_mul, norm_mul, hd, mul_one, map_inv₀, norm_inv] at h
    rw [← h] at hn'
    have hpos : 0 < ‖τ y‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hy0)
    have : 1 < ‖τ y‖ := by
      rw [inv_lt_one₀ hpos] at hn'
      exact hn'
    linarith

/-- The absolute value `adicAbv` at `𝔭_τ` and `‖τ ·‖` have the same unit ball. -/
theorem adicAbv_le_one_iff (τ : F →+* PadicAlgCl p) (y : F) :
    adicAbv F (placeOfRingHom τ) y ≤ 1 ↔ ‖τ y‖ ≤ 1 := by
  rw [adicAbv_def, ← valuation_le_one_iff_norm_le_one τ y]
  have := WithZeroMulInt.toNNReal_le_one_iff (m := (placeOfRingHom τ).valuation F y)
    (one_lt_absNorm_nnreal (placeOfRingHom τ))
  exact_mod_cast this

/-- `adicAbv` at `𝔭_τ` is equivalent to `‖τ ·‖`. -/
theorem isEquiv_ringHomAbv (τ : F →+* PadicAlgCl p) :
    (ringHomAbv τ).IsEquiv (adicAbv F (placeOfRingHom τ)) := by
  intro x y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hA : 0 < ringHomAbv τ y := (ringHomAbv τ).pos hy
  have hB : 0 < adicAbv F (placeOfRingHom τ) y := (adicAbv F (placeOfRingHom τ)).pos hy
  rw [← div_le_one hA, ← div_le_one hB, ← map_div₀, ← map_div₀, ringHomAbv_apply,
    adicAbv_le_one_iff]

/-- The norm of `𝔭_τ` is a positive power of `p`. -/
theorem exists_absNorm_eq_pow {v : HeightOneSpectrum (𝓞 F)} (hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∃ j : ℕ, 0 < j ∧ Ideal.absNorm v.asIdeal = p ^ j := by
  have hle : Ideal.span {((p : ℕ) : 𝓞 F)} ≤ v.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpv
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
    Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  refine ⟨j, Nat.pos_of_ne_zero fun h0 => ?_, hj⟩
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at hj
  exact v.isPrime.ne_top hj

/-- `‖τ ·‖ ^ N = adicAbv` at `𝔭_τ` for a natural number `0 < N ≤ [F : ℚ]`. -/
theorem exists_pow_eq_adicAbv (τ : F →+* PadicAlgCl p) :
    ∃ N : ℕ, 0 < N ∧ N ≤ Module.finrank ℚ F ∧
      ∀ y : F, adicAbv F (placeOfRingHom τ) y = ‖τ y‖ ^ N := by
  set v := placeOfRingHom τ with hv
  obtain ⟨c, hc, hcw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp (isEquiv_ringHomAbv τ)
  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := natCast_p_mem_primeOfRingHom τ
  obtain ⟨j, hj, hjN⟩ := exists_absNorm_eq_pow hpv
  have hp0 : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  -- the multiplicity `m` of `𝔭_τ` in `p`
  set m := multiplicity v.asIdeal (Ideal.span {((p : ℕ) : 𝓞 F)}) with hm
  have hmp := HeightOneSpectrum.embedding_mul_absNorm (K := F) v hp0
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity
      (mt Submodule.span_singleton_eq_bot.mp hp0), map_pow, hjN, ← hm,
    FinitePlace.norm_embedding] at hmp
  -- evaluate the equivalence at `p`
  have hcp := congrFun hcw ((p : ℕ) : F)
  simp only [ringHomAbv_apply, norm_ringHom_natCast_p] at hcp
  have hpF : algebraMap (𝓞 F) F ((p : ℕ) : 𝓞 F) = ((p : ℕ) : F) := by simp
  rw [hpF] at hmp
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hval' : adicAbv F v ((p : ℕ) : F) * (p : ℝ) ^ (j * m) = 1 := by
    push_cast at hmp ⊢
    rw [pow_mul]
    exact hmp
  have hval : adicAbv F v ((p : ℕ) : F) = ((p : ℝ) ^ (j * m))⁻¹ :=
    eq_inv_of_mul_eq_one_left hval'
  have hceq : c = (j * m : ℕ) := by
    rw [hval] at hcp
    have h1 : Real.log (((p : ℝ)⁻¹) ^ c) = Real.log (((p : ℝ) ^ (j * m))⁻¹) := by rw [hcp]
    rw [Real.log_rpow (by positivity), Real.log_inv, Real.log_inv, Real.log_pow] at h1
    have hlogp : 0 < Real.log p := Real.log_pos hpR
    have h2 : c * Real.log p = ((j * m : ℕ) : ℝ) * Real.log p := by linarith
    exact mul_right_cancel₀ hlogp.ne' h2
  refine ⟨j * m, ?_, ?_, fun y => ?_⟩
  · have : (0 : ℝ) < ((j * m : ℕ) : ℝ) := hceq ▸ hc
    exact_mod_cast this
  · -- `N(𝔭)^m ∣ N(p) = p^[F:ℚ]`
    have hdiv : v.asIdeal ^ m ∣ Ideal.span {((p : ℕ) : 𝓞 F)} := pow_multiplicity_dvd _ _
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
    rw [map_pow, hjN, Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 F)),
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp hdvd
    rwa [RingOfIntegers.rank] at this
  · have := congrFun hcw y
    simp only [ringHomAbv_apply] at this
    rw [← this, hceq, Real.rpow_natCast]

/-- **Every prime of `𝓞 F` over `p` is `𝔭_τ` for some `τ : F → ℚ̄_p`.** -/
theorem exists_placeOfRingHom_eq {v : HeightOneSpectrum (𝓞 F)}
    (hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) : ∃ τ : F →+* PadicAlgCl p, placeOfRingHom τ = v := by
  classical
  by_contra hne
  push Not at hne
  -- prime avoidance: some `y ∈ 𝔭` lies in no `𝔭_τ`
  have hnot : ¬ ((v.asIdeal : Set (𝓞 F)) ⊆ ⋃ τ ∈ (Finset.univ : Finset (F →+* PadicAlgCl p)),
      (primeOfRingHom τ : Set (𝓞 F))) := by
    intro hsub
    obtain ⟨τ, -, hτ⟩ := (Ideal.subset_union_prime (s := Finset.univ)
      (f := fun τ => primeOfRingHom τ) (Classical.arbitrary _) (Classical.arbitrary _)
      (fun τ _ _ _ => inferInstance)).mp hsub
    have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    have heq : v.asIdeal = primeOfRingHom τ :=
      hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hτ
    exact hne τ (HeightOneSpectrum.ext heq.symm)
  obtain ⟨y, hyv, hyτ⟩ := Set.not_subset.mp hnot
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe, not_exists] at hyτ
  have hone : ∀ τ : F →+* PadicAlgCl p, ‖τ y‖ = 1 := fun τ => norm_eq_one_of_notMem (hyτ τ)
  -- the norm of `y`
  have hnorm := Algebra.norm_eq_prod_embeddings ℚ (PadicAlgCl p) (y : F)
  have hnorm1 : ‖algebraMap ℚ (PadicAlgCl p) (Algebra.norm ℚ (y : F))‖ = 1 := by
    rw [hnorm, norm_prod]
    exact Finset.prod_eq_one fun σ _ => hone σ.toRingHom
  rw [← Algebra.coe_norm_int] at hnorm1
  -- `p` divides the norm of `y`
  have hle : Ideal.span {y} ≤ v.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hyv
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  obtain ⟨j, hj, hjN⟩ := exists_absNorm_eq_pow hpv
  rw [hjN, Ideal.absNorm_span_singleton] at hdvd
  have hpdvd : (p : ℤ) ∣ Algebra.norm ℤ y := by
    have : p ∣ (Algebra.norm ℤ y).natAbs := (dvd_pow_self p hj.ne').trans hdvd
    exact Int.natCast_dvd.mpr this
  obtain ⟨k, hk⟩ := hpdvd
  rw [hk] at hnorm1
  have : ‖algebraMap ℚ (PadicAlgCl p) (((p : ℤ) * k : ℤ) : ℚ)‖ < 1 := by
    have h1 : algebraMap ℚ (PadicAlgCl p) (((p : ℤ) * k : ℤ) : ℚ) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℚ_[p]) * (k : ℚ_[p])) := by
      simp
    rw [h1, norm_algebraMap', norm_mul, Padic.norm_p]
    have hk1 : ‖(k : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one k
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    calc (p : ℝ)⁻¹ * ‖(k : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ < 1 := by rw [mul_one]; exact hpinv
  linarith

/-- **Finite places of a number field and embeddings into `ℚ̄_p`**: for a finite place `w` of
`F` whose prime contains `p`, there are `τ : F → ℚ̄_p` and `0 < N ≤ [F : ℚ]` with
`w y = ‖τ y‖ ^ N` for all `y`. -/
theorem exists_ringHom_padicAlgCl_eq_pow (w : FinitePlace F)
    (hpw : ((p : ℕ) : 𝓞 F) ∈ w.maximalIdeal.asIdeal) :
    ∃ τ : F →+* PadicAlgCl p, ∃ N : ℕ, 0 < N ∧ N ≤ Module.finrank ℚ F ∧
      ∀ y : F, w y = ‖τ y‖ ^ N := by
  obtain ⟨τ, hτ⟩ := exists_placeOfRingHom_eq hpw
  obtain ⟨N, hN, hNle, hNeq⟩ := exists_pow_eq_adicAbv τ
  refine ⟨τ, N, hN, hNle, fun y => ?_⟩
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding, ← hτ, hNeq]

end Heights.Local
