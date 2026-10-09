/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Different.Conductor
import Heights.Different.Unramified

/-!
# The different of a Kummer extension of bounded degree

Let `F` be a number field, `N ≥ 1`, `c ∈ F`, and `L = F(a, b)` with `a^N = c`,
`b^N = 1 − c`, presented as a tower `F ⊆ M = F[a] ⊆ L = M[b]`. Let `G ⊆ F` be a finite set
such that `c` and `1 − c` are units at every finite place of `F` which does not meet `G`.
Then (the number-field core of the second half of [GenEll] Proposition 1.7)

* `Heights.Different.log_absNorm_differentIdeal_div_le_cond_add`:
  `log N(𝔇_{L/F})/[L : ℚ] ≤ cond G + kummerConst N`, and
* `Heights.Different.logDisc_le_logDisc_add_cond_add`:
  `logDisc L ≤ logDisc F + cond G + kummerConst N`,

with the explicit constant `kummerConst N = ∑_{p ≤ N², p prime} (log p + 2 log N)` depending
only on `N`. The versions `..._of_adjoin` take `a, b ∈ L` with `F⟮a, b⟯ = L` instead of the
tower.

The proof applies `Heights.Different.log_absNorm_differentIdeal_div_le` with `S` the primes
`≤ N²` (note `[L : F] ≤ N²`) and `B` the places meeting `G`. At a place `u ∉ B` not over `S`,
`c` is a `u`-unit but need not be integral; we choose `t ∈ 𝓞 F ∖ 𝔭_u` with `t c ∈ 𝓞 F`
(`Heights.Different.exists_mul_mem_of_apply_le_one`), and apply the Kummer criterion
`Heights.Different.ramificationIdx'_eq_one_of_pow_eq_of_pow_eq` to the integral generators
`t a`, `t b`, with `(t a)^N = t^{N-1}·(t c)` and `(t b)^N = t^{N-1}·(t − t c)`, which are
`u`-units, while `N ∉ 𝔭_u`.
-/

namespace Heights.Different

open NumberField IsDedekindDomain Module Polynomial

/-! ### Clearing denominators locally -/

section Local

variable {F : Type*} [Field F] [NumberField F]

/-- For `x ∈ 𝓞 F`: `u x = 1 ↔ x ∉ 𝔭_u`. -/
lemma apply_coe_eq_one_iff (u : FinitePlace F) (x : 𝓞 F) :
    u (x : F) = 1 ↔ x ∉ u.maximalIdeal.asIdeal := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_eq_one_iff_notMem F u.maximalIdeal x

/-- `u x = N(u)^{-ord_u x}` for `x ∈ 𝓞 F ∖ {0}`. -/
lemma apply_coe_eq_inv_pow (u : FinitePlace F) {x : 𝓞 F} (hx : x ≠ 0) :
    u (x : F) = ((placeNorm u : ℝ) ^ multiplicity u.maximalIdeal.asIdeal
      (Ideal.span {x}))⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (FinitePlace.apply_mul_absNorm_pow_eq_one u hx)

/-- **Clearing the denominator of a `u`-integral element**: if `u c ≤ 1`, there is
`t ∈ 𝓞 F ∖ 𝔭_u` with `t c ∈ 𝓞 F`. -/
theorem exists_mul_mem_of_apply_le_one (u : FinitePlace F) {c : F} (hc : u c ≤ 1) :
    ∃ t : 𝓞 F, t ∉ u.maximalIdeal.asIdeal ∧ ∃ z : 𝓞 F, (t : F) * c = z := by
  set P := u.maximalIdeal.asIdeal
  haveI : P.IsPrime := u.maximalIdeal.isPrime
  have hP : P ≠ ⊥ := u.maximalIdeal.ne_bot
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hy' : (algebraMap (𝓞 F) F y) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hy0
  by_cases hx0 : x = 0
  · refine ⟨1, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance), 0, ?_⟩
    simp [hx0]
  have hsx : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hsy : Ideal.span {y} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  set k := multiplicity P (Ideal.span {y})
  -- `ord_u y ≤ ord_u x`
  have hk : k ≤ multiplicity P (Ideal.span {x}) := by
    rw [map_div₀, apply_coe_eq_inv_pow u hx0, apply_coe_eq_inv_pow u hy0, inv_div_inv,
      div_le_one (pow_pos (by exact_mod_cast (zero_lt_one.trans (one_lt_placeNorm u))) _)] at hc
    exact (pow_le_pow_iff_right₀ (by exact_mod_cast one_lt_placeNorm u)).mp hc
  have hxk : x ∈ P ^ k := Ideal.dvd_span_singleton.mp
    ((pow_dvd_iff_le_multiplicity hP hsx).mpr hk)
  -- `(y) = P^k·B` with `P ∤ B`
  obtain ⟨B, hB⟩ : P ^ k ∣ Ideal.span {y} := (pow_dvd_iff_le_multiplicity hP hsy).mpr le_rfl
  have hPB : ¬ B ≤ P := by
    intro hle
    have h1 : P ^ (k + 1) ∣ Ideal.span {y} := by
      rw [hB, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have := (pow_dvd_iff_le_multiplicity hP hsy).mp h1
    omega
  obtain ⟨t, htB, htP⟩ := SetLike.not_le_iff_exists.mp hPB
  have htx : t * x ∈ Ideal.span {y} := by
    rw [hB, mul_comm t x]
    exact Ideal.mul_mem_mul hxk htB
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp htx
  refine ⟨t, htP, z, ?_⟩
  rw [mul_div_assoc', div_eq_iff hy', RingOfIntegers.coe_eq_algebraMap,
    RingOfIntegers.coe_eq_algebraMap, ← map_mul, ← map_mul, ← hz, mul_comm]

end Local

/-! ### Degree bounds and generators -/

section Generators

/-- `[E : K] ≤ N` if `E = K[x]` with `x^N ∈ K`, `N ≥ 1`. -/
lemma finrank_le_of_adjoin_eq_top_of_pow_eq {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] {x : E} (hx : Algebra.adjoin K {x} = ⊤) {N : ℕ} (hN : 0 < N)
    {c : K} (hxc : x ^ N = algebraMap K E c) : finrank K E ≤ N := by
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  have htop : IntermediateField.adjoin K {x} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hx,
      IntermediateField.top_toSubalgebra]
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint]
  have hdeg := minpoly.degree_le_of_ne_zero K x (X_pow_sub_C_ne_zero hN c)
    (by simp [hxc])
  have := natDegree_le_natDegree hdeg
  rwa [natDegree_X_pow_sub_C] at this

/-- `K[t·x] = ⊤` if `K[x] = ⊤` and `t ≠ 0`. -/
lemma adjoin_mul_eq_top {K E : Type*} [Field K] [Ring E] [Algebra K E] {x : E}
    (hx : Algebra.adjoin K {x} = ⊤) {t : K} (ht : t ≠ 0) :
    Algebra.adjoin K {algebraMap K E t * x} = ⊤ := by
  rw [eq_top_iff, ← hx, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  have h : x = t⁻¹ • (algebraMap K E t * x) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
  have hmem : t⁻¹ • (algebraMap K E t * x) ∈ Algebra.adjoin K {algebraMap K E t * x} :=
    Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _
  rw [← h] at hmem
  exact hmem

/-- An element of `𝓞` from an integral element `t·x` with `(t x)^N ∈ 𝓞 F`. -/
lemma isIntegral_of_pow_eq_coe {F E : Type*} [Field F] [NumberField F] [Field E]
    [Algebra F E] {x : E} {N : ℕ} (hN : 0 < N) {a : 𝓞 F}
    (h : x ^ N = algebraMap F E (a : F)) : IsIntegral ℤ x := by
  refine IsIntegral.of_pow hN ?_
  rw [h]
  exact (RingOfIntegers.isIntegral_coe a).algebraMap

end Generators

/-! ### Unramifiedness at the places where `c`, `1 − c` are units -/

section Unramified

variable {F : Type*} [Field F] [NumberField F] (M : Type*) [Field M] [NumberField M]
  {L : Type*} [Field L] [NumberField L] [Algebra F M] [Algebra M L] [Algebra F L]
  [IsScalarTower F M L]

lemma coe_algebraMap_ringOfIntegers {K E : Type*} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] (x : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 E) x : 𝓞 E) : E) = algebraMap K E (x : K) := by
  rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- **Unramifiedness of the Kummer tower at a place where `c`, `1 − c` are units**: if
`M = F[a]`, `L = M[b]`, `a^N = c`, `b^N = 1 − c`, `N ≥ 1`, `u c = u (1 − c) = 1` and
`N ∉ 𝔭_u`, then every prime of `L` over `𝔭_u` is unramified. -/
theorem ramificationIdx'_eq_one_of_kummer {N : ℕ} (hN : 0 < N) {c : F} {a : M} {b : L}
    (ha : a ^ N = algebraMap F M c) (hb : b ^ N = 1 - algebraMap F L c)
    (haM : Algebra.adjoin F {a} = ⊤) (hbL : Algebra.adjoin M {b} = ⊤)
    (u : FinitePlace F) (hc : u c = 1) (hc' : u (1 - c) = 1)
    (hNu : (N : 𝓞 F) ∉ u.maximalIdeal.asIdeal)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver u.maximalIdeal.asIdeal] :
    u.maximalIdeal.asIdeal.ramificationIdx' P = 1 := by
  set 𝔭 := u.maximalIdeal.asIdeal
  haveI : 𝔭.IsMaximal := u.maximalIdeal.isMaximal
  haveI : 𝔭.IsPrime := u.maximalIdeal.isPrime
  obtain ⟨t, ht, z, hz⟩ := exists_mul_mem_of_apply_le_one u hc.le
  have ht1 : u (t : F) = 1 := (apply_coe_eq_one_iff u t).mpr ht
  have ht0 : (t : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht1
    exact zero_ne_one ht1
  -- the two Kummer radicands, `t^{N-1}·(t c)` and `t^{N-1}·(t − t c)`
  set a₀ : 𝓞 F := t ^ (N - 1) * z
  set b₀ : 𝓞 F := t ^ (N - 1) * (t - z)
  have hpow : ∀ s : F, (t : F) ^ N * s = (t : F) ^ (N - 1) * ((t : F) * s) := by
    intro s
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hN]
  have ha₀ : ((a₀ : 𝓞 F) : F) = (t : F) ^ N * c := by
    rw [hpow, hz]
    simp only [a₀, RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow]
  have hb₀ : ((b₀ : 𝓞 F) : F) = (t : F) ^ N * (1 - c) := by
    rw [hpow, mul_sub, mul_one, hz]
    simp only [b₀, RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_sub]
  -- `a₀`, `b₀` are `u`-units
  have hz1 : ∀ s : F, u s = 1 → u ((t : F) ^ N * s) = 1 := by
    intro s hs
    rw [map_mul, map_pow, ht1, hs, one_pow, one_mul]
  have ha₀P : a₀ ∉ 𝔭 := (apply_coe_eq_one_iff u a₀).mp (by rw [ha₀]; exact hz1 c hc)
  have hb₀P : b₀ ∉ 𝔭 := (apply_coe_eq_one_iff u b₀).mp (by rw [hb₀]; exact hz1 _ hc')
  have hNa : (N : 𝓞 F) * a₀ ∉ 𝔭 := fun h =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem h).elim hNu ha₀P
  have hNb : (N : 𝓞 F) * b₀ ∉ 𝔭 := fun h =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem h).elim hNu hb₀P
  -- the integral generators `t a`, `t b`
  set β : M := algebraMap F M t * a
  set γ : L := algebraMap F L t * b
  have hβ : β ^ N = algebraMap F M (a₀ : F) := by
    rw [mul_pow, ha, ← map_pow, ← map_mul, ha₀]
  have hγ : γ ^ N = algebraMap F L (b₀ : F) := by
    rw [mul_pow, hb, ← map_pow, hb₀, map_mul, map_sub, map_one]
  have hβi : IsIntegral ℤ β := isIntegral_of_pow_eq_coe hN hβ
  have hγi : IsIntegral ℤ γ := isIntegral_of_pow_eq_coe hN hγ
  refine ramificationIdx'_eq_one_of_pow_eq_of_pow_eq M u.maximalIdeal.ne_bot ⟨β, hβi⟩
    (adjoin_mul_eq_top haM ht0) N a₀ ?_ hNa ⟨γ, hγi⟩ ?_ N b₀ ?_ hNb P
  · ext
    rw [RingOfIntegers.coe_eq_algebraMap, map_pow, coe_algebraMap_ringOfIntegers]
    exact hβ
  · have h := adjoin_mul_eq_top hbL (K := M) (E := L) (map_ne_zero (algebraMap F M) |>.mpr ht0)
    rwa [← IsScalarTower.algebraMap_apply] at h
  · ext
    rw [RingOfIntegers.coe_eq_algebraMap, map_pow, coe_algebraMap_ringOfIntegers]
    exact hγ

end Unramified

/-! ### The bound on the different -/

section Bound

/-- The rational primes `≤ N²`. -/
noncomputable def kummerPrimes (N : ℕ) : Finset ℕ := (Finset.range (N ^ 2 + 1)).filter Nat.Prime

/-- The constant `∑_{p ≤ N², p prime} (log p + 2 log N)`. -/
noncomputable def kummerConst (N : ℕ) : ℝ :=
  ∑ p ∈ kummerPrimes N, (Real.log p + 2 * Real.log N)

lemma mem_kummerPrimes {N p : ℕ} : p ∈ kummerPrimes N ↔ p.Prime ∧ p ≤ N ^ 2 := by
  rw [kummerPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

lemma kummerConst_nonneg (N : ℕ) : 0 ≤ kummerConst N :=
  Finset.sum_nonneg fun p _ => add_nonneg (Real.log_natCast_nonneg p)
    (mul_nonneg zero_le_two (Real.log_natCast_nonneg N))

variable {F : Type*} [Field F] [NumberField F] (M : Type*) [Field M] [NumberField M]
  {L : Type*} [Field L] [NumberField L] [Algebra F M] [Algebra M L] [Algebra F L]
  [IsScalarTower F M L]

/-- **(W7b) The different of a Kummer extension of bounded degree**: let `M = F[a]`,
`L = M[b]` with `a^N = c ∈ F`, `b^N = 1 − c`, `N ≥ 1`, and let `G ⊆ F` be a finite set such
that `c`, `1 − c` are units at every finite place of `F` not meeting `G`. Then
`log N(𝔇_{L/F})/[L : ℚ] ≤ cond G + kummerConst N`. -/
theorem log_absNorm_differentIdeal_div_le_cond_add {N : ℕ} (hN : 0 < N) {c : F} {a : M}
    {b : L} (ha : a ^ N = algebraMap F M c) (hb : b ^ N = 1 - algebraMap F L c)
    (haM : Algebra.adjoin F {a} = ⊤) (hbL : Algebra.adjoin M {b} = ⊤) (G : Finset F)
    (hG : ∀ u : FinitePlace F, u ∉ meets G → u c = 1 ∧ u (1 - c) = 1) :
    Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L ≤
      cond G + kummerConst N := by
  classical
  -- the degree bound `[L : F] ≤ N²`
  have hM : finrank F M ≤ N := finrank_le_of_adjoin_eq_top_of_pow_eq haM hN ha
  have hL : finrank M L ≤ N := finrank_le_of_adjoin_eq_top_of_pow_eq hbL hN
    (c := 1 - algebraMap F M c) (by rw [hb, map_sub, map_one, ← IsScalarTower.algebraMap_apply])
  have hFL : finrank F L ≤ N ^ 2 := by
    rw [← finrank_mul_finrank F M L, sq]
    exact Nat.mul_le_mul hM hL
  set S := kummerPrimes N
  set B := (meetsFinset G).image (fun u : FinitePlace F => u.maximalIdeal)
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (mem_kummerPrimes.mp hp).1
  have hSL : ∀ p : ℕ, p.Prime → p ≤ finrank F L → p ∈ S :=
    fun p hp hpL => mem_kummerPrimes.mpr ⟨hp, hpL.trans hFL⟩
  have hB : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 𝔭 ∉ B → (∀ p ∈ S, (p : 𝓞 F) ∉ 𝔭.asIdeal) →
      ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔭.asIdeal (𝓞 L),
        𝔭.asIdeal.ramificationIdx' P = 1 := by
    intro 𝔭 h𝔭B h𝔭S P hP
    obtain ⟨u, rfl⟩ : ∃ u : FinitePlace F, u.maximalIdeal = 𝔭 :=
      ⟨FinitePlace.mk 𝔭, FinitePlace.maximalIdeal_mk 𝔭⟩
    haveI := u.maximalIdeal.isMaximal
    obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP
    have hu : u ∉ meets G := fun hu => h𝔭B (Finset.mem_image_of_mem _
      (by rw [meetsFinset, Set.Finite.mem_toFinset]; exact hu))
    obtain ⟨hc, hc'⟩ := hG u hu
    obtain ⟨p, hp, hpu⟩ := exists_prime_natCast_mem u.maximalIdeal.asIdeal u.maximalIdeal.ne_bot
    have hpN : N < p := by
      by_contra hle
      have hpS : p ∈ S := mem_kummerPrimes.mpr ⟨hp, (not_lt.mp hle).trans
        (Nat.le_self_pow two_ne_zero N)⟩
      exact h𝔭S p hpS hpu
    have hNu : (N : 𝓞 F) ∉ u.maximalIdeal.asIdeal :=
      natCast_notMem_of_not_dvd hp hpu (Nat.not_dvd_of_pos_of_lt hN hpN)
    exact ramificationIdx'_eq_one_of_kummer M hN ha hb haM hbL u hc hc' hNu P
  refine (log_absNorm_differentIdeal_div_le L S hS hSL B hB).trans (add_le_add ?_ ?_)
  · -- the places meeting `G`
    rw [cond_eq_sum]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc ∑ 𝔭 ∈ B with ∀ p ∈ S, (p : 𝓞 F) ∉ 𝔭.asIdeal, Real.log (Ideal.absNorm 𝔭.asIdeal)
        ≤ ∑ 𝔭 ∈ B, Real.log (Ideal.absNorm 𝔭.asIdeal) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => log_absNorm_nonneg _
      _ = ∑ w ∈ meetsFinset G, Real.log (placeNorm w) :=
          Finset.sum_image fun _ _ _ _ h => (FinitePlace.maximalIdeal_inj _ _).mp h
  · -- the primes `≤ N²`
    refine Finset.sum_le_sum fun p _ => add_le_add le_rfl ?_
    have hpos : (0 : ℝ) < finrank F L := by exact_mod_cast finrank_pos
    rcases Nat.eq_zero_or_pos N with rfl | hN'
    · omega
    calc Real.log (finrank F L) ≤ Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log hpos (by exact_mod_cast hFL)
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num

/-- **(W7b) with the tower formula**: `logDisc L ≤ logDisc F + cond G + kummerConst N`. -/
theorem logDisc_le_logDisc_add_cond_add {N : ℕ} (hN : 0 < N) {c : F} {a : M} {b : L}
    (ha : a ^ N = algebraMap F M c) (hb : b ^ N = 1 - algebraMap F L c)
    (haM : Algebra.adjoin F {a} = ⊤) (hbL : Algebra.adjoin M {b} = ⊤) (G : Finset F)
    (hG : ∀ u : FinitePlace F, u ∉ meets G → u c = 1 ∧ u (1 - c) = 1) :
    logDisc L ≤ logDisc F + cond G + kummerConst N := by
  have h1 := log_absNorm_differentIdeal_div_le_cond_add M hN ha hb haM hbL G hG
  have h2 := logDisc_eq_add F L
  linarith

end Bound

/-! ### The version with `L = F⟮a, b⟯` -/

section Adjoin

variable {F : Type*} [Field F] [NumberField F] {L : Type*} [Field L] [NumberField L]
  [Algebra F L]

/-- For `a, b ∈ L` with `F⟮a, b⟯ = L`: `F⟮a⟯[gen] = F⟮a⟯` and `F⟮a⟯[b] = L`. -/
lemma adjoin_pair_eq_top {a b : L} (hab : IntermediateField.adjoin F {a, b} = ⊤) :
    Algebra.adjoin F {IntermediateField.AdjoinSimple.gen F a} = ⊤ ∧
      Algebra.adjoin (IntermediateField.adjoin F {a}) {b} = ⊤ := by
  have hai : IsIntegral F a := IsIntegral.of_finite F a
  refine ⟨?_, ?_⟩
  · rw [← IntermediateField.adjoin.powerBasis_gen hai]
    exact (IntermediateField.adjoin.powerBasis hai).adjoin_gen_eq_top
  · have hb : IntermediateField.adjoin (IntermediateField.adjoin F {a}) {b} = ⊤ := by
      rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
        IntermediateField.adjoin_simple_adjoin_simple]
      exact hab
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.of_finite _ b).isAlgebraic, hb, IntermediateField.top_toSubalgebra]

/-- **(W7b) for `L = F⟮a, b⟯`**: if `a^N = c`, `b^N = 1 − c` with `N ≥ 1` and `F⟮a, b⟯ = L`,
and `c`, `1 − c` are units at every finite place of `F` not meeting `G`, then
`log N(𝔇_{L/F})/[L : ℚ] ≤ cond G + kummerConst N`. -/
theorem log_absNorm_differentIdeal_div_le_cond_add_of_adjoin {N : ℕ} (hN : 0 < N) {c : F}
    {a b : L} (ha : a ^ N = algebraMap F L c) (hb : b ^ N = 1 - algebraMap F L c)
    (hab : IntermediateField.adjoin F {a, b} = ⊤) (G : Finset F)
    (hG : ∀ u : FinitePlace F, u ∉ meets G → u c = 1 ∧ u (1 - c) = 1) :
    Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L ≤
      cond G + kummerConst N := by
  obtain ⟨h1, h2⟩ := adjoin_pair_eq_top hab
  refine log_absNorm_differentIdeal_div_le_cond_add (IntermediateField.adjoin F {a}) hN
    (a := IntermediateField.AdjoinSimple.gen F a) ?_ hb h1 h2 G hG
  apply Subtype.ext
  simpa using ha

/-- **(W7b) for `L = F⟮a, b⟯`, with the tower formula**:
`logDisc L ≤ logDisc F + cond G + kummerConst N`. -/
theorem logDisc_le_logDisc_add_cond_add_of_adjoin {N : ℕ} (hN : 0 < N) {c : F} {a b : L}
    (ha : a ^ N = algebraMap F L c) (hb : b ^ N = 1 - algebraMap F L c)
    (hab : IntermediateField.adjoin F {a, b} = ⊤) (G : Finset F)
    (hG : ∀ u : FinitePlace F, u ∉ meets G → u c = 1 ∧ u (1 - c) = 1) :
    logDisc L ≤ logDisc F + cond G + kummerConst N := by
  have h1 := log_absNorm_differentIdeal_div_le_cond_add_of_adjoin hN ha hb hab G hG
  have h2 := logDisc_eq_add F L
  linarith

end Adjoin

end Heights.Different
