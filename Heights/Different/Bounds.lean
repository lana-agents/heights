/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Heights.Different.NumberField
import Heights.Different.SerreBound

/-!
# Bounds on the local contributions to the different of an extension of number fields

For number fields `F ⊆ L`, `𝔇 = 𝔇_{𝓞 L/𝓞 F}` and a nonzero prime `𝔭` of `F` over the
rational prime `p`, writing `e = e(P|𝔭)`, `f = f(P|𝔭)` for the primes `P ∣ 𝔭`:

* (a) `sum_le_diffContrib`: `∑_{P ∣ 𝔭} (e − 1)·f·log N(𝔭)/[L : ℚ] ≤ diffContrib L 𝔭`
  (Mathlib's `pow_sub_one_dvd_differentIdeal`);
* (b) `diffContrib_eq_zero_of_unramified`: `diffContrib L 𝔭 = 0` if `e = 1` for all `P ∣ 𝔭`;
* (c) `diffContrib_le_of_tame`: `diffContrib L 𝔭 ≤ log N(𝔭)/[F : ℚ]` if `e ∉ 𝔭`
  (i.e. `p ∤ e`) for all `P ∣ 𝔭`, since then `ord_P(𝔇) = e − 1` (Serre's bound with
  `κ = 0`);
* (d) `sum_diffContrib_le_of_mem`: `∑_{𝔭 ∣ p} diffContrib L 𝔭 ≤ (1 + log_p [L : F])·log p
  ≤ log p + log [L : F]`, from Serre's bound `ord_P(𝔇) ≤ e − 1 + e(P|p)·v_p(e)` and
  `∑_{𝔭 ∣ p} e(𝔭|p) f(𝔭|p) = [F : ℚ]`, `∑_{P ∣ 𝔭} e f = [L : F]`;
* `log_absNorm_differentIdeal_div_le`: for a finite set `S` of rational primes containing
  all primes `≤ [L : F]` and a finite set `B` of primes of `F` such that every prime not in
  `B` and not over `S` is unramified in `L`,
  `log N(𝔇)/[L : ℚ] ≤ (∑_{𝔭 ∈ B, p_𝔭 ∉ S} log N(𝔭))/[F : ℚ] + ∑_{p ∈ S} (log p + log [L : F])`.
-/

namespace Heights.Different

open NumberField Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ### Elementary facts on primes of a number field over a rational prime -/

section Base

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
/-- For a rational prime `p ∈ 𝔭`, the prime of `ℤ` below `𝔭` is `pℤ`. -/
lemma comap_int_eq_span {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {p : ℕ} (hp : p.Prime)
    (hp𝔭 : (p : 𝓞 F) ∈ 𝔭) : 𝔭.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)} := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ((Int.ideal_span_isMaximal_of_prime p).eq_of_le (Ideal.IsPrime.comap _).ne_top ?_).symm
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact hp𝔭

omit [NumberField F] in
lemma liesOver_span_of_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {p : ℕ} (hp : p.Prime)
    (hp𝔭 : (p : 𝓞 F) ∈ 𝔭) : 𝔭.LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨(comap_int_eq_span hp hp𝔭).symm⟩

omit [NumberField F] in
/-- `(r : 𝓞 F) ∉ 𝔭` if `p ∤ r`, for a rational prime `p ∈ 𝔭`. -/
lemma natCast_notMem_of_not_dvd {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {p : ℕ} (hp : p.Prime)
    (hp𝔭 : (p : 𝓞 F) ∈ 𝔭) {r : ℕ} (hpr : ¬ p ∣ r) : (r : 𝓞 F) ∉ 𝔭 := by
  intro hmem
  apply hpr
  have h1 : (r : ℤ) ∈ 𝔭.comap (algebraMap ℤ (𝓞 F)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hmem
  rw [comap_int_eq_span hp hp𝔭, Ideal.mem_span_singleton] at h1
  exact Int.natCast_dvd_natCast.mp h1

/-- Every nonzero prime of `𝓞 F` contains a rational prime (its residue characteristic). -/
lemma exists_prime_natCast_mem (𝔭 : Ideal (𝓞 F)) [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 F) ∈ 𝔭 := by
  letI := Ideal.Quotient.field 𝔭
  haveI : Finite (𝓞 F ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot _ h𝔭
  refine ⟨ringChar (𝓞 F ⧸ 𝔭), CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

/-- `p ∈ 𝔭^{e₀} ∖ 𝔭^{e₀+1}` for `e₀ = e(𝔭|p)`. -/
lemma natCast_mem_pow_ramificationIdx' {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {p : ℕ} (hp : p.Prime)
    (h𝔭 : 𝔭 ≠ ⊥) :
    (p : 𝓞 F) ∈ 𝔭 ^ (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 ∧
      (p : 𝓞 F) ∉ 𝔭 ^ ((Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 + 1) := by
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : 𝓞 F)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have he := Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity (p := Ideal.span {(p : ℤ)})
    (P := 𝔭) (hmap ▸ hne) inferInstance
  rw [hmap] at he
  rw [← Ideal.dvd_span_singleton, ← Ideal.dvd_span_singleton,
    pow_dvd_iff_le_multiplicity h𝔭 hne, pow_dvd_iff_le_multiplicity h𝔭 hne, he]
  omega

/-- `a^m ∉ 𝔓^{em+1}` for `a ∈ 𝔓^e ∖ 𝔓^{e+1}`, `𝔓` a nonzero prime of a Dedekind domain. -/
lemma pow_notMem_pow_mul_succ {R : Type*} [CommRing R] [IsDedekindDomain R] (𝔓 : Ideal R)
    [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥) {a : R} {e : ℕ} (ha : a ∈ 𝔓 ^ e) (ha' : a ∉ 𝔓 ^ (e + 1))
    (m : ℕ) : a ^ m ∉ 𝔓 ^ (e * m + 1) := by
  intro h
  have hprime : Prime 𝔓 := Ideal.prime_of_isPrime h𝔓 inferInstance
  obtain ⟨𝔞, h𝔞⟩ : 𝔓 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
  have h1 : 𝔓 ^ (e * m + 1) ∣ Ideal.span {a} ^ m := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_span_singleton.mpr h
  rw [h𝔞, mul_pow, pow_succ, ← pow_mul] at h1
  have h2 : 𝔓 ∣ 𝔞 ^ m := (mul_dvd_mul_iff_left (pow_ne_zero _ h𝔓)).mp h1
  have h3 : 𝔓 ∣ 𝔞 := hprime.dvd_of_dvd_pow h2
  apply ha'
  rw [← Ideal.dvd_span_singleton, h𝔞, pow_succ]
  exact mul_dvd_mul_left _ h3

/-- `p ∤ e / p^{v_p(e)}`. -/
lemma not_dvd_of_pow_padicValNat_mul {p e r : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hr : e = p ^ padicValNat p e * r) : ¬ p ∣ r := by
  intro hdvd
  apply pow_succ_padicValNat_not_dvd (p := p) he
  calc p ^ (padicValNat p e + 1) = p ^ padicValNat p e * p := pow_succ _ _
    _ ∣ p ^ padicValNat p e * r := mul_dvd_mul_left _ hdvd
    _ = e := hr.symm

/-- `(e : 𝓞 F) ∉ 𝔭^{e₀·v_p(e) + 1}` for `e ≠ 0`, `e₀ = e(𝔭|p)`. -/
lemma natCast_notMem_pow_mul_padicValNat {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp𝔭 : (p : 𝓞 F) ∈ 𝔭) {e : ℕ} (he : e ≠ 0) :
    (e : 𝓞 F) ∉
      𝔭 ^ ((Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 * padicValNat p e + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpmem, hpnot⟩ := natCast_mem_pow_ramificationIdx' (𝔭 := 𝔭) hp h𝔭
  obtain ⟨r, hr⟩ : p ^ padicValNat p e ∣ e := pow_padicValNat_dvd
  have hr' := natCast_notMem_of_not_dvd hp hp𝔭 (not_dvd_of_pow_padicValNat_mul he hr)
  intro hmem
  have hmem' : (r : 𝓞 F) * (p : 𝓞 F) ^ padicValNat p e ∈
      𝔭 ^ ((Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 * padicValNat p e + 1) := by
    rw [mul_comm (r : 𝓞 F), ← Nat.cast_pow, ← Nat.cast_mul, ← hr]
    exact hmem
  exact pow_notMem_pow_mul_succ 𝔭 h𝔭 hpmem hpnot _
    (Serre.mem_pow_of_mul_mem_pow 𝔭 hr' _ hmem')

end Base

/-! ### Bounds on the multiplicity of a prime in the different -/

section Prime

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) (P : Ideal (𝓞 L)) [P.IsPrime]
  [P.LiesOver 𝔭]

include h𝔭

omit [NumberField F] [NumberField L] [𝔭.IsMaximal] [P.IsPrime] in
lemma ne_bot_of_liesOver : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P

omit [P.IsPrime] in
/-- `log N(P) = f(P|𝔭)·log N(𝔭)`. -/
lemma log_absNorm_eq_inertiaDeg_mul :
    Real.log (Ideal.absNorm P) = 𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭 inferInstance h𝔭, Nat.cast_pow,
    Real.log_pow]

omit h𝔭 [NumberField F] [𝔭.IsMaximal] [P.IsPrime] [P.LiesOver 𝔭] in
lemma pow_ramificationIdx'_dvd :
    P ^ 𝔭.ramificationIdx' P ∣ 𝔭.map (algebraMap (𝓞 F) (𝓞 L)) :=
  Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'

omit [NumberField F] [𝔭.IsMaximal] in
lemma ramificationIdx'_ne_zero' : 𝔭.ramificationIdx' P ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P h𝔭

/-- **(a)** `e(P|𝔭) − 1 ≤ ord_P(𝔇)`. -/
lemma ramificationIdx'_sub_one_le_multiplicity :
    𝔭.ramificationIdx' P - 1 ≤ multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) :=
  (pow_dvd_iff_le_multiplicity (ne_bot_of_liesOver h𝔭 P) differentIdeal_ne_bot).mp
    (pow_sub_one_dvd_differentIdeal (𝓞 F) P _ h𝔭 (pow_ramificationIdx'_dvd P))

/-- **Serre's bound**: `ord_P(𝔇) ≤ e(κ + 1) − 1` if `e = e(P|𝔭) ∉ 𝔭^{κ+1}`. -/
lemma multiplicity_le_of_notMem_pow (κ : ℕ)
    (hκ : ((𝔭.ramificationIdx' P : ℕ) : 𝓞 F) ∉ 𝔭 ^ (κ + 1)) :
    multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) ≤ 𝔭.ramificationIdx' P * (κ + 1) - 1 := by
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (ne_bot_of_liesOver h𝔭 P)
  haveI : Finite (𝓞 F ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot _ h𝔭
  have h := Heights.Serre.not_pow_dvd_differentIdeal 𝔭 P h𝔭 κ hκ
  have he := ramificationIdx'_ne_zero' h𝔭 P
  apply multiplicity_le_of_not_pow_dvd (ne_bot_of_liesOver h𝔭 P) differentIdeal_ne_bot
  rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero he (Nat.succ_ne_zero _)))]

/-- **The tame case**: `ord_P(𝔇) = e − 1` if `e = e(P|𝔭) ∉ 𝔭`. -/
lemma multiplicity_eq_of_tame (h : ((𝔭.ramificationIdx' P : ℕ) : 𝓞 F) ∉ 𝔭) :
    multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) = 𝔭.ramificationIdx' P - 1 := by
  refine le_antisymm ?_ (ramificationIdx'_sub_one_le_multiplicity h𝔭 P)
  have := multiplicity_le_of_notMem_pow h𝔭 P 0 (by rwa [zero_add, pow_one])
  rwa [zero_add, mul_one] at this

/-- `e(P|𝔭) ≤ [L : F]`. -/
lemma ramificationIdx'_le_finrank : 𝔭.ramificationIdx' P ≤ finrank F L := by
  classical
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) F L h𝔭
  have hmem : P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L) :=
    (mem_primesOverFinset_iff' h𝔭).mpr ⟨inferInstance, inferInstance⟩
  have hf := Ideal.inertiaDeg'_pos 𝔭 P
  calc 𝔭.ramificationIdx' P ≤ 𝔭.ramificationIdx' P * 𝔭.inertiaDeg' P :=
        Nat.le_mul_of_pos_right _ hf
    _ ≤ _ := Finset.single_le_sum (f := fun P => 𝔭.ramificationIdx' P * 𝔭.inertiaDeg' P)
        (fun _ _ => Nat.zero_le _) hmem
    _ = finrank F L := hsum

/-- **The wild bound at a prime**: `ord_P(𝔇) ≤ e(P|𝔭)·e(𝔭|p)·(1 + log_p [L : F])`. -/
lemma multiplicity_le_wild {p : ℕ} (hp : p.Prime) (hp𝔭 : (p : 𝓞 F) ∈ 𝔭) :
    multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) ≤
      𝔭.ramificationIdx' P * (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 *
        (1 + Nat.log p (finrank F L)) := by
  set e := 𝔭.ramificationIdx' P
  set e₀ := (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭
  have he := ramificationIdx'_ne_zero' h𝔭 P
  have h1 := multiplicity_le_of_notMem_pow h𝔭 P (e₀ * padicValNat p e)
    (natCast_notMem_pow_mul_padicValNat h𝔭 hp hp𝔭 he)
  haveI := liesOver_span_of_mem hp hp𝔭
  haveI : Fact p.Prime := ⟨hp⟩
  have he₀ : e₀ ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver 𝔭
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)
  have hv : padicValNat p e ≤ Nat.log p (finrank F L) :=
    (padicValNat_le_nat_log e).trans (Nat.log_mono_right (ramificationIdx'_le_finrank h𝔭 P))
  have h2 : e * (e₀ * padicValNat p e + 1) - 1 ≤ e * e₀ * (1 + Nat.log p (finrank F L)) := by
    have h3 : e * (e₀ * padicValNat p e + 1) ≤ e * e₀ * (1 + Nat.log p (finrank F L)) := by
      have h4 : e ≤ e * e₀ := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero he₀)
      have h5 : e * e₀ * padicValNat p e ≤ e * e₀ * Nat.log p (finrank F L) :=
        Nat.mul_le_mul_left _ hv
      nlinarith
    omega
  exact h1.trans h2

end Prime

/-! ### Bounds on `diffContrib` -/

section Contrib

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal]

lemma finrank_ℚ_pos (K : Type*) [Field K] [NumberField K] : (0 : ℝ) < finrank ℚ K := by
  exact_mod_cast finrank_pos

/-- The summands of `diffContrib` in terms of `ord_P(𝔇)` and `f(P|𝔭)`. -/
lemma diffContrib_eq (h𝔭 : 𝔭 ≠ ⊥) :
    diffContrib L 𝔭 = ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * 𝔭.inertiaDeg' P *
        Real.log (Ideal.absNorm 𝔭) / finrank ℚ L := by
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  rw [log_absNorm_eq_inertiaDeg_mul h𝔭 P, mul_assoc]

/-- **(a) The lower bound**: `∑_{P ∣ 𝔭} (e − 1)·f·log N(𝔭)/[L : ℚ] ≤ diffContrib L 𝔭`. -/
theorem sum_le_diffContrib (h𝔭 : 𝔭 ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) * 𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) /
        finrank ℚ L ≤ diffContrib L 𝔭 := by
  rw [diffContrib_eq h𝔭]
  refine Finset.sum_le_sum fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ?_ (by positivity)) (log_absNorm_nonneg _)) (by positivity)
  exact_mod_cast ramificationIdx'_sub_one_le_multiplicity h𝔭 P

/-- **(b) Unramified primes do not contribute**: `diffContrib L 𝔭 = 0` if `e(P|𝔭) = 1` for
all `P ∣ 𝔭`. -/
theorem diffContrib_eq_zero_of_unramified (h𝔭 : 𝔭 ≠ ⊥)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L), 𝔭.ramificationIdx' P = 1) :
    diffContrib L 𝔭 = 0 := by
  refine Finset.sum_eq_zero fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  have h1 := h P hP
  have h2 := multiplicity_eq_of_tame h𝔭 P (by
    rw [h1, Nat.cast_one]
    exact (Ideal.ne_top_iff_one 𝔭).mp (Ideal.IsMaximal.ne_top inferInstance))
  rw [h2, h1]
  simp

/-- **(c) The tame bound**: `diffContrib L 𝔭 ≤ log N(𝔭)/[F : ℚ]` if `e(P|𝔭) ∉ 𝔭` for all
`P ∣ 𝔭`. -/
theorem diffContrib_le_of_tame (h𝔭 : 𝔭 ≠ ⊥)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      ((𝔭.ramificationIdx' P : ℕ) : 𝓞 F) ∉ 𝔭) :
    diffContrib L 𝔭 ≤ Real.log (Ideal.absNorm 𝔭) / finrank ℚ F := by
  classical
  rw [diffContrib_eq h𝔭]
  have hlog := log_absNorm_nonneg 𝔭
  calc ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
        (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * 𝔭.inertiaDeg' P *
          Real.log (Ideal.absNorm 𝔭) / finrank ℚ L
      ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
        ((𝔭.ramificationIdx' P * 𝔭.inertiaDeg' P : ℕ) : ℝ) *
          (Real.log (Ideal.absNorm 𝔭) / finrank ℚ L) := by
        refine Finset.sum_le_sum fun P hP => ?_
        obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
        rw [multiplicity_eq_of_tame h𝔭 P (h P hP), mul_div_assoc, Nat.cast_mul]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (div_nonneg hlog (by positivity))
        exact_mod_cast Nat.sub_le _ _
    _ = (finrank F L : ℝ) * (Real.log (Ideal.absNorm 𝔭) / finrank ℚ L) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Ideal.sum_ramification_inertia (𝓞 L) F L h𝔭]
    _ = Real.log (Ideal.absNorm 𝔭) / finrank ℚ F := by
        rw [← finrank_mul_finrank ℚ F L, Nat.cast_mul]
        have := finrank_ℚ_pos F
        have : (0 : ℝ) < finrank F L := by exact_mod_cast finrank_pos
        field_simp

/-- **(c)**, with the residue characteristic: if `p ∈ 𝔭` is a rational prime and
`p ∤ e(P|𝔭)` for all `P ∣ 𝔭`, then `diffContrib L 𝔭 ≤ log N(𝔭)/[F : ℚ]`. -/
theorem diffContrib_le_of_not_dvd (h𝔭 : 𝔭 ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp𝔭 : (p : 𝓞 F) ∈ 𝔭)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L), ¬ p ∣ 𝔭.ramificationIdx' P) :
    diffContrib L 𝔭 ≤ Real.log (Ideal.absNorm 𝔭) / finrank ℚ F :=
  diffContrib_le_of_tame h𝔭 fun P hP => natCast_notMem_of_not_dvd hp hp𝔭 (h P hP)

/-- The wild bound at one prime `𝔭 ∣ p`:
`diffContrib L 𝔭 ≤ e(𝔭|p)·f(𝔭|p)·(1 + log_p [L : F])·log p/[F : ℚ]`. -/
lemma diffContrib_le_wild (h𝔭 : 𝔭 ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp𝔭 : (p : 𝓞 F) ∈ 𝔭) :
    diffContrib L 𝔭 ≤ ((Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 *
      (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 : ℕ) * ((1 + Nat.log p (finrank F L) : ℕ) *
        Real.log p) / finrank ℚ F := by
  classical
  haveI := liesOver_span_of_mem hp hp𝔭
  set e₀ := (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭
  set f₀ := (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭
  set c := 1 + Nat.log p (finrank F L)
  have hN : Real.log (Ideal.absNorm 𝔭) = f₀ * Real.log p := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' 𝔭 hp, Nat.cast_pow, Real.log_pow]
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [diffContrib_eq h𝔭]
  calc ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
        (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * 𝔭.inertiaDeg' P *
          Real.log (Ideal.absNorm 𝔭) / finrank ℚ L
      ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
        ((𝔭.ramificationIdx' P * 𝔭.inertiaDeg' P : ℕ) : ℝ) *
          ((e₀ * f₀ : ℕ) * ((c : ℕ) * Real.log p) / finrank ℚ L) := by
        refine Finset.sum_le_sum fun P hP => ?_
        obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
        have hm : (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) ≤
            (𝔭.ramificationIdx' P * e₀ * c : ℕ) := by
          exact_mod_cast multiplicity_le_wild h𝔭 P hp hp𝔭
        rw [hN]
        push_cast at hm ⊢
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (finrank_ℚ_pos L)]
        have hf : (0 : ℝ) ≤ 𝔭.inertiaDeg' P := by positivity
        have hf₀ : (0 : ℝ) ≤ f₀ := by positivity
        calc (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * 𝔭.inertiaDeg' P *
              (f₀ * Real.log p)
            ≤ (𝔭.ramificationIdx' P * e₀ * c : ℝ) * 𝔭.inertiaDeg' P * (f₀ * Real.log p) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hf)
                (mul_nonneg hf₀ hlogp)
          _ = _ := by ring
    _ = (finrank F L : ℝ) * ((e₀ * f₀ : ℕ) * ((c : ℕ) * Real.log p) / finrank ℚ L) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Ideal.sum_ramification_inertia (𝓞 L) F L h𝔭]
    _ = (e₀ * f₀ : ℕ) * ((c : ℕ) * Real.log p) / finrank ℚ F := by
        rw [← finrank_mul_finrank ℚ F L, Nat.cast_mul (finrank ℚ F)]
        have := finrank_ℚ_pos F
        have : (0 : ℝ) < finrank F L := by exact_mod_cast finrank_pos
        field_simp

end Contrib

/-! ### The wild bound over a rational prime -/

section Wild

variable {F : Type*} [Field F] [NumberField F] (L : Type*) [Field L] [NumberField L]
  [Algebra F L]

/-- **(d) The wild bound**: `∑_{𝔭 ∣ p} diffContrib L 𝔭 ≤ (1 + log_p [L : F])·log p`. -/
theorem sum_diffContrib_le_wild {p : ℕ} (hp : p.Prime) :
    ∑ 𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F), diffContrib L 𝔭 ≤
      (1 + Nat.log p (finrank F L) : ℕ) * Real.log p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Int.ideal_span_isMaximal_of_prime p
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set c := 1 + Nat.log p (finrank F L)
  calc ∑ 𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F), diffContrib L 𝔭
      ≤ ∑ 𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F),
          (((Ideal.span {(p : ℤ)}).ramificationIdx' 𝔭 *
            (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 : ℕ) : ℝ) *
            ((c : ℕ) * Real.log p / finrank ℚ F) := by
        refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
        rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at h𝔭
        obtain ⟨h𝔭p, h𝔭l⟩ := h𝔭
        have h𝔭0 : 𝔭 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 𝔭
        haveI : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal h𝔭p h𝔭0
        have hp𝔭 : (p : 𝓞 F) ∈ 𝔭 := by
          have h : (p : ℤ) ∈ 𝔭.comap (algebraMap ℤ (𝓞 F)) := by
            rw [← Ideal.under_def, ← Ideal.over_def 𝔭 (Ideal.span {(p : ℤ)})]
            exact Ideal.mem_span_singleton_self _
          rwa [Ideal.mem_comap, map_natCast] at h
        rw [mul_div_assoc']
        exact diffContrib_le_wild h𝔭0 hp hp𝔭
    _ = (finrank ℚ F : ℝ) * ((c : ℕ) * Real.log p / finrank ℚ F) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Ideal.sum_ramification_inertia (𝓞 F) ℚ F hp0]
    _ = (c : ℕ) * Real.log p := by
        have := finrank_ℚ_pos F
        field_simp

/-- `(1 + log_p n)·log p ≤ log p + log n` for `n ≠ 0`. -/
lemma one_add_log_mul_log_le {p : ℕ} (hp : 0 < p) {n : ℕ} (hn : n ≠ 0) :
    (1 + Nat.log p n : ℕ) * Real.log p ≤ Real.log p + Real.log n := by
  have h : (Nat.log p n : ℝ) * Real.log p ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos (by exact_mod_cast hp) _)
      (by exact_mod_cast Nat.pow_log_le_self p hn)
  push_cast
  linarith

/-- **(d)**, for any finite set `T` of primes of `F` over `p`:
`∑_{𝔭 ∈ T} diffContrib L 𝔭 ≤ log p + log [L : F]`. -/
theorem sum_diffContrib_le_of_mem {p : ℕ} (hp : p.Prime)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : ∀ 𝔭 ∈ T, (p : 𝓞 F) ∈ 𝔭.asIdeal) :
    ∑ 𝔭 ∈ T, diffContrib L 𝔭.asIdeal ≤ Real.log p + Real.log (finrank F L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Int.ideal_span_isMaximal_of_prime p
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hinj : Set.InjOn (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => 𝔭.asIdeal) T :=
    fun _ _ _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h
  rw [← Finset.sum_image (g := fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => 𝔭.asIdeal)
    (f := diffContrib L) hinj]
  refine le_trans ?_ ((sum_diffContrib_le_wild L hp).trans
    (one_add_log_mul_log_le hp.pos finrank_pos.ne'))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => diffContrib_nonneg _
  intro I hI
  obtain ⟨𝔭, h𝔭, rfl⟩ := Finset.mem_image.mp hI
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0]
  exact ⟨𝔭.isPrime, liesOver_span_of_mem hp (hT 𝔭 h𝔭)⟩

end Wild

/-! ### The global bound -/

section Global

variable {F : Type*} [Field F] [NumberField F] (L : Type*) [Field L] [NumberField L]
  [Algebra F L]

open scoped Classical in
/-- **The bound on the different of `L/F`**: let `S` be a finite set of rational primes
containing every prime `≤ [L : F]` and `B` a finite set of primes of `F` such that every prime
of `F` which is not in `B` and does not lie over `S` is unramified in `L`. Then
`log N(𝔇_{L/F})/[L : ℚ] ≤ (∑_{𝔭 ∈ B, p_𝔭 ∉ S} log N(𝔭))/[F : ℚ] + ∑_{p ∈ S} (log p + log [L : F])`.
Here "`𝔭` lies over `S`" is expressed as `∃ p ∈ S, (p : 𝓞 F) ∈ 𝔭`. -/
theorem log_absNorm_differentIdeal_div_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hSL : ∀ p : ℕ, p.Prime → p ≤ finrank F L → p ∈ S)
    (B : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hB : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F), 𝔭 ∉ B →
      (∀ p ∈ S, (p : 𝓞 F) ∉ 𝔭.asIdeal) →
      ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔭.asIdeal (𝓞 L), 𝔭.asIdeal.ramificationIdx' P = 1) :
    Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L ≤
      (∑ 𝔭 ∈ B with ∀ p ∈ S, (p : 𝓞 F) ∉ 𝔭.asIdeal, Real.log (Ideal.absNorm 𝔭.asIdeal)) /
        finrank ℚ F + ∑ p ∈ S, (Real.log p + Real.log (finrank F L)) := by
  set t := (diffContrib_support_finite (F := F) L).toFinset
  set Q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Prop :=
    fun 𝔭 => ∀ p ∈ S, (p : 𝓞 F) ∉ 𝔭.asIdeal
  set g : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℝ := fun 𝔭 => diffContrib L 𝔭.asIdeal
  have hg : ∀ 𝔭, 0 ≤ g 𝔭 := fun 𝔭 => diffContrib_nonneg _
  rw [log_absNorm_differentIdeal_div_eq_finsum, finsum_eq_sum_of_support_subset g (s := t)
    (by intro 𝔭 h𝔭; rw [Set.Finite.coe_toFinset]; exact h𝔭),
    ← Finset.sum_filter_add_sum_filter_not t Q]
  refine add_le_add ?_ ?_
  · -- the primes not over `S`: tame, and unramified outside `B`
    rw [Finset.sum_div]
    calc ∑ 𝔭 ∈ t.filter Q, g 𝔭
        ≤ ∑ 𝔭 ∈ t.filter Q,
            if 𝔭 ∈ B then Real.log (Ideal.absNorm 𝔭.asIdeal) / finrank ℚ F else 0 := by
          refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
          have hQ : Q 𝔭 := (Finset.mem_filter.mp h𝔭).2
          haveI := 𝔭.isMaximal
          split_ifs with hB𝔭
          · obtain ⟨p, hp, hp𝔭⟩ := exists_prime_natCast_mem 𝔭.asIdeal 𝔭.ne_bot
            have hpS : p ∉ S := fun hpS => hQ p hpS hp𝔭
            have hlt : finrank F L < p := by
              by_contra hle
              exact hpS (hSL p hp (not_lt.mp hle))
            refine diffContrib_le_of_not_dvd 𝔭.ne_bot hp hp𝔭 fun P hP => ?_
            obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' 𝔭.ne_bot).mp hP
            exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero
              (ramificationIdx'_ne_zero' 𝔭.ne_bot P))
              ((ramificationIdx'_le_finrank 𝔭.ne_bot P).trans_lt hlt)
          · exact (diffContrib_eq_zero_of_unramified 𝔭.ne_bot (hB 𝔭 hB𝔭 hQ)).le
      _ = ∑ 𝔭 ∈ (t.filter Q).filter (· ∈ B),
            Real.log (Ideal.absNorm 𝔭.asIdeal) / finrank ℚ F :=
          (Finset.sum_filter _ _).symm
      _ ≤ ∑ 𝔭 ∈ B.filter Q, Real.log (Ideal.absNorm 𝔭.asIdeal) / finrank ℚ F := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun 𝔭 _ _ =>
            div_nonneg (log_absNorm_nonneg _) (by positivity)
          intro 𝔭 h𝔭
          simp only [Finset.mem_filter] at h𝔭 ⊢
          exact ⟨h𝔭.2, h𝔭.1.2⟩
  · -- the primes over `S`: the wild bound
    set u := t.filter (fun 𝔭 => ¬ Q 𝔭)
    calc ∑ 𝔭 ∈ u, g 𝔭
        ≤ ∑ 𝔭 ∈ u, ∑ p ∈ S, if (p : 𝓞 F) ∈ 𝔭.asIdeal then g 𝔭 else 0 := by
          refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
          have hQ : ¬ Q 𝔭 := (Finset.mem_filter.mp h𝔭).2
          simp only [Q, not_forall, not_not] at hQ
          obtain ⟨p, hpS, hp𝔭⟩ := hQ
          calc g 𝔭 = if (p : 𝓞 F) ∈ 𝔭.asIdeal then g 𝔭 else 0 := (if_pos hp𝔭).symm
            _ ≤ _ := Finset.single_le_sum
                (f := fun p : ℕ => if (p : 𝓞 F) ∈ 𝔭.asIdeal then g 𝔭 else 0)
                (fun q _ => by split_ifs; exacts [hg 𝔭, le_rfl]) hpS
      _ = ∑ p ∈ S, ∑ 𝔭 ∈ u, if (p : 𝓞 F) ∈ 𝔭.asIdeal then g 𝔭 else 0 := Finset.sum_comm
      _ = ∑ p ∈ S, ∑ 𝔭 ∈ u.filter (fun 𝔭 => (p : 𝓞 F) ∈ 𝔭.asIdeal), g 𝔭 := by
          simp_rw [Finset.sum_filter]
      _ ≤ ∑ p ∈ S, (Real.log p + Real.log (finrank F L)) :=
          Finset.sum_le_sum fun p hp => sum_diffContrib_le_of_mem L (hS p hp) _
            fun 𝔭 h𝔭 => (Finset.mem_filter.mp h𝔭).2

end Global

end Heights.Different
