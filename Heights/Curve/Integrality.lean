/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Heights.Curve.TupleHeight
import Heights.Absolute.Northcott
import Heights.Absolute.RootBound

/-!
# Comparison of heights of tuples: the integrality argument

For tuples `s`, `t` of functions on a curve with `A_s ≤ A_t` (i.e. `min_i ord_P(s_i) ≥
min_j ord_P(t_j)` at every place `P`), the heights satisfy `h_s ≲ h_t`: there is a constant
`C` with `tupleHeight s x ≤ tupleHeight t x + C` for all algebraic points `x`
(`Heights.Curve.tupleHeight_le_of_minOrd_le`). In particular tuples with the same divisor
`A_s = A_t` have heights differing by a bounded amount: the BD-class of `h_s` only depends on
the divisor `A_s`, which is the content of [GenEll], Proposition 1.4 (iii) for curves.

## The argument

For `j` with `t_j ≠ 0`, every quotient `s_i / t_j` lies in every valuation subring of `K`
containing the `ℚ`-algebra `ℚ[t_l / t_j]` (such a subring is `K` or a place `P` at which
`t_j` has minimal order among the `t_l`, hence `ord_P(s_i) ≥ ord_P(t_j)`); so `s_i / t_j` is
integral over `ℚ[t_l / t_j]` (`iInf_valuationSubring_superset`) and satisfies a monic equation
whose coefficients are polynomials with rational coefficients in the `t_l / t_j`. At an
algebraic point `x` and a place `w` of its field of definition, choose `j` so that
`|t_j(x)|_w` is maximal (after normalising); then all `|(t_l/t_j)(x)|_w ≤ 1`, and the root
bounds give `|(s_i/t_j)(x)|_w ≤ C_w` with `C_w` depending only on the absolute values of the
finitely many rational coefficients at `w` (and on their number at the archimedean places).
Summing over the places, the constants add up to `∑ h(q)` over the rational coefficients plus
a logarithmic term. The finitely many points lying over places where `A_s < A_t` are treated
separately.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute NumberField Polynomial
open scoped Classical

/-! ### Elementary bounds -/

section RootBound

variable {F : Type*} [Field F] (w : AbsoluteValue F ℝ)

/-- A product of reals `≥ 1` is `≥ 1`. -/
theorem one_le_prod_of_one_le {α : Type*} (s : Finset α) {f : α → ℝ} (hf : ∀ a ∈ s, 1 ≤ f a) :
    1 ≤ ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    nlinarith

/-- A factor `≥ 1` of a product of reals `≥ 1` is at most the product. -/
theorem le_prod_of_one_le {α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ a ∈ s, 1 ≤ f a)
    {a : α} (ha : a ∈ s) : f a ≤ ∏ b ∈ s, f b := by
  rw [← Finset.mul_prod_erase s f ha]
  have := one_le_prod_of_one_le (s.erase a) fun b hb => hf b (Finset.mem_of_mem_erase hb)
  have h0 : 0 ≤ f a := zero_le_one.trans (hf a ha)
  nlinarith

/-- The polynomial `X^n + ∑_{k<n} c_k X^k`. -/
noncomputable def monicOf (n : ℕ) (c : ℕ → F) : F[X] :=
  X ^ n + ∑ k ∈ Finset.range n, C (c k) * X ^ k

theorem degree_sum_lt (n : ℕ) (c : ℕ → F) :
    (∑ k ∈ Finset.range n, C (c k) * X ^ k).degree < (n : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro k hk
  exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.mp hk)

theorem monicOf_monic (n : ℕ) (c : ℕ → F) : (monicOf n c).Monic := by
  unfold monicOf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact monic_X_pow_add (degree_sum_lt n c)

theorem natDegree_monicOf (n : ℕ) (c : ℕ → F) : (monicOf n c).natDegree = n := by
  unfold monicOf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [natDegree_add_eq_left_of_degree_lt] <;> simp only [natDegree_X_pow, degree_X_pow]
  exact degree_sum_lt n c

theorem coeff_monicOf {n : ℕ} (c : ℕ → F) {k : ℕ} (hk : k < n) : (monicOf n c).coeff k = c k := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg hk.ne, zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_range.mpr hk) h

theorem eval_monicOf (n : ℕ) (c : ℕ → F) (z : F) :
    (monicOf n c).eval z = z ^ n + ∑ k ∈ Finset.range n, c k * z ^ k := by
  simp [monicOf, eval_finsetSum]

/-- **Nonarchimedean root bound** for `z^n + ∑_{k<n} c_k z^k = 0`. -/
theorem apply_le_of_eq_nonarch (hw : ∀ a b, w (a + b) ≤ max (w a) (w b)) {n : ℕ} {c : ℕ → F}
    {z : F} (hz : z ^ n + ∑ k ∈ Finset.range n, c k * z ^ k = 0) {B : ℝ} (hB : 1 ≤ B)
    (hc : ∀ k < n, w (c k) ≤ B) : w z ≤ B := by
  rw [← eval_monicOf] at hz
  refine Heights.Absolute.apply_le_of_isNonarchimedean w hw (monicOf_monic n c) hz hB
    fun k hk => ?_
  rw [natDegree_monicOf] at hk
  rw [coeff_monicOf c hk]
  exact hc k hk

/-- **Archimedean root bound** (Cauchy) for `z^n + ∑_{k<n} c_k z^k = 0`. -/
theorem apply_le_of_eq {n : ℕ} {c : ℕ → F} {z : F}
    (hz : z ^ n + ∑ k ∈ Finset.range n, c k * z ^ k = 0) :
    w z ≤ 1 + ∑ k ∈ Finset.range n, w (c k) := by
  rw [← eval_monicOf] at hz
  have := Heights.Absolute.apply_le_one_add_sum w (monicOf_monic n c) hz
  rw [natDegree_monicOf] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [coeff_monicOf c (Finset.mem_range.mp hk)]

end RootBound

/-! ### Bounds for polynomial expressions with rational coefficients -/

section PolyBound

variable {F : Type*} [Field F] [CharZero F] (w : AbsoluteValue F ℝ) {κ : Type*}

/-- `∏_{m ∈ supp Q} max(1, |coeff_m Q|_w)`. -/
noncomputable def coeffBound (Q : MvPolynomial κ ℚ) : ℝ :=
  ∏ m ∈ Q.support, max 1 (w ((Q.coeff m : ℚ) : F))

theorem one_le_coeffBound (Q : MvPolynomial κ ℚ) : 1 ≤ coeffBound w Q :=
  one_le_prod_of_one_le _ fun _ _ => le_max_left _ _

theorem log_coeffBound (Q : MvPolynomial κ ℚ) :
    Real.log (coeffBound w Q) = ∑ m ∈ Q.support, Real.posLog (w ((Q.coeff m : ℚ) : F)) := by
  rw [coeffBound, Real.log_prod (fun m _ => by positivity)]
  exact Finset.sum_congr rfl fun m _ => (Real.posLog_eq_log_max_one (w.nonneg _)).symm

/-- The value of a polynomial with rational coefficients at a point of the closed unit polydisc,
nonarchimedean case. -/
theorem apply_eval₂_le_nonarch (hw : ∀ a b, w (a + b) ≤ max (w a) (w b)) {a : κ → F}
    (ha : ∀ l, w (a l) ≤ 1) (Q : MvPolynomial κ ℚ) :
    w (MvPolynomial.eval₂ (Rat.castHom F) a Q) ≤ coeffBound w Q := by
  rw [MvPolynomial.eval₂_eq]
  refine Heights.Absolute.apply_sum_le_of_isNonarchimedean w hw _ _
    (zero_le_one.trans (one_le_coeffBound w Q)) fun m hm => ?_
  rw [map_mul, map_prod]
  have hprod : ∏ i ∈ m.support, w (a i ^ m i) ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => w.nonneg _) fun i _ => ?_
    rw [map_pow]
    exact pow_le_one₀ (w.nonneg _) (ha i)
  calc w (Rat.castHom F (Q.coeff m)) * ∏ i ∈ m.support, w (a i ^ m i)
      ≤ w (Rat.castHom F (Q.coeff m)) * 1 :=
        mul_le_mul_of_nonneg_left hprod (w.nonneg _)
    _ = w ((Q.coeff m : ℚ) : F) := by simp
    _ ≤ max 1 (w ((Q.coeff m : ℚ) : F)) := le_max_right _ _
    _ ≤ coeffBound w Q := le_prod_of_one_le
          (f := fun m => max 1 (w (((Q.coeff m : ℚ)) : F))) (fun _ _ => le_max_left _ _) hm

/-- The value of a polynomial with rational coefficients at a point of the closed unit polydisc,
general case. -/
theorem apply_eval₂_le {a : κ → F} (ha : ∀ l, w (a l) ≤ 1) (Q : MvPolynomial κ ℚ) :
    w (MvPolynomial.eval₂ (Rat.castHom F) a Q) ≤ Q.support.card * coeffBound w Q := by
  rw [MvPolynomial.eval₂_eq]
  refine (w.sum_le _ _).trans ?_
  have hc : Q.support.card * coeffBound w Q = ∑ _m ∈ Q.support, coeffBound w Q := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hc]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [map_mul, map_prod]
  have hprod : ∏ i ∈ m.support, w (a i ^ m i) ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => w.nonneg _) fun i _ => ?_
    rw [map_pow]
    exact pow_le_one₀ (w.nonneg _) (ha i)
  calc w (Rat.castHom F (Q.coeff m)) * ∏ i ∈ m.support, w (a i ^ m i)
      ≤ w (Rat.castHom F (Q.coeff m)) * 1 :=
        mul_le_mul_of_nonneg_left hprod (w.nonneg _)
    _ = w ((Q.coeff m : ℚ) : F) := by simp
    _ ≤ max 1 (w ((Q.coeff m : ℚ) : F)) := le_max_right _ _
    _ ≤ coeffBound w Q := le_prod_of_one_le
          (f := fun m => max 1 (w (((Q.coeff m : ℚ)) : F))) (fun _ _ => le_max_left _ _) hm

/-- **Local bound for roots of integral equations** with polynomial coefficients, in logarithmic
form: `log |z|_w ≤ ∑_{k,m} log⁺ |q_{k,m}|_w + [w archimedean]·log(1 + N)`. -/
theorem log_apply_le_of_eq {a : κ → F} (ha : ∀ l, w (a l) ≤ 1) {n : ℕ}
    (Q : ℕ → MvPolynomial κ ℚ) {z : F} (hz0 : z ≠ 0)
    (hz : z ^ n + ∑ k ∈ Finset.range n, MvPolynomial.eval₂ (Rat.castHom F) a (Q k) * z ^ k = 0) :
    Real.log (w z) ≤ Real.log (1 + ∑ k ∈ Finset.range n, ((Q k).support.card : ℝ)) +
      ∑ k ∈ Finset.range n, ∑ m ∈ (Q k).support, Real.posLog (w (((Q k).coeff m : ℚ) : F)) := by
  have hwz : 0 < w z := w.pos hz0
  have hB : 1 ≤ ∏ k ∈ Finset.range n, coeffBound w (Q k) :=
    one_le_prod_of_one_le _ fun k _ => one_le_coeffBound w (Q k)
  have h1 := apply_le_of_eq w hz
  have h2 : ∑ k ∈ Finset.range n, w (MvPolynomial.eval₂ (Rat.castHom F) a (Q k)) ≤
      (∑ k ∈ Finset.range n, ((Q k).support.card : ℝ)) *
        ∏ k ∈ Finset.range n, coeffBound w (Q k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => (apply_eval₂_le w ha (Q k)).trans ?_
    exact mul_le_mul_of_nonneg_left (le_prod_of_one_le (fun k _ => one_le_coeffBound w (Q k)) hk)
      (Nat.cast_nonneg _)
  have hN : 0 ≤ ∑ k ∈ Finset.range n, ((Q k).support.card : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have h3 : w z ≤ (1 + ∑ k ∈ Finset.range n, ((Q k).support.card : ℝ)) *
      ∏ k ∈ Finset.range n, coeffBound w (Q k) := by
    nlinarith
  have h4 := Real.log_le_log hwz h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_prod (fun k _ => by
    have := one_le_coeffBound w (Q k); positivity)] at h4
  simpa only [log_coeffBound] using h4

/-- Nonarchimedean version: `log |z|_w ≤ ∑_{k,m} log⁺ |q_{k,m}|_w`. -/
theorem log_apply_le_of_eq_nonarch (hw : ∀ a b, w (a + b) ≤ max (w a) (w b)) {a : κ → F}
    (ha : ∀ l, w (a l) ≤ 1) {n : ℕ} (Q : ℕ → MvPolynomial κ ℚ) {z : F} (hz0 : z ≠ 0)
    (hz : z ^ n + ∑ k ∈ Finset.range n, MvPolynomial.eval₂ (Rat.castHom F) a (Q k) * z ^ k = 0) :
    Real.log (w z) ≤
      ∑ k ∈ Finset.range n, ∑ m ∈ (Q k).support, Real.posLog (w (((Q k).coeff m : ℚ) : F)) := by
  have hwz : 0 < w z := w.pos hz0
  have hB : 1 ≤ ∏ k ∈ Finset.range n, coeffBound w (Q k) :=
    one_le_prod_of_one_le _ fun k _ => one_le_coeffBound w (Q k)
  have h3 : w z ≤ ∏ k ∈ Finset.range n, coeffBound w (Q k) :=
    apply_le_of_eq_nonarch w hw hz hB fun k hk =>
      (apply_eval₂_le_nonarch w hw ha (Q k)).trans
        (le_prod_of_one_le (fun k _ => one_le_coeffBound w (Q k)) (Finset.mem_range.mpr hk))
  have h4 := Real.log_le_log hwz h3
  rw [Real.log_prod (fun k _ => by have := one_le_coeffBound w (Q k); positivity)] at h4
  simpa only [log_coeffBound] using h4

end PolyBound

/-! ### Integral equations of quotients -/

section Integral

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- If `r` lies in every place containing all the `g l`, then `r` satisfies a monic equation
whose coefficients are polynomials with rational coefficients in the `g l`. -/
theorem exists_integral_eq {κ : Type*} (g : κ → K) (r : K)
    (hr : ∀ P : Place K, (∀ l, g l ∈ P.1) → r ∈ P.1) :
    ∃ n : ℕ, ∃ Q : ℕ → MvPolynomial κ ℚ,
      r ^ n + ∑ k ∈ Finset.range n, MvPolynomial.aeval g (Q k) * r ^ k = 0 := by
  set S : Set K := Set.range (algebraMap ℚ K) ∪ Set.range g with hS
  have hmem : r ∈ (⨅ V : {V : ValuationSubring K // S ⊆ V.toSubring}, V.1.toSubring) := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    by_cases htop : V = ⊤
    · subst htop
      exact trivial
    · have hq : ∀ q : ℚ, (q : K) ∈ V := fun q => hV (Or.inl ⟨q, (eq_ratCast _ q)⟩)
      exact hr ⟨V, htop, hq⟩ fun l => hV (Or.inr ⟨l, rfl⟩)
  rw [iInf_valuationSubring_superset] at hmem
  obtain ⟨p, hpm, hp⟩ : IsIntegral (Subring.closure S) r := hmem
  have hcl : ∀ c : Subring.closure S, ∃ Q : MvPolynomial κ ℚ,
      MvPolynomial.aeval g Q = (c : K) := by
    intro c
    have h1 : (c : K) ∈ (Algebra.adjoin ℚ (Set.range g)).toSubring := by
      rw [Algebra.adjoin_eq_ring_closure]
      exact c.2
    rw [Subalgebra.mem_toSubring, Algebra.adjoin_range_eq_range_aeval] at h1
    exact h1
  choose Q hQ using hcl
  refine ⟨p.natDegree, fun k => Q (p.coeff k), ?_⟩
  have h := hp
  rw [hpm.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at h
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow] at h
  simp only [hQ]
  exact h

end Integral

/-! ### Evaluation of polynomial expressions at points -/

section Evaluation

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- Evaluation at `x` as a ring homomorphism `𝒪_{x} → ℚ(x)`. -/
noncomputable def evalF (x : QbarPoint K) : x.P.1 →+* x.fieldOf :=
  x.residueFieldEquiv.toRingHom.comp x.P.residue

theorem coe_evalF (x : QbarPoint K) (f : x.P.1) : ((evalF x f : x.fieldOf) : Qbar) =
    x.eval f.1 f.2 := rfl

theorem evalF_comp_ratHom (x : QbarPoint K) :
    (evalF x).comp x.P.ratHom = Rat.castHom x.fieldOf := RingHom.ext_rat _ _

/-- Polynomial expressions in functions regular at `x` are regular at `x`, and evaluation
commutes with them. -/
theorem aeval_mem_and_evalF {κ : Type*} (x : QbarPoint K) (g : κ → K) (hg : ∀ l, g l ∈ x.P.1)
    (Q : MvPolynomial κ ℚ) : ∃ h : MvPolynomial.aeval g Q ∈ x.P.1,
      evalF x ⟨_, h⟩ = MvPolynomial.eval₂ (Rat.castHom x.fieldOf)
        (fun l => evalF x ⟨g l, hg l⟩) Q := by
  set g' : κ → x.P.1 := fun l => ⟨g l, hg l⟩
  set e := MvPolynomial.eval₂ x.P.ratHom g' Q with he
  have hcoe : (e : K) = MvPolynomial.aeval g Q := by
    have := MvPolynomial.eval₂_comp_left x.P.1.subtype x.P.ratHom g' Q
    rw [MvPolynomial.aeval_def]
    have h1 : x.P.1.subtype.comp x.P.ratHom = algebraMap ℚ K := RingHom.ext_rat _ _
    rw [h1] at this
    exact this
  refine ⟨hcoe ▸ e.2, ?_⟩
  have h2 : (⟨MvPolynomial.aeval g Q, hcoe ▸ e.2⟩ : x.P.1) = e := Subtype.ext hcoe.symm
  rw [h2, he, MvPolynomial.eval₂_comp_left, evalF_comp_ratHom]
  rfl

end Evaluation

/-! ### From local to global bounds -/

section LocalGlobal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Finitely many finite places see a nonzero tuple with maximum `≠ 1`. -/
theorem hasFiniteSupport_log_iSup (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F]
    {y : ι → F} (hy : y ≠ 0) :
    (fun v : FinitePlace F => Real.log (⨆ i, v (y i))).HasFiniteSupport := by
  have hfin : ∀ i, y i ≠ 0 → {v : FinitePlace F | v (y i) ≠ 1}.Finite := fun i hi =>
    FinitePlace.hasFiniteMulSupport hi
  refine (Set.Finite.biUnion (Set.finite_univ.inter_of_left {i | y i ≠ 0})
    fun i hi => hfin i hi.2).subset fun v hv => ?_
  simp only [Function.mem_support, ne_eq] at hv
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq,
    exists_prop]
  by_contra hall
  push Not at hall
  apply hv
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  haveI : Nonempty ι := ⟨i₀⟩
  have hsup : (⨆ i, v (y i)) = 1 := by
    apply le_antisymm
    · refine ciSup_le fun i => ?_
      rcases eq_or_ne (y i) 0 with h | h
      · rw [h, map_zero]
        exact zero_le_one
      · exact (hall i h).le
    · exact le_ciSup_of_le (Finite.bddAbove_range _) i₀ (hall i₀ hi₀).ge
  rw [hsup, Real.log_one]

theorem hasFiniteSupport_posLog (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] (b : F) :
    (fun v : FinitePlace F => Real.posLog (v b)).HasFiniteSupport := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [Function.HasFiniteSupport]
  refine (FinitePlace.hasFiniteMulSupport hb).subset fun v hv => ?_
  simp only [Function.mem_support, ne_eq] at hv
  simp only [Function.mem_mulSupport, ne_eq]
  intro h1
  rw [h1] at hv
  simp at hv

/-- **Local-to-global**: if at every place `|y|_w ≤ e^{c_w} |z|_w` with
`c_w = [w | ∞]·c + ∑_τ log⁺ |q_τ|_w` for finitely many rationals `q_τ`, then
`h(y) ≤ h(z) + c + ∑_τ h(q_τ)`. -/
theorem logHeight_le_of_forall_place (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F]
    {y : ι → F} {z : κ → F} (hy : y ≠ 0) (hz : z ≠ 0) (c : ℝ) {T : Type*} (U : Finset T)
    (q : T → ℚ)
    (hinf : ∀ w : InfinitePlace F, Real.log (⨆ i, w (y i)) ≤
      Real.log (⨆ l, w (z l)) + c + ∑ τ ∈ U, Real.posLog (w (q τ : F)))
    (hfin : ∀ v : FinitePlace F, Real.log (⨆ i, v (y i)) ≤
      Real.log (⨆ l, v (z l)) + ∑ τ ∈ U, Real.posLog (v (q τ : F))) :
    logHeight (fun i => (y i : Qbar)) ≤ logHeight (fun l => (z l : Qbar)) + c +
      ∑ τ ∈ U, Height.logHeight₁ (q τ) := by
  have hF : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  have hy' := finrank_mul_logHeight_eq_sum F hy
  have hz' := finrank_mul_logHeight_eq_sum F hz
  -- the heights of the rationals
  have hq : ∀ τ, (Module.finrank ℚ F : ℝ) * Height.logHeight₁ (q τ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.posLog (w (q τ : F)) +
        ∑ᶠ v : FinitePlace F, Real.posLog (v (q τ : F)) := by
    intro τ
    have := finrank_mul_logHeight_one_comp_ringHom_eq_sum (F.val : F →+* Qbar) (q τ : F)
    have h2 : (F.val : F →+* Qbar) (q τ : F) = algebraMap ℚ Qbar (q τ) := by simp
    rw [← this, h2, logHeight_one_ratCast]
  -- infinite places
  have hsumw : ∑ w : InfinitePlace F, (w.mult : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  have hinfsum : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (⨆ i, w (y i)) ≤
      ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (⨆ l, w (z l)) +
        (Module.finrank ℚ F : ℝ) * c +
        ∑ τ ∈ U, ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.posLog (w (q τ : F)) := by
    rw [Finset.sum_comm, ← hsumw, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have := mul_le_mul_of_nonneg_left (hinf w) (Nat.cast_nonneg w.mult)
    calc (w.mult : ℝ) * Real.log (⨆ i, w (y i)) ≤ (w.mult : ℝ) * (Real.log (⨆ l, w (z l)) + c +
          ∑ τ ∈ U, Real.posLog (w (q τ : F))) := this
      _ = _ := by rw [mul_add, mul_add, Finset.mul_sum]
  -- finite places
  have hfinsum : ∑ᶠ v : FinitePlace F, Real.log (⨆ i, v (y i)) ≤
      ∑ᶠ v : FinitePlace F, Real.log (⨆ l, v (z l)) +
        ∑ τ ∈ U, ∑ᶠ v : FinitePlace F, Real.posLog (v (q τ : F)) := by
    rw [← finsum_sum_comm U (fun (v : FinitePlace F) (τ : T) => Real.posLog (v (q τ : F)))
      (fun τ _ => hasFiniteSupport_posLog F _)]
    rw [← finsum_add_distrib (hasFiniteSupport_log_iSup F hz)]
    · refine finsum_le_finsum' (hasFiniteSupport_log_iSup F hy) ?_ fun v => hfin v
      exact (hasFiniteSupport_log_iSup F hz).add
        (Function.HasFiniteSupport.sum (fun τ => hasFiniteSupport_posLog F _) U)
    · exact Function.HasFiniteSupport.sum (fun τ => hasFiniteSupport_posLog F _) U
  have htot : (Module.finrank ℚ F : ℝ) * logHeight (fun i => (y i : Qbar)) ≤
      (Module.finrank ℚ F : ℝ) * (logHeight (fun l => (z l : Qbar)) + c +
        ∑ τ ∈ U, Height.logHeight₁ (q τ)) := by
    rw [mul_add, mul_add, hy', hz', Finset.mul_sum]
    simp only [hq, Finset.sum_add_distrib]
    linarith
  exact le_of_mul_le_mul_left htot hF

end LocalGlobal

end Heights.Curve
