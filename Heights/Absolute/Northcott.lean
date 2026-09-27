import Heights.Absolute.Basic

set_option linter.style.header false

/-!
# Northcott's theorem over `ℚ̄`

For every `d : ℕ` and `B : ℝ` there are only finitely many algebraic numbers `a ∈ ℚ̄` with
`[ℚ(a) : ℚ] ≤ d` and absolute logarithmic height `h(a) ≤ B`
(`Heights.Absolute.finite_setOf_finrank_le_logHeight_le`).

The proof bounds the heights of the coefficients of the minimal polynomial: all conjugates of
`a` have height `h(a)` (they are images of `a` under embeddings `ℚ(a) →+* ℚ̄`), and the
coefficients are, up to sign, elementary symmetric functions of the conjugates, whose heights
are controlled by the subadditivity of the height under sums and products.  Mathlib's
Northcott property for `ℚ` (`NumberField.finite_setOf_logHeight₁_le`) then leaves only
finitely many possible minimal polynomials.
-/

namespace Heights.Absolute

open NumberField Module IntermediateField Polynomial
open scoped IntermediateField

/-- The height of the image of `b ∈ L` under an embedding `L →+* ℚ̄`. -/
theorem logHeight_one_comp_ringHom {L : Type*} [Field L] [NumberField L] (φ : L →+* Qbar)
    (b : L) : logHeight ![1, φ b] = Height.logHeight₁ b / finrank ℚ L := by
  have H := logHeight_comp_ringHom φ ![1, b]
  have hfun : (fun i => φ ((![1, b] : Fin 2 → L) i)) = ![1, φ b] := by
    ext i
    fin_cases i <;> simp
  rw [hfun] at H
  rw [H, Height.logHeight_swap, ← Height.logHeight₁_eq_logHeight]

/-- The height of a rational number in `ℚ̄` is its height over `ℚ`. -/
theorem logHeight_one_ratCast (q : ℚ) :
    logHeight ![1, algebraMap ℚ Qbar q] = Height.logHeight₁ q := by
  rw [logHeight_one_comp_ringHom (algebraMap ℚ Qbar) q, finrank_self, Nat.cast_one, div_one]

@[simp]
theorem logHeight_one_one : logHeight ![1, (1 : Qbar)] = 0 := by
  have := logHeight_one_ratCast 1
  rw [map_one, Height.logHeight₁_one] at this
  exact this

/-- Conjugate algebraic numbers have the same height. -/
theorem logHeight_one_of_mem_aroots {a r : Qbar} (hr : r ∈ (minpoly ℚ a).aroots Qbar) :
    logHeight ![1, r] = logHeight ![1, a] := by
  set φ := (algHomAdjoinIntegralEquiv ℚ (isIntegral a)).symm ⟨r, hr⟩
  have hφ : φ (AdjoinSimple.gen ℚ a) = r := algHomAdjoinIntegralEquiv_symm_apply_gen _ _ _
  have := logHeight_one_comp_ringHom φ.toRingHom (AdjoinSimple.gen ℚ a)
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφ] at this
  rw [this, logHeight_one_eq_gen]

/-- `h(∑ S) ≤ ∑_{s ∈ S} h(s) + #S · log 2`. -/
theorem logHeight_one_multiset_sum_le (S : Multiset Qbar) :
    logHeight ![1, S.sum] ≤ (S.map fun s => logHeight ![1, s]).sum +
      Multiset.card S * Real.log 2 := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have := logHeight_one_add_le a S.sum
    push_cast
    linarith

/-- `h(∏ S) ≤ ∑_{s ∈ S} h(s)`. -/
theorem logHeight_one_multiset_prod_le (S : Multiset Qbar) :
    logHeight ![1, S.prod] ≤ (S.map fun s => logHeight ![1, s]).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have := logHeight_one_mul_le a S.prod
    linarith

/-- Height bound for the elementary symmetric functions of elements of height `≤ B`. -/
theorem logHeight_one_esymm_le (S : Multiset Qbar) {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ r ∈ S, logHeight ![1, r] ≤ B) (m : ℕ) :
    logHeight ![1, S.esymm m] ≤
      2 ^ Multiset.card S * (Multiset.card S * B + Real.log 2) := by
  set n := Multiset.card S
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hterm : ∀ t ∈ (S.powersetCard m).map Multiset.prod,
      logHeight ![1, t] ≤ n * B := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp ht
    obtain ⟨hle, -⟩ := Multiset.mem_powersetCard.mp hu
    refine (logHeight_one_multiset_prod_le u).trans ?_
    refine (Multiset.sum_le_card_nsmul _ B fun x hx => ?_).trans ?_
    · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
      exact hS s (Multiset.subset_of_le hle hs)
    · rw [Multiset.card_map, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Multiset.card_le_card hle) hB
  have hcard : (Multiset.card ((S.powersetCard m).map Multiset.prod) : ℝ) ≤ 2 ^ n := by
    rw [Multiset.card_map, Multiset.card_powersetCard]
    exact_mod_cast Nat.choose_le_two_pow n m
  refine (logHeight_one_multiset_sum_le _).trans ?_
  have hsum : ((((S.powersetCard m).map Multiset.prod).map
      fun s => logHeight ![1, s]).sum) ≤
      Multiset.card ((S.powersetCard m).map Multiset.prod) * (n * B) := by
    refine (Multiset.sum_le_card_nsmul _ ((n : ℝ) * B) fun x hx => ?_).trans ?_
    · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
      exact hterm t ht
    · rw [Multiset.card_map, nsmul_eq_mul]
  have hnB : 0 ≤ (n : ℝ) * B + Real.log 2 := by positivity
  calc _ ≤ Multiset.card ((S.powersetCard m).map Multiset.prod) * (n * B) +
        Multiset.card ((S.powersetCard m).map Multiset.prod) * Real.log 2 := by linarith
    _ = Multiset.card ((S.powersetCard m).map Multiset.prod) * (n * B + Real.log 2) := by ring
    _ ≤ 2 ^ n * (n * B + Real.log 2) := mul_le_mul_of_nonneg_right hcard hnB

/-- The coefficients of the minimal polynomial of `a` have height bounded in terms of the
degree and the height of `a`. -/
theorem logHeight₁_coeff_minpoly_le (a : Qbar) {d : ℕ} (hd : finrank ℚ ℚ⟮a⟯ ≤ d) {B : ℝ}
    (hB : logHeight ![1, a] ≤ B) (k : ℕ) :
    Height.logHeight₁ ((minpoly ℚ a).coeff k) ≤ 2 ^ d * (d * max B 0 + Real.log 2) := by
  set p := minpoly ℚ a
  set n := p.natDegree
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hn : n = finrank ℚ ℚ⟮a⟯ := (IntermediateField.adjoin.finrank (isIntegral a)).symm
  have hC : 0 ≤ 2 ^ d * (d * max B 0 + Real.log 2) := by positivity
  rcases lt_or_ge n k with hk | hk
  · rw [coeff_eq_zero_of_natDegree_lt hk, Height.logHeight₁_zero]
    exact hC
  set q := p.map (algebraMap ℚ Qbar)
  have hmonic : q.Monic := (minpoly.monic (isIntegral a)).map _
  have hqn : q.natDegree = n := natDegree_map _
  have hcoeff := coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits q) (k := k) (hqn ▸ hk)
  rw [coeff_map, hmonic.leadingCoeff, one_mul, hqn] at hcoeff
  have hcard : Multiset.card q.roots = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqn]
  have hroots : ∀ r ∈ q.roots, logHeight ![1, r] ≤ max B 0 := fun r hr =>
    (logHeight_one_of_mem_aroots hr).le.trans (hB.trans (le_max_left _ _))
  have hes := logHeight_one_esymm_le q.roots (le_max_right B 0) hroots (n - k)
  rw [hcard] at hes
  have hsign : logHeight ![1, (-1 : Qbar) ^ (n - k) * q.roots.esymm (n - k)] =
      logHeight ![1, q.roots.esymm (n - k)] := by
    rcases neg_one_pow_eq_or Qbar (n - k) with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, neg_one_mul, logHeight_one_neg]
  rw [← logHeight_one_ratCast, hcoeff, hsign]
  refine hes.trans ?_
  have hnd : n ≤ d := hn ▸ hd
  gcongr
  norm_num

/-- **Northcott's theorem over `ℚ̄`**: there are only finitely many algebraic numbers of bounded
degree and bounded height. -/
theorem finite_setOf_finrank_le_logHeight_le (d : ℕ) (B : ℝ) :
    {a : Qbar | finrank ℚ ℚ⟮a⟯ ≤ d ∧ logHeight ![1, a] ≤ B}.Finite := by
  classical
  set C : ℝ := 2 ^ d * (d * max B 0 + Real.log 2)
  set T := {q : ℚ | Height.logHeight₁ q ≤ C}
  have hT : T.Finite := NumberField.finite_setOf_logHeight₁_le ℚ C
  have : Finite T := hT.to_subtype
  set P := {p : ℚ[X] | p.natDegree ≤ d ∧ ∀ k, p.coeff k ∈ T}
  have hP : P.Finite := by
    refine (Set.finite_range fun c : Fin (d + 1) → T =>
      ∑ i : Fin (d + 1), monomial (i : ℕ) (c i : ℚ)).subset ?_
    rintro p ⟨hpd, hpT⟩
    refine ⟨fun i => ⟨p.coeff i, hpT i⟩, ?_⟩
    change ∑ i : Fin (d + 1), monomial (i : ℕ) (p.coeff i) = p
    rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)),
      ← p.as_sum_range' (d + 1) (Nat.lt_succ_of_le hpd)]
  refine (hP.biUnion fun p _ => ((p.aroots Qbar).toFinset.finite_toSet)).subset ?_
  rintro a ⟨hd, hB⟩
  refine Set.mem_biUnion (x := minpoly ℚ a) ⟨?_, fun k => ?_⟩ ?_
  · rw [← IntermediateField.adjoin.finrank (isIntegral a)]
    exact hd
  · exact logHeight₁_coeff_minpoly_le a hd hB k
  · rw [Finset.mem_coe, Multiset.mem_toFinset, mem_aroots]
    exact ⟨minpoly.ne_zero (isIntegral a), minpoly.aeval ℚ a⟩

end Heights.Absolute
