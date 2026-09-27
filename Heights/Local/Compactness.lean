/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Mathlib

/-!
# Sequential compactness of `ℙ¹(ℚ̄_p)^{≤ d}` and of `ℙ¹(ℂ)`

The compactness argument in the proof of [GenEll], Theorem 2.1 (p. 13 of Mochizuki,
*Arithmetic elliptic curves in general position*) uses that the points of bounded degree
of a proper curve over the completions `ℚ_v`, `v ∈ V`, form a compact set. We only need the
following form, for values of functions (i.e. points of `ℙ¹`): a sequence in
`ℚ̄_p = PadicAlgCl p` whose terms have degree at most `d` over `ℚ_p` has a subsequence which
either converges in `ℚ̄_p` or tends to `∞` (`‖·‖ → ∞`); and likewise, with no degree
condition, in any proper normed field such as `ℂ`.

Note that `ℚ̄_p` is not locally compact; the degree bound is essential. The proof: if the
terms are bounded by `1`, the coefficients of their minimal polynomials over `ℚ_p` lie in
`ℤ_p` (the norm of `ℚ̄_p` is the spectral norm, `spectralValue_le_one_iff`), so along a
subsequence the minimal polynomials converge to a monic polynomial `g` of the same degree;
then `g(a_n) → 0`, and since `g = ∏ (X − r_j)` over `ℚ̄_p`, a further subsequence converges
to one of the roots `r_j`. The unbounded case is reduced to the bounded one by inversion.

## Main results

* `Heights.Local.exists_strictMono_eq`: infinite pigeonhole for sequences.
* `Heights.Local.PadicAlgCl.exists_tendsto_of_norm_le_one`: the bounded case.
* `Heights.Local.PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop`: the dichotomy in `ℚ̄_p`.
* `Heights.Local.exists_tendsto_or_tendsto_norm_atTop`: the dichotomy in a proper normed
  field (e.g. `ℂ`).
-/

namespace Heights.Local

open Filter Topology Polynomial

/-- **Infinite pigeonhole**: a sequence with values in a finite type is constant along a
subsequence. -/
theorem exists_strictMono_eq {α : Type*} [Finite α] (f : ℕ → α) :
    ∃ (c : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, f (φ n) = c := by
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber f
  have hinf : (setOf fun n => f n = c).Infinite := Set.infinite_coe_iff.mp hc
  exact ⟨c, Nat.nth (fun n => f n = c), Nat.nth_strictMono hinf,
    fun n => Nat.nth_mem_of_infinite hinf n⟩

/-- A subsequence of the terms satisfying a predicate that holds infinitely often. -/
theorem exists_strictMono_forall_of_infinite {P : ℕ → Prop} (h : (setOf P).Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) :=
  ⟨Nat.nth P, Nat.nth_strictMono h, fun n => Nat.nth_mem_of_infinite h n⟩

/-- Pigeonhole for a sequence of natural numbers bounded by `d`. -/
theorem exists_strictMono_eq_of_le {f : ℕ → ℕ} {d : ℕ} (hf : ∀ n, f n ≤ d) :
    ∃ (c : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, f (φ n) = c := by
  obtain ⟨c, φ, hφ, hc⟩ := exists_strictMono_eq (fun n => (⟨f n, Nat.lt_succ_of_le (hf n)⟩ :
    Fin (d + 1)))
  exact ⟨c, φ, hφ, fun n => congrArg Fin.val (hc n)⟩

/-- If `t n ^ c ≤ ε n` with `t n ≥ 0`, `c ≠ 0` and `ε n → 0`, then `t n → 0`. -/
theorem tendsto_zero_of_pow_le {t ε : ℕ → ℝ} {c : ℕ} (hc : c ≠ 0) (ht : ∀ n, 0 ≤ t n)
    (hle : ∀ n, t n ^ c ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) : Tendsto t atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hε ⊢
  intro δ hδ
  obtain ⟨N, hN⟩ := hε (δ ^ c) (pow_pos hδ c)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ht n)]
  by_contra h2
  push Not at h2
  have : δ ^ c ≤ t n ^ c := pow_le_pow_left₀ hδ.le h2 c
  have h3 : ε n < δ ^ c := lt_of_abs_lt h1
  linarith [hle n]

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The norm of `ℚ̄_p` is the spectral norm. -/
theorem PadicAlgCl.norm_eq_spectralNorm (x : PadicAlgCl p) :
    ‖x‖ = spectralNorm ℚ_[p] (PadicAlgCl p) x := rfl

/-- If `‖x‖ ≤ 1` in `ℚ̄_p`, the coefficients of the minimal polynomial of `x` over `ℚ_p`
are `p`-adic integers. -/
theorem PadicAlgCl.norm_coeff_minpoly_le_one {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (i : ℕ) :
    ‖(minpoly ℚ_[p] x).coeff i‖ ≤ 1 := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  rw [PadicAlgCl.norm_eq_spectralNorm, spectralNorm] at hx
  exact (spectralValue_le_one_iff (minpoly.monic hint)).mp hx i

/-- A monic polynomial written with its coefficients. -/
theorem monic_eq_sum {R : Type*} [CommRing R] {P : R[X]} (hP : P.Monic) :
    P = X ^ P.natDegree + ∑ i : Fin P.natDegree, C (P.coeff i) * X ^ (i : ℕ) := by
  conv_lhs => rw [hP.as_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]

/-- The inverse of an element has the same degree. -/
theorem natDegree_minpoly_inv {K L : Type*} [Field K] [Field L] [Algebra K L] (x : L) :
    (minpoly K x⁻¹).natDegree = (minpoly K x).natDegree := by
  by_cases hx : IsIntegral K x
  · by_cases h0 : x = 0
    · simp [h0]
    have hxi : IsIntegral K x⁻¹ := by
      have := (IsIntegral.isAlgebraic hx).inv
      exact this.isIntegral
    rw [← IntermediateField.adjoin.finrank hx, ← IntermediateField.adjoin.finrank hxi]
    have : IntermediateField.adjoin K {x⁻¹} = IntermediateField.adjoin K {x} := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
        rwa [inv_inv] at this
    rw [this]
  · have hxi : ¬ IsIntegral K x⁻¹ := fun h => by
      have := (IsIntegral.isAlgebraic h).inv
      rw [inv_inv] at this
      exact hx this.isIntegral
    rw [minpoly.eq_zero hx, minpoly.eq_zero hxi]

/-- In an algebraically closed normed field, a monic polynomial `G` of positive degree has a
root `r` with `‖x − r‖ ^ deg G ≤ ‖G(x)‖`. -/
theorem exists_mem_roots_norm_sub_pow_le {K : Type*} [NormedField K] [IsAlgClosed K]
    {G : K[X]} (hG : G.Monic) (hdeg : 0 < G.natDegree) (x : K) :
    ∃ r ∈ G.roots, ‖x - r‖ ^ G.natDegree ≤ ‖G.eval x‖ := by
  have hsplit : G = (G.roots.map fun r => X - C r).prod :=
    (IsAlgClosed.splits G).eq_prod_roots_of_monic hG
  have hcard : G.roots.card = G.natDegree :=
    (IsAlgClosed.splits G).natDegree_eq_card_roots.symm
  have hne : G.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  obtain ⟨r, hr, hmin⟩ := Multiset.exists_min_image (fun r => ‖x - r‖) hne
  refine ⟨r, hr, ?_⟩
  have key : ∀ s : Multiset K, (∀ y ∈ s, ‖x - r‖ ≤ ‖x - y‖) →
      ‖x - r‖ ^ Multiset.card s ≤ ‖((s.map fun r => X - C r).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, Multiset.card_cons,
        pow_succ, mul_comm]
      simp only [eval_sub, eval_X, eval_C]
      exact mul_le_mul (hs a (Multiset.mem_cons_self a s))
        (ih fun y hy => hs y (Multiset.mem_cons_of_mem hy)) (by positivity) (norm_nonneg _)
  have := key G.roots hmin
  rwa [← hsplit, hcard] at this

/-- **The bounded case**: a sequence in the closed unit ball of `ℚ̄_p` whose terms have
degree at most `d` over `ℚ_p` has a convergent subsequence. -/
theorem PadicAlgCl.exists_tendsto_of_norm_le_one (d : ℕ) (a : ℕ → PadicAlgCl p)
    (hdeg : ∀ n, (minpoly ℚ_[p] (a n)).natDegree ≤ d) (hnorm : ∀ n, ‖a n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b, Tendsto (a ∘ φ) atTop (𝓝 b) := by
  classical
  have hint : ∀ x : PadicAlgCl p, IsIntegral ℚ_[p] x :=
    fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  -- constant degree along a subsequence
  obtain ⟨c, φ₁, hφ₁, hc⟩ := exists_strictMono_eq_of_le hdeg
  set a₁ := a ∘ φ₁ with ha₁
  have hc₁ : ∀ n, (minpoly ℚ_[p] (a₁ n)).natDegree = c := hc
  have hcpos : 0 < c := by
    rw [← hc₁ 0]
    exact minpoly.natDegree_pos (hint _)
  -- the coefficient vectors lie in the unit ball
  set v : ℕ → (Fin c → ℚ_[p]) := fun n i => (minpoly ℚ_[p] (a₁ n)).coeff i with hv
  have hvmem : ∀ n, v n ∈ Metric.closedBall (0 : Fin c → ℚ_[p]) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact fun i => PadicAlgCl.norm_coeff_minpoly_le_one (hnorm _) i
  obtain ⟨w, -, ψ, hψ, hw⟩ := (isCompact_closedBall (0 : Fin c → ℚ_[p]) 1).tendsto_subseq hvmem
  set a₂ := a₁ ∘ ψ with ha₂
  -- the limit polynomial
  set g : ℚ_[p][X] := X ^ c + ∑ i : Fin c, C (w i) * X ^ (i : ℕ) with hg
  -- `g(a₂ n) → 0`
  have hgeval : ∀ n, aeval (a₂ n) g =
      ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p) (w i - v (ψ n) i) * (a₂ n) ^ (i : ℕ) := by
    intro n
    have hmin : aeval (a₂ n) (minpoly ℚ_[p] (a₂ n)) = 0 := minpoly.aeval _ _
    have hm := monic_eq_sum (minpoly.monic (hint (a₂ n)))
    have hdn : (minpoly ℚ_[p] (a₂ n)).natDegree = c := hc₁ (ψ n)
    rw [hm] at hmin
    have hmin' : (a₂ n) ^ c + ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p)
        ((minpoly ℚ_[p] (a₂ n)).coeff i) * (a₂ n) ^ (i : ℕ) = 0 := by
      rw [map_add, map_pow, aeval_X, map_sum] at hmin
      simp only [map_mul, aeval_C, map_pow, aeval_X] at hmin
      convert hmin using 2
      · rw [hdn]
      · rw [hdn]
    rw [hg, map_add, map_pow, aeval_X, map_sum]
    simp only [map_mul, aeval_C, map_pow, aeval_X]
    have : ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p) (w i - v (ψ n) i) * a₂ n ^ (i : ℕ) =
        (a₂ n ^ c + ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p) (w i) * a₂ n ^ (i : ℕ)) -
        (a₂ n ^ c + ∑ i : Fin c, algebraMap ℚ_[p] (PadicAlgCl p)
          ((minpoly ℚ_[p] (a₂ n)).coeff i) * a₂ n ^ (i : ℕ)) := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, hv, ha₂, Function.comp_apply]
      ring
    rw [this, hmin', sub_zero]
  have hgto : Tendsto (fun n => ‖aeval (a₂ n) g‖) atTop (𝓝 0) := by
    have hbound : ∀ n, ‖aeval (a₂ n) g‖ ≤ ∑ i : Fin c, ‖w i - v (ψ n) i‖ := by
      intro n
      rw [hgeval n]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_pow, norm_algebraMap']
      have h1 : ‖a₂ n‖ ^ (i : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hnorm _)
      calc ‖w i - v (ψ n) i‖ * ‖a₂ n‖ ^ (i : ℕ) ≤ ‖w i - v (ψ n) i‖ * 1 :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖w i - v (ψ n) i‖ := mul_one _
    have hsum : Tendsto (fun n => ∑ i : Fin c, ‖w i - v (ψ n) i‖) atTop (𝓝 0) := by
      have : (0 : ℝ) = ∑ i : Fin c, ‖w i - w i‖ := by simp
      rw [this]
      refine tendsto_finsetSum _ fun i _ => ?_
      exact ((continuous_apply i).tendsto w |>.comp hw).const_sub (w i) |>.norm
    exact squeeze_zero (fun n => norm_nonneg _) hbound hsum
  -- factor `g` over `ℚ̄_p` and find a nearby root
  have hgmonic : g.Monic := by
    rw [hg]
    refine monic_X_pow_add ?_
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i _
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast i.2
  have hgdeg : g.natDegree = c := by
    rw [hg, natDegree_add_eq_left_of_degree_lt]
    · simp
    · refine (degree_sum_le _ _).trans_lt ?_
      rw [degree_X_pow, Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro i _
      refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
      exact_mod_cast i.2
  set G := g.map (algebraMap ℚ_[p] (PadicAlgCl p)) with hG
  have hGmonic : G.Monic := hgmonic.map _
  have hGdeg : G.natDegree = c := by rw [hG, natDegree_map, hgdeg]
  have hGeval : ∀ n, G.eval (a₂ n) = aeval (a₂ n) g := fun n => by
    rw [hG, eval_map_algebraMap]
  have hnear : ∀ n, ∃ r ∈ G.roots, ‖a₂ n - r‖ ^ c ≤ ‖aeval (a₂ n) g‖ := by
    intro n
    rw [← hGeval n, ← hGdeg]
    exact exists_mem_roots_norm_sub_pow_le hGmonic (hGdeg ▸ hcpos) (a₂ n)
  choose r hrmem hr using hnear
  -- the roots form a finite set: pigeonhole
  set S : Finset (PadicAlgCl p) := G.roots.toFinset
  obtain ⟨r₀, χ, hχ, hr₀⟩ := exists_strictMono_eq (fun n => (⟨r n, by
    simpa [S] using hrmem n⟩ : S))
  refine ⟨φ₁ ∘ ψ ∘ χ, hφ₁.comp (hψ.comp hχ), r₀, ?_⟩
  have hdist : Tendsto (fun n => ‖a₂ (χ n) - r₀‖) atTop (𝓝 0) := by
    refine tendsto_zero_of_pow_le hcpos.ne' (fun n => norm_nonneg _) (fun n => ?_)
      (hgto.comp hχ.tendsto_atTop)
    have := hr (χ n)
    have hrr : r (χ n) = r₀ := congrArg Subtype.val (hr₀ n)
    rw [hrr] at this
    exact this
  have : Tendsto (fun n => a₂ (χ n)) atTop (𝓝 (r₀ : PadicAlgCl p)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hdist
  exact this

/-- **The dichotomy in `ℚ̄_p`**: a sequence in `ℚ̄_p = PadicAlgCl p` whose terms have degree
at most `d` over `ℚ_p` has a subsequence which converges or whose norm tends to `∞`. -/
theorem PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop (d : ℕ) (a : ℕ → PadicAlgCl p)
    (hdeg : ∀ n, (minpoly ℚ_[p] (a n)).natDegree ≤ d) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop) := by
  by_cases h : (setOf fun n => ‖a n‖ ≤ 1).Infinite
  · obtain ⟨φ₁, hφ₁, h1⟩ := exists_strictMono_forall_of_infinite h
    obtain ⟨ψ, hψ, b, hb⟩ :=
      PadicAlgCl.exists_tendsto_of_norm_le_one d (a ∘ φ₁) (fun n => hdeg _) h1
    exact ⟨φ₁ ∘ ψ, hφ₁.comp hψ, Or.inl ⟨b, hb⟩⟩
  · rw [Set.not_infinite] at h
    obtain ⟨N, hN⟩ := h.bddAbove
    have hgt : ∀ n, 1 < ‖a (n + N + 1)‖ := by
      intro n
      by_contra hle
      push Not at hle
      have := hN hle
      omega
    have hne : ∀ n, a (n + N + 1) ≠ 0 := fun n h0 => by
      have := hgt n
      rw [h0, norm_zero] at this
      linarith
    set b : ℕ → PadicAlgCl p := fun n => (a (n + N + 1))⁻¹ with hb
    have hbdeg : ∀ n, (minpoly ℚ_[p] (b n)).natDegree ≤ d := by
      intro n
      rw [hb, natDegree_minpoly_inv]
      exact hdeg _
    have hbnorm : ∀ n, ‖b n‖ ≤ 1 := by
      intro n
      rw [hb, norm_inv]
      exact inv_le_one_of_one_le₀ (hgt n).le
    obtain ⟨ψ, hψ, β, hβ⟩ := PadicAlgCl.exists_tendsto_of_norm_le_one d b hbdeg hbnorm
    have hφ : StrictMono fun n => ψ n + N + 1 := fun m n hmn => by
      have := hψ hmn
      change ψ m + N + 1 < ψ n + N + 1
      omega
    refine ⟨fun n => ψ n + N + 1, hφ, ?_⟩
    by_cases hβ0 : β = 0
    · right
      have h0 : Tendsto (fun n => ‖b (ψ n)‖) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := hβ.norm
          rwa [hβ0, norm_zero] at this
        · exact norm_pos_iff.mpr (inv_ne_zero (hne _))
      have := h0.inv_tendsto_nhdsGT_zero
      refine this.congr fun n => ?_
      simp [hb, norm_inv]
    · left
      refine ⟨β⁻¹, ?_⟩
      have := hβ.inv₀ hβ0
      refine this.congr fun n => ?_
      simp [hb]

end Padic

/-- **The dichotomy in a proper normed field** (e.g. `ℂ`): every sequence has a subsequence
which converges or whose norm tends to `∞`. -/
theorem exists_tendsto_or_tendsto_norm_atTop {K : Type*} [NormedField K] [ProperSpace K]
    (a : ℕ → K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop) := by
  by_cases h : ∃ C : ℝ, (setOf fun n => ‖a n‖ ≤ C).Infinite
  · obtain ⟨C, hC⟩ := h
    obtain ⟨φ₁, hφ₁, h1⟩ := exists_strictMono_forall_of_infinite hC
    have hmem : ∀ n, (a ∘ φ₁) n ∈ Metric.closedBall (0 : K) C := fun n => by
      rw [mem_closedBall_zero_iff]
      exact h1 n
    obtain ⟨b, -, ψ, hψ, hb⟩ := (isCompact_closedBall (0 : K) C).tendsto_subseq hmem
    exact ⟨φ₁ ∘ ψ, hφ₁.comp hψ, Or.inl ⟨b, hb⟩⟩
  · push Not at h
    refine ⟨id, strictMono_id, Or.inr ?_⟩
    rw [tendsto_atTop]
    intro C
    obtain ⟨N, hN⟩ := (h C).bddAbove
    refine eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hN (show n ∈ setOf fun n => ‖a n‖ ≤ C from hlt.le)
    omega

end Heights.Local
