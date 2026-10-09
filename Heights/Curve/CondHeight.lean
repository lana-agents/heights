/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.Integrality
import Heights.Curve.Conductor

/-!
# The log-conductor is bounded by the height ([GenEll], Proposition 1.6)

Let `s : ι → K` be a tuple and `s' = s ∘ e` a subfamily, so that `A_s ≥ A_{s'}`; the
difference `D = A_s − A_{s'}` is effective and `h_s − h_{s'}` is a height for `D`. Let `G` be a
finite set of functions regular off `supp D` (e.g. generators of `𝒪(X ∖ D)`). Then

`log-cond_G(x) ≤ h_s(x) − h_{s'}(x) + C`

for all algebraic points `x` at which the `g ∈ G` are regular
(`Heights.Curve.logCondOf_le_tupleHeight_sub`). This is [GenEll], Proposition 1.6.

The proof is local: at every place `w` of `ℚ(x)`, `log max_{all} |y|_w − log max_{s'} |y|_w ≥ 0`
for the normalised values `y`, and at a finite place `w` where `x` meets `D` (some `|g(x)|_w > 1`)
not above the finitely many primes dividing denominators of the integral equations, the two
maxima differ: if they were equal, an index `j'` of `s'` maximal at `w` would make all
`|(s_l / s'_{j'})(x)|_w ≤ 1`, and the integral equations of the `g ∈ G` over
`ℚ[s_l / s'_{j'}]` would force `|g(x)|_w ≤ 1`. By discreteness of `w`, the maxima then differ by
a factor `≥ N(w)`.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute NumberField
open scoped Classical

/-! ### Discreteness of finite places -/

section Discrete

variable {F : Type*} [Field F] [NumberField F]

/-- Nonzero values of a finite place are integral powers of the norm of its prime. -/
theorem FinitePlace.exists_eq_zpow (w : FinitePlace F) {a : F} (ha : a ≠ 0) :
    ∃ k : ℤ, w a = (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^ k := by
  set v := w.maximalIdeal
  have h1 : w a = HeightOneSpectrum.adicAbv F v a := by
    rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding]
  have hva : v.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  refine ⟨(WithZero.unzero hva).toAdd, ?_⟩
  rw [h1, HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ hva]
  push_cast
  rfl

/-- If `|a|_w > |b|_w` for nonzero `a`, `b`, then `|a|_w ≥ N(w)·|b|_w`. -/
theorem FinitePlace.mul_absNorm_le_of_lt (w : FinitePlace F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : w b < w a) : (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) * w b ≤ w a := by
  obtain ⟨ka, hka⟩ := FinitePlace.exists_eq_zpow w ha
  obtain ⟨kb, hkb⟩ := FinitePlace.exists_eq_zpow w hb
  have hN : (1 : ℝ) < (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal
  set N : ℝ := (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ)
  rw [hka, hkb] at hlt ⊢
  have hk : kb < ka := (zpow_lt_zpow_iff_right₀ hN).mp hlt
  calc N * N ^ kb = N ^ (kb + 1) := by rw [zpow_add_one₀ (by linarith), mul_comm]
    _ ≤ N ^ ka := zpow_le_zpow_right₀ hN.le (by omega)

/-- If `|a|_w > 1` then `|a|_w ≥ N(w)`. -/
theorem FinitePlace.absNorm_le_of_one_lt (w : FinitePlace F) {a : F} (ha : 1 < w a) :
    (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ≤ w a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    linarith
  have := FinitePlace.mul_absNorm_le_of_lt w ha0 one_ne_zero (by rwa [map_one])
  rwa [map_one, mul_one] at this

end Discrete

/-! ### Proposition 1.6 -/

section Prop16

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-- The minimal order of a subfamily is at least that of the family. -/
theorem minOrd_le_minOrd_comp {s : ι → K} (hs : ∃ i, s i ≠ 0) (e : κ → ι)
    (hse : ∃ j, (s ∘ e) j ≠ 0) (P : Place K) : minOrd P s ≤ minOrd P (s ∘ e) := by
  rw [minOrd_eq hse]
  exact minOrd_le hs (normIdx_ne_zero hse)

/-- The finite part of the height of a rational number is at most its height. -/
theorem finsum_posLog_le (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] (q : ℚ) :
    ∑ᶠ v : FinitePlace F, Real.posLog (v (q : F)) ≤
      (Module.finrank ℚ F : ℝ) * Height.logHeight₁ q := by
  have := finrank_mul_logHeight_one_comp_ringHom_eq_sum (F.val : F →+* Qbar) (q : F)
  have h2 : (F.val : F →+* Qbar) (q : F) = algebraMap ℚ Qbar q := by simp
  rw [h2, logHeight_one_ratCast] at this
  rw [this]
  have : 0 ≤ ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.posLog (w (q : F)) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  linarith

theorem hasFiniteSupport_meetsAt (x : QbarPoint K) (G : Finset K) (hG : ∀ g ∈ G, g ∈ x.P.1) :
    (fun w : FinitePlace x.fieldOf => if w ∈ meetsAt x G hG then
      Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0).HasFiniteSupport := by
  refine (Set.Finite.biUnion (s := {g : G | x.eval g.1 (hG g.1 g.2) ≠ 0}) (Set.toFinite _)
    fun g hg => FinitePlace.hasFiniteMulSupport
      (x := (⟨x.eval g.1 (hG g.1 g.2), x.eval_mem_fieldOf _⟩ : x.fieldOf)) (by
        intro h0
        apply hg
        exact congrArg Subtype.val h0)).subset fun w hw => ?_
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hw
  obtain ⟨⟨g, hgG, hg1⟩, -⟩ := hw
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Function.mem_mulSupport, exists_prop]
  refine ⟨⟨g, hgG⟩, fun h0 => ?_, hg1.ne'⟩
  have : (⟨x.eval g (hG g hgG), x.eval_mem_fieldOf _⟩ : x.fieldOf) = 0 := Subtype.ext h0
  rw [this, map_zero] at hg1
  linarith

/-- **[GenEll], Proposition 1.6 (tuple form)**: for a tuple `s` with a subfamily `s ∘ e`, and a
finite set `G` of functions regular wherever `A_s` and `A_{s ∘ e}` agree, the log-conductor with
respect to `G` is bounded by `h_s − h_{s ∘ e}` up to a constant. -/
theorem logCondOf_le_tupleHeight_sub {s : ι → K} (hs : ∃ i, s i ≠ 0) (e : κ → ι)
    (hse : ∃ j, (s ∘ e) j ≠ 0) (G : Finset K)
    (hGreg : ∀ P : Place K, minOrd P s = minOrd P (s ∘ e) → ∀ g ∈ G, g ∈ P.1) :
    ∃ C, ∀ x : QbarPoint K, (∀ g ∈ G, g ∈ x.P.1) →
      logCondOf G x ≤ tupleHeight s x - tupleHeight (s ∘ e) x + C := by
  -- integral equations of the `g ∈ G` over `ℚ[s_l / s_{e j}]`
  have hint : ∀ (g : G) (j : κ), ∃ n : ℕ, ∃ Q : ℕ → MvPolynomial ι ℚ, s (e j) ≠ 0 →
      (g : K) ^ n + ∑ k ∈ Finset.range n,
        MvPolynomial.aeval (fun l => s l / s (e j)) (Q k) * (g : K) ^ k = 0 := by
    intro g j
    by_cases hj : s (e j) = 0
    · exact ⟨0, fun _ => 0, fun h => absurd hj h⟩
    obtain ⟨n, Q, hQ⟩ := exists_integral_eq (fun l => s l / s (e j)) (g : K) fun P hP => by
      refine hGreg P (le_antisymm (minOrd_le_minOrd_comp hs e hse P) ?_) g g.2
      have h1 : minOrd P (s ∘ e) ≤ P.ord (s (e j)) := minOrd_le hse hj
      have h2 : P.ord (s (e j)) ≤ minOrd P s := by
        rw [minOrd_eq hs]
        have := P.ord_nonneg_of_mem (hP (normIdx P s hs))
        rw [P.ord_div (normIdx_ne_zero hs) hj] at this
        linarith
      linarith
    exact ⟨n, Q, fun _ => hQ⟩
  choose n Q hQ using hint
  -- the rational coefficients
  set U : Finset (Σ p : G × κ, Σ _ : ℕ, ι →₀ ℕ) :=
    Finset.univ.sigma fun p => (Finset.range (n p.1 p.2)).sigma fun k => (Q p.1 p.2 k).support
    with hU
  set q : (Σ p : G × κ, Σ _ : ℕ, ι →₀ ℕ) → ℚ := fun τ => (Q τ.1.1 τ.1.2 τ.2.1).coeff τ.2.2
    with hq
  have hloc : ∀ {F : Type} [Field F] [CharZero F] (W : AbsoluteValue F ℝ) (g : G) (j : κ),
      ∑ k ∈ Finset.range (n g j), ∑ m ∈ (Q g j k).support,
          Real.posLog (W (((Q g j k).coeff m : ℚ) : F)) ≤
        ∑ τ ∈ U, Real.posLog (W (q τ : F)) := by
    intro F _ _ W g j
    have hsub : ((Finset.range (n g j)).sigma fun k => (Q g j k).support).map
        ⟨fun τ => (⟨(g, j), τ⟩ : Σ p : G × κ, Σ _ : ℕ, ι →₀ ℕ), fun a b h => by
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact h⟩ ⊆ U := by
      intro τ hτ
      simp only [Finset.mem_map, Finset.mem_sigma, Finset.mem_range,
        Function.Embedding.coeFn_mk] at hτ
      obtain ⟨⟨k, m⟩, ⟨hk, hm⟩, rfl⟩ := hτ
      simp [hU, hk, hm]
    calc ∑ k ∈ Finset.range (n g j), ∑ m ∈ (Q g j k).support,
          Real.posLog (W (((Q g j k).coeff m : ℚ) : F))
        = ∑ τ ∈ ((Finset.range (n g j)).sigma fun k => (Q g j k).support).map
            ⟨fun τ => (⟨(g, j), τ⟩ : Σ p : G × κ, Σ _ : ℕ, ι →₀ ℕ), fun a b h => by
              simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact h⟩,
            Real.posLog (W (q τ : F)) := by
          rw [Finset.sum_map, Finset.sum_sigma]
          rfl
      _ ≤ ∑ τ ∈ U, Real.posLog (W (q τ : F)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Real.posLog_nonneg
  -- exceptional points
  set E : Set (Place K) := {P | minOrd P s ≠ minOrd P (s ∘ e)} with hE
  have hEfin : E.Finite := by
    have h1 : {P : Place K | minOrd P s ≠ 0} ⊆
        ⋃ i ∈ {i | s i ≠ 0}, {P : Place K | P.ord (s i) ≠ 0} := by
      intro P hP
      simp only [Set.mem_setOf_eq] at hP
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      rw [minOrd_eq hs] at hP
      exact ⟨_, normIdx_ne_zero hs, hP⟩
    have h2 : {P : Place K | minOrd P (s ∘ e) ≠ 0} ⊆
        ⋃ j ∈ {j | (s ∘ e) j ≠ 0}, {P : Place K | P.ord ((s ∘ e) j) ≠ 0} := by
      intro P hP
      simp only [Set.mem_setOf_eq] at hP
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      rw [minOrd_eq hse] at hP
      exact ⟨_, normIdx_ne_zero hse, hP⟩
    refine ((Set.Finite.biUnion (Set.toFinite _)
      fun i _ => Place.finite_setOf_ord_ne_zero (s i)).subset h1 |>.union
      ((Set.Finite.biUnion (Set.toFinite _) fun j _ =>
        Place.finite_setOf_ord_ne_zero ((s ∘ e) j)).subset h2)).subset
      fun P hP => ?_
    by_contra hPn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hPn
    exact hP (hPn.1.trans hPn.2.symm)
  have hXE : {x : QbarPoint K | x.P ∈ E}.Finite := QbarPoint.finite_setOf_mem hEfin
  obtain ⟨C₂, hC₂⟩ := (hXE.image fun x => logCondOf G x - (tupleHeight s x -
    tupleHeight (s ∘ e) x)).bddAbove
  refine ⟨max (∑ τ ∈ U, Height.logHeight₁ (q τ)) C₂, fun x hGx => ?_⟩
  by_cases hxE : x.P ∈ E
  · have := hC₂ ⟨x, hxE, rfl⟩
    linarith [le_max_right (∑ τ ∈ U, Height.logHeight₁ (q τ)) C₂]
  suffices hsuff : logCondOf G x ≤ tupleHeight s x - tupleHeight (s ∘ e) x +
      ∑ τ ∈ U, Height.logHeight₁ (q τ) by
    linarith [le_max_left (∑ τ ∈ U, Height.logHeight₁ (q τ)) C₂]
  have hxE' : minOrd x.P s = minOrd x.P (s ∘ e) := by
    by_contra h
    exact hxE h
  -- normalised values
  set j₀ := normIdx x.P (s ∘ e) hse with hj₀
  have hsj₀ : s (e j₀) ≠ 0 := normIdx_ne_zero hse
  have hymem : ∀ l, s l / s (e j₀) ∈ x.P.1 := fun l => by
    refine div_mem_of_minimal hsj₀ (fun l' hl' => ?_) l
    have h1 := minOrd_le (P := x.P) hs hl'
    rw [hxE', minOrd_eq hse] at h1
    exact h1
  set y : ι → x.fieldOf := fun l => evalF x ⟨s l / s (e j₀), hymem l⟩ with hy
  have hyej₀ : y (e j₀) = 1 := by
    simp only [hy]
    rw [show (⟨s (e j₀) / s (e j₀), hymem (e j₀)⟩ : x.P.1) = 1 from
      Subtype.ext (div_self hsj₀), map_one]
  have hy0 : y ≠ 0 := fun h => by
    have := congrFun h (e j₀)
    rw [hyej₀] at this
    exact one_ne_zero this
  have hye0 : y ∘ e ≠ 0 := fun h => by
    have := congrFun h j₀
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rw [hyej₀] at this
    exact one_ne_zero this
  have hsh : tupleHeight s x = logHeight fun l => (y l : Qbar) := by
    have hmem : ∀ l, s l * (s (e j₀))⁻¹ ∈ x.P.1 := fun l => by
      rw [← div_eq_mul_inv]
      exact hymem l
    have hne : ∃ l, x.eval (s l * (s (e j₀))⁻¹) (hmem l) ≠ 0 := by
      refine ⟨e j₀, ?_⟩
      rw [x.eval_congr (mul_inv_cancel₀ hsj₀), x.eval_one]
      exact one_ne_zero
    rw [tupleHeight_eq_of_mul hs x (s (e j₀))⁻¹ hmem hne]
    congr 1
    funext l
    rw [coe_evalF]
    exact x.eval_congr (div_eq_mul_inv _ _).symm _
  have hseh : tupleHeight (s ∘ e) x = logHeight fun j => (y (e j) : Qbar) := by
    rw [tupleHeight_def hse]
    rfl
  rw [hsh, hseh]
  -- the local inequality at a finite place
  have hlocal : ∀ w : FinitePlace x.fieldOf,
      (if w ∈ meetsAt x G hGx then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) ≤
        (Real.log (⨆ l, w (y l)) - Real.log (⨆ j, w (y (e j)))) +
          ∑ τ ∈ U, Real.posLog (w (q τ : x.fieldOf)) := by
    intro w
    haveI : Nonempty ι := ⟨e j₀⟩
    haveI : Nonempty κ := ⟨j₀⟩
    obtain ⟨l₁, -, hl₁⟩ := Finset.exists_max_image Finset.univ (fun l => w (y l)) ⟨e j₀, by simp⟩
    obtain ⟨j₁, -, hj₁⟩ := Finset.exists_max_image Finset.univ (fun j => w (y (e j)))
      ⟨j₀, by simp⟩
    have hsupy : (⨆ l, w (y l)) = w (y l₁) :=
      le_antisymm (ciSup_le fun l => hl₁ l (by simp))
        (le_ciSup (f := fun l => w (y l)) (Finite.bddAbove_range _) l₁)
    have hsupye : (⨆ j, w (y (e j))) = w (y (e j₁)) :=
      le_antisymm (ciSup_le fun j => hj₁ j (by simp))
        (le_ciSup (f := fun j => w (y (e j))) (Finite.bddAbove_range _) j₁)
    have hwyej₁ : 1 ≤ w (y (e j₁)) := by
      have := hj₁ j₀ (by simp)
      rw [hyej₀, map_one] at this
      exact this
    have hyej₁ : y (e j₁) ≠ 0 := fun h => by
      rw [h, map_zero] at hwyej₁
      linarith
    have hle : w (y (e j₁)) ≤ w (y l₁) := hl₁ (e j₁) (by simp)
    have hyl₁ : y l₁ ≠ 0 := fun h => by
      rw [h, map_zero] at hle
      linarith
    have hU0 : 0 ≤ ∑ τ ∈ U, Real.posLog (w (q τ : x.fieldOf)) :=
      Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
    rw [hsupy, hsupye]
    rcases hle.lt_or_eq with hlt | heq
    · -- the maxima differ: by discreteness, by a factor `≥ N(w)`
      have h1 := FinitePlace.mul_absNorm_le_of_lt w hyl₁ hyej₁ hlt
      have hN : (0 : ℝ) < Ideal.absNorm w.maximalIdeal.asIdeal := by
        exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm _))
      have h2 : Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) ≤
          Real.log (w (y l₁)) - Real.log (w (y (e j₁))) := by
        rw [← Real.log_div (w.pos_iff.mpr hyl₁).ne' (w.pos_iff.mpr hyej₁).ne']
        refine Real.log_le_log hN ?_
        rw [le_div_iff₀ (w.pos_iff.mpr hyej₁)]
        exact h1
      split_ifs
      · linarith
      · have : 0 ≤ Real.log (w (y l₁)) - Real.log (w (y (e j₁))) := by
          have := Real.log_le_log (w.pos_iff.mpr hyej₁) hle
          linarith
        linarith
    · -- the maxima agree: `x` does not meet `D` at `w` beyond the coefficients' contribution
      rw [← heq, sub_self, zero_add]
      split_ifs with hmeet
      · obtain ⟨g, hgG, hg1⟩ := hmeet
        -- all `s_l / s_{e j₁}` are regular at `x` with `|·|_w ≤ 1`
        have hse₁ : s (e j₁) ≠ 0 := by
          intro h0
          apply hyej₁
          apply Subtype.ext
          rw [coe_evalF]
          simp only [ZeroMemClass.coe_zero]
          rw [x.eval_eq_zero_iff']
          left
          rw [h0, zero_div]
        have hordj₁ : x.P.ord (s (e j₁) / s (e j₀)) = 0 := by
          have h0 : 0 ≤ x.P.ord (s (e j₁) / s (e j₀)) := x.P.ord_nonneg_of_mem (hymem (e j₁))
          by_contra hne0
          apply hyej₁
          apply Subtype.ext
          rw [coe_evalF]
          simp only [ZeroMemClass.coe_zero]
          rw [x.eval_eq_zero_iff _ (div_ne_zero hse₁ hsj₀)]
          omega
        have hgmem : ∀ l, s l / s (e j₁) ∈ x.P.1 := fun l => by
          rcases eq_or_ne (s l) 0 with hsl | hsl
          · rw [hsl, zero_div]
            exact zero_mem _
          apply x.P.mem_of_ord_nonneg
          rw [x.P.ord_div hsl hse₁]
          have h1 := x.P.ord_nonneg_of_mem (hymem l)
          rw [x.P.ord_div hsl hsj₀] at h1
          rw [x.P.ord_div hse₁ hsj₀] at hordj₁
          linarith
        have hgval : ∀ l, evalF x ⟨s l / s (e j₁), hgmem l⟩ = y l / y (e j₁) := fun l => by
          rw [eq_div_iff hyej₁]
          simp only [hy]
          rw [← map_mul]
          congr 1
          apply Subtype.ext
          simp only [MulMemClass.coe_mul]
          field_simp
        have hcoef : ∀ k, ∃ h : MvPolynomial.aeval (fun l => s l / s (e j₁))
            (Q ⟨g, hgG⟩ j₁ k) ∈ x.P.1, evalF x ⟨_, h⟩ =
              MvPolynomial.eval₂ (Rat.castHom x.fieldOf) (fun l => y l / y (e j₁))
                (Q ⟨g, hgG⟩ j₁ k) := fun k => by
          obtain ⟨h, he⟩ := aeval_mem_and_evalF x (fun l => s l / s (e j₁)) hgmem
            (Q ⟨g, hgG⟩ j₁ k)
          exact ⟨h, he.trans (by simp only [hgval])⟩
        choose hcm hce using hcoef
        have heq' : ((⟨g, hGx g hgG⟩ : x.P.1) ^ n ⟨g, hgG⟩ j₁ +
            ∑ k ∈ Finset.range (n ⟨g, hgG⟩ j₁),
              (⟨_, hcm k⟩ : x.P.1) * ⟨g, hGx g hgG⟩ ^ k) = 0 := by
          apply Subtype.ext
          simp only [AddMemClass.coe_add, SubmonoidClass.coe_pow, ZeroMemClass.coe_zero]
          rw [← hQ ⟨g, hgG⟩ j₁ hse₁]
          congr 1
          rw [AddSubmonoidClass.coe_finsetSum]
          rfl
        have heqF := congrArg (evalF x) heq'
        rw [map_add, map_pow, map_sum, map_zero] at heqF
        simp only [map_mul, map_pow, hce] at heqF
        set gx : x.fieldOf := evalF x ⟨g, hGx g hgG⟩ with hgx
        have hgx1 : 1 < w gx := hg1
        have hgx0 : gx ≠ 0 := fun h0 => by
          rw [h0, map_zero] at hgx1
          linarith
        have hbound := log_apply_le_of_eq_nonarch w.1 (fun a b => w.add_le a b)
          (a := fun l => y l / y (e j₁)) (fun l => by
            change w (y l / y (e j₁)) ≤ 1
            rw [map_div₀]
            exact div_le_one_of_le₀ (heq ▸ hl₁ l (by simp)) (apply_nonneg w _))
          (Q ⟨g, hgG⟩ j₁) hgx0 heqF
        have hN := FinitePlace.absNorm_le_of_one_lt w hgx1
        have hNpos : (0 : ℝ) < Ideal.absNorm w.maximalIdeal.asIdeal := by
          exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm _))
        have h3 := Real.log_le_log hNpos hN
        have h4 := hloc w.1 ⟨g, hgG⟩ j₁
        change Real.log (w gx) ≤ _ at hbound
        simp only [← NumberField.FinitePlace.coe_apply] at hbound h4
        linarith
      · exact hU0
  -- summation
  have hF : (0 : ℝ) < Module.finrank ℚ x.fieldOf := Nat.cast_pos.mpr Module.finrank_pos
  have hy' := finrank_mul_logHeight_eq_sum x.fieldOf hy0
  have hye' := finrank_mul_logHeight_eq_sum x.fieldOf hye0
  have hinf : ∑ w : InfinitePlace x.fieldOf, (w.mult : ℝ) * Real.log (⨆ j, w (y (e j))) ≤
      ∑ w : InfinitePlace x.fieldOf, (w.mult : ℝ) * Real.log (⨆ l, w (y l)) := by
    refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    haveI : Nonempty κ := ⟨j₀⟩
    have hpos : 0 < ⨆ j, w (y (e j)) := by
      refine lt_of_lt_of_le ?_ (le_ciSup (f := fun j => w (y (e j))) (Finite.bddAbove_range _) j₀)
      rw [hyej₀, map_one]
      exact one_pos
    refine Real.log_le_log hpos (ciSup_le fun j => ?_)
    exact le_ciSup (f := fun l => w (y l)) (Finite.bddAbove_range _) (e j)
  have hA := hasFiniteSupport_log_iSup x.fieldOf hy0
  have hB : (fun v : FinitePlace x.fieldOf => Real.log (⨆ j, v (y (e j)))).HasFiniteSupport :=
    hasFiniteSupport_log_iSup x.fieldOf (y := fun j => y (e j)) hye0
  have hC : (fun v : FinitePlace x.fieldOf =>
      ∑ τ ∈ U, Real.posLog (v (q τ : x.fieldOf))).HasFiniteSupport :=
    Function.HasFiniteSupport.sum (fun τ => hasFiniteSupport_posLog x.fieldOf (q τ : x.fieldOf)) U
  have hM := hasFiniteSupport_meetsAt x G hGx
  -- all finsums as sums over a common finite set
  set S0 : Finset (FinitePlace x.fieldOf) :=
    (hA.union hB).toFinset ∪ hC.toFinset ∪ hM.toFinset with hS0
  have hsum : ∀ f : FinitePlace x.fieldOf → ℝ, Function.support f ⊆ S0 →
      ∑ᶠ v, f v = ∑ v ∈ S0, f v := fun f hf => finsum_eq_sum_of_support_subset f hf
  have hsA : ∑ᶠ v : FinitePlace x.fieldOf, Real.log (⨆ l, v (y l)) =
      ∑ v ∈ S0, Real.log (⨆ l, v (y l)) := hsum _ fun v hv => by
    simp only [hS0, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    exact Or.inl (Or.inl (Or.inl hv))
  have hsB : ∑ᶠ v : FinitePlace x.fieldOf, Real.log (⨆ j, v (y (e j))) =
      ∑ v ∈ S0, Real.log (⨆ j, v (y (e j))) := hsum _ fun v hv => by
    simp only [hS0, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    exact Or.inl (Or.inl (Or.inr hv))
  have hsM : (∑ᶠ v : FinitePlace x.fieldOf, if v ∈ meetsAt x G hGx then
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) =
      ∑ v ∈ S0, if v ∈ meetsAt x G hGx then
        Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0 := hsum _ fun v hv => by
    simp only [hS0, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    exact Or.inr hv
  have hsC : ∀ τ ∈ U, ∑ᶠ v : FinitePlace x.fieldOf, Real.posLog (v (q τ : x.fieldOf)) ≥
      ∑ v ∈ S0, Real.posLog (v (q τ : x.fieldOf)) := by
    intro τ _
    rw [finsum_eq_sum_of_support_subset _ (s := (hasFiniteSupport_posLog x.fieldOf
      (q τ : x.fieldOf)).toFinset ∪ S0) (by
        intro v hv
        simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
        exact Or.inl hv)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      fun _ _ _ => Real.posLog_nonneg
  have hlocalsum : (∑ v ∈ S0, if v ∈ meetsAt x G hGx then
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) ≤
      (∑ v ∈ S0, Real.log (⨆ l, v (y l))) - (∑ v ∈ S0, Real.log (⨆ j, v (y (e j)))) +
        ∑ τ ∈ U, ∑ v ∈ S0, Real.posLog (v (q τ : x.fieldOf)) := by
    rw [Finset.sum_comm (s := U), ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => hlocal v
  have hqsum : ∑ τ ∈ U, ∑ v ∈ S0, Real.posLog (v (q τ : x.fieldOf)) ≤
      (Module.finrank ℚ x.fieldOf : ℝ) * ∑ τ ∈ U, Height.logHeight₁ (q τ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ hτ => (hsC τ hτ).trans (finsum_posLog_le x.fieldOf (q τ))
  have hdeg : (x.deg : ℝ) = Module.finrank ℚ x.fieldOf := rfl
  unfold logCondOf
  rw [dif_pos hGx, div_le_iff₀ (by rw [hdeg]; exact hF), hdeg]
  rw [hsA] at hy'
  have hye'' : (Module.finrank ℚ x.fieldOf : ℝ) * logHeight (fun j => (y (e j) : Qbar)) =
      ∑ w : InfinitePlace x.fieldOf, (w.mult : ℝ) * Real.log (⨆ j, w (y (e j))) +
        ∑ v ∈ S0, Real.log (⨆ j, v (y (e j))) := by
    rw [← hsB]
    exact hye'
  rw [hsM]
  nlinarith [hinf, hlocalsum, hqsum, hy', hye'']

end Prop16

end Heights.Curve
