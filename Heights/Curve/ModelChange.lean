/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.CondHeight

/-!
# Changing the model: log-conductors ([GenEll], Remark 1.5.1)

The log-conductor of a point with respect to the affine model given by generators `G` of the
coordinate ring of `X ∖ D` depends on the model only up to a bounded amount: if every `g' ∈ G'`
is a polynomial with rational coefficients in the elements of `G`, then
`log-cond_{G'} ≤ log-cond_G + C` on the points where the `G` are regular
(`Heights.Curve.logCondOf_le_logCondOf_add`). At a place where `x` meets the `G'`-model but not
the `G`-model, some rational coefficient must be non-integral, and the contribution of such
places is bounded by the heights of the finitely many coefficients.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute NumberField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

open Classical in
/-- **Model independence of log-conductors** ([GenEll], Remark 1.5.1). -/
theorem logCondOf_le_logCondOf_add (G G' : Finset K)
    (hG' : ∀ g' ∈ G', g' ∈ Algebra.adjoin ℚ (G : Set K)) :
    ∃ C, ∀ x : QbarPoint K, (hG : ∀ g ∈ G, g ∈ x.P.1) → (∀ g ∈ G', g ∈ x.P.1) →
      logCondOf G' x ≤ logCondOf G x + C := by
  -- write the elements of `G'` as polynomials in those of `G`
  have hpoly : ∀ g' : G', ∃ Q : MvPolynomial G ℚ,
      MvPolynomial.aeval (fun g : G => (g : K)) Q = (g' : K) := by
    intro g'
    have h := hG' g'.1 g'.2
    have hrange : Set.range (fun g : G => (g : K)) = (G : Set K) := by
      ext y
      simp
    rw [← hrange, Algebra.adjoin_range_eq_range_aeval] at h
    exact h
  choose Q hQ using hpoly
  set U : Finset (Σ _ : G', G →₀ ℕ) := Finset.univ.sigma fun g' => (Q g').support with hU
  set q : (Σ _ : G', G →₀ ℕ) → ℚ := fun τ => (Q τ.1).coeff τ.2 with hq
  refine ⟨∑ τ ∈ U, Height.logHeight₁ (q τ), fun x hG hG' => ?_⟩
  set F := x.fieldOf
  set a : G → F := fun g => evalF x ⟨g.1, hG g.1 g.2⟩ with ha
  -- the values of the `g'` are the polynomials evaluated at the values of the `g`
  have hval : ∀ g' : G', ∃ h : (g' : K) ∈ x.P.1, evalF x ⟨g', h⟩ =
      MvPolynomial.eval₂ (Rat.castHom F) a (Q g') := by
    intro g'
    obtain ⟨h, he⟩ := aeval_mem_and_evalF x (fun g : G => (g : K)) (fun g => hG g.1 g.2) (Q g')
    rw [hQ g'] at h
    refine ⟨h, ?_⟩
    have : (⟨(g' : K), h⟩ : x.P.1) = ⟨MvPolynomial.aeval (fun g : G => (g : K)) (Q g'), by
      rw [hQ g']; exact h⟩ := Subtype.ext (hQ g').symm
    rw [this]
    exact he
  -- the local inequality
  have hlocal : ∀ w : FinitePlace F,
      (if w ∈ meetsAt x G' hG' then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) ≤
        (if w ∈ meetsAt x G hG then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) +
          ∑ τ ∈ U, Real.posLog (w (q τ : F)) := by
    intro w
    have hU0 : 0 ≤ ∑ τ ∈ U, Real.posLog (w (q τ : F)) :=
      Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
    have hN0 : 0 ≤ Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) :=
      Real.log_nonneg (by exact_mod_cast
        (NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal).le)
    by_cases hm : w ∈ meetsAt x G hG
    · rw [if_pos hm]
      split_ifs <;> linarith
    · rw [if_neg hm, zero_add]
      split_ifs with hm'
      · obtain ⟨g', hg'G, hg'1⟩ := hm'
        -- all generators of the `G`-model are `w`-integral at `x`
        have hle : ∀ g : G, w (a g) ≤ 1 := by
          intro g
          by_contra hlt
          push Not at hlt
          exact hm ⟨g.1, g.2, hlt⟩
        obtain ⟨h, he⟩ := hval ⟨g', hg'G⟩
        have h1 : w (evalF x ⟨g', h⟩) ≤ coeffBound w.1 (Q ⟨g', hg'G⟩) := by
          rw [he]
          exact apply_eval₂_le_nonarch w.1 (fun a b => w.add_le a b) hle _
        have h2 : 1 < w (evalF x ⟨g', h⟩) := hg'1
        have h3 := FinitePlace.absNorm_le_of_one_lt w h2
        have hNpos : (0 : ℝ) < Ideal.absNorm w.maximalIdeal.asIdeal := by
          exact_mod_cast (Nat.zero_lt_one.trans
            (NumberField.HeightOneSpectrum.one_lt_absNorm _))
        have h4 : Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) ≤
            Real.log (coeffBound w.1 (Q ⟨g', hg'G⟩)) :=
          Real.log_le_log hNpos (h3.trans h1)
        rw [log_coeffBound] at h4
        have h5 : ∑ m ∈ (Q ⟨g', hg'G⟩).support, Real.posLog (w.1 (((Q ⟨g', hg'G⟩).coeff m : ℚ) : F))
            ≤ ∑ τ ∈ U, Real.posLog (w (q τ : F)) := by
          have hsub : ((Q ⟨g', hg'G⟩).support).map
              ⟨fun m => (⟨⟨g', hg'G⟩, m⟩ : Σ _ : G', G →₀ ℕ), fun a b h => by
                simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact h⟩ ⊆ U := by
            intro τ hτ
            simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hτ
            obtain ⟨m, hm, rfl⟩ := hτ
            simp [hU, hm]
          calc ∑ m ∈ (Q ⟨g', hg'G⟩).support, Real.posLog (w.1 (((Q ⟨g', hg'G⟩).coeff m : ℚ) : F))
              = ∑ τ ∈ ((Q ⟨g', hg'G⟩).support).map
                  ⟨fun m => (⟨⟨g', hg'G⟩, m⟩ : Σ _ : G', G →₀ ℕ), fun a b h => by
                    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact h⟩,
                  Real.posLog (w (q τ : F)) := by
                rw [Finset.sum_map]
                rfl
            _ ≤ ∑ τ ∈ U, Real.posLog (w (q τ : F)) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Real.posLog_nonneg
        linarith
      · exact hU0
  -- summation over a common finite set of places
  have hM := hasFiniteSupport_meetsAt x G hG
  have hM' := hasFiniteSupport_meetsAt x G' hG'
  set S0 : Finset (FinitePlace F) := hM.toFinset ∪ hM'.toFinset with hS0
  have hsM : (∑ᶠ v : FinitePlace F, if v ∈ meetsAt x G hG then
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) =
      ∑ v ∈ S0, if v ∈ meetsAt x G hG then
        Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0 :=
    finsum_eq_sum_of_support_subset _ fun v hv => by
      simp only [hS0, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
      exact Or.inl hv
  have hsM' : (∑ᶠ v : FinitePlace F, if v ∈ meetsAt x G' hG' then
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) =
      ∑ v ∈ S0, if v ∈ meetsAt x G' hG' then
        Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0 :=
    finsum_eq_sum_of_support_subset _ fun v hv => by
      simp only [hS0, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
      exact Or.inr hv
  have hsC : ∀ τ ∈ U, ∑ v ∈ S0, Real.posLog (v (q τ : F)) ≤
      (Module.finrank ℚ F : ℝ) * Height.logHeight₁ (q τ) := by
    intro τ _
    refine le_trans ?_ (finsum_posLog_le F (q τ))
    rw [finsum_eq_sum_of_support_subset _ (s := (hasFiniteSupport_posLog F
      (q τ : F)).toFinset ∪ S0) (by
        intro v hv
        simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
        exact Or.inl hv)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      fun _ _ _ => Real.posLog_nonneg
  have hsum : (∑ v ∈ S0, if v ∈ meetsAt x G' hG' then
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) ≤
      (∑ v ∈ S0, if v ∈ meetsAt x G hG then
        Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) +
        (Module.finrank ℚ F : ℝ) * ∑ τ ∈ U, Height.logHeight₁ (q τ) := by
    calc _ ≤ ∑ v ∈ S0, ((if v ∈ meetsAt x G hG then
            Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) +
            ∑ τ ∈ U, Real.posLog (v (q τ : F))) := Finset.sum_le_sum fun v _ => hlocal v
      _ = _ + ∑ τ ∈ U, ∑ v ∈ S0, Real.posLog (v (q τ : F)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ _ := by
          rw [Finset.mul_sum]
          linarith [Finset.sum_le_sum hsC]
  have hF : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  have hdeg : (x.deg : ℝ) = Module.finrank ℚ F := rfl
  unfold logCondOf
  rw [dif_pos hG, dif_pos hG', hsM, hsM', hdeg, div_add' _ _ _ hF.ne',
    div_le_div_iff_of_pos_right hF]
  linarith

end Heights.Curve
