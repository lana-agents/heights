/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Heights.Different.Bounds

/-!
# Unramifiedness criteria for extensions of number fields

For number fields `F ⊆ L`:

* `Heights.Different.ramificationIdx'_eq_one_of_not_dvd`: a prime `P` of `L` not dividing
  the different `𝔇_{L/F}` is unramified over `F`;
* `Heights.Different.ramificationIdx'_eq_one_of_aeval_derivative_notMem`: if
  `L = F[α]` with `α ∈ 𝓞 L` and `g'(α) ∉ P` for the minimal polynomial `g` of `α` over
  `𝓞 F`, then `e(P|P ∩ 𝓞 F) = 1` (since `g'(α) ∈ 𝔇`);
* `Heights.Different.ramificationIdx'_eq_one_of_pow_eq` (Kummer-type): if `L = F[α]`,
  `α^N = a ∈ 𝓞 F` and `N·a ∉ 𝔭`, every prime of `L` over `𝔭` is unramified;
* `Heights.Different.ramificationIdx'_eq_one_of_tower`: unramifiedness over `𝔭` in a tower
  `F ⊆ M ⊆ L` follows from unramifiedness in each step.
-/

namespace Heights.Different

open NumberField Module Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

section Criterion

variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) (P : Ideal (𝓞 L)) [P.IsPrime]
  [P.LiesOver 𝔭]

include h𝔭

/-- A prime of `L` not dividing `𝔇_{L/F}` is unramified over `F`. -/
theorem ramificationIdx'_eq_one_of_not_dvd (hP : ¬ P ∣ differentIdeal (𝓞 F) (𝓞 L)) :
    𝔭.ramificationIdx' P = 1 := by
  have h1 := ramificationIdx'_sub_one_le_multiplicity h𝔭 P
  rw [multiplicity_eq_zero_of_not_dvd hP] at h1
  have h2 := ramificationIdx'_ne_zero' h𝔭 P
  omega

/-- **The derivative criterion**: if `L = F[α]` with `α ∈ 𝓞 L`, and `g'(α) ∉ P` for the
minimal polynomial `g` of `α` over `𝓞 F`, then `P` is unramified over `F`. -/
theorem ramificationIdx'_eq_one_of_aeval_derivative_notMem (α : 𝓞 L)
    (hα : Algebra.adjoin F {(α : L)} = ⊤)
    (hP : aeval α (derivative (minpoly (𝓞 F) α)) ∉ P) :
    𝔭.ramificationIdx' P = 1 := by
  refine ramificationIdx'_eq_one_of_not_dvd h𝔭 P fun hdvd => hP ?_
  exact Ideal.le_of_dvd hdvd (aeval_derivative_mem_differentIdeal (𝓞 F) F L α hα)

/-- The derivative criterion with `L = F⟮α⟯`. -/
theorem ramificationIdx'_eq_one_of_aeval_derivative_notMem' (α : 𝓞 L)
    (hα : IntermediateField.adjoin F {(α : L)} = ⊤)
    (hP : aeval α (derivative (minpoly (𝓞 F) α)) ∉ P) :
    𝔭.ramificationIdx' P = 1 := by
  refine ramificationIdx'_eq_one_of_aeval_derivative_notMem h𝔭 P α ?_ hP
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (α : L)), hα, IntermediateField.top_toSubalgebra]

omit h𝔭 [NumberField F] [NumberField L] [𝔭.IsMaximal] [P.IsPrime] in
/-- An element of `𝓞 F` outside `𝔭` stays outside every prime of `L` over `𝔭`. -/
lemma algebraMap_notMem {x : 𝓞 F} (hx : x ∉ 𝔭) : algebraMap (𝓞 F) (𝓞 L) x ∉ P := by
  intro h
  apply hx
  rw [Ideal.over_def P 𝔭]
  exact h

/-- **The Kummer criterion**: if `L = F[α]` with `α^N = a ∈ 𝓞 F` and `N·a ∉ 𝔭`, then every
prime `P` of `L` over `𝔭` is unramified. -/
theorem ramificationIdx'_eq_one_of_pow_eq (α : 𝓞 L) (hα : Algebra.adjoin F {(α : L)} = ⊤)
    (N : ℕ) (a : 𝓞 F) (hαa : α ^ N = algebraMap (𝓞 F) (𝓞 L) a) (hNa : (N : 𝓞 F) * a ∉ 𝔭) :
    𝔭.ramificationIdx' P = 1 := by
  refine ramificationIdx'_eq_one_of_aeval_derivative_notMem h𝔭 P α hα fun hmem => hNa ?_
  -- the minimal polynomial divides `X^N − a`
  have hint : IsIntegral (𝓞 F) α := Algebra.IsIntegral.isIntegral α
  obtain ⟨h, hh⟩ : minpoly (𝓞 F) α ∣ X ^ N - C a := by
    refine minpoly.isIntegrallyClosed_dvd hint ?_
    simp [hαa]
  -- differentiating, `N·α^{N-1} = g'(α)·h(α)`
  have hder : ((N : 𝓞 L)) * α ^ (N - 1) =
      aeval α (derivative (minpoly (𝓞 F) α)) * aeval α h := by
    have := congrArg (fun q => aeval α (derivative q)) hh
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul,
      map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at this
    simpa using this
  have hmem' : ((N : 𝓞 L)) * α ^ (N - 1) ∈ P := by
    rw [hder]
    exact Ideal.mul_mem_right _ _ hmem
  have hcomap : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 L) x ∈ P → x ∈ 𝔭 := by
    intro x hx
    by_contra hx'
    exact algebraMap_notMem P hx' hx
  rcases (inferInstance : P.IsPrime).mem_or_mem hmem' with hN | hα'
  · exact Ideal.mul_mem_right _ _ (hcomap _ (by rwa [map_natCast]))
  · refine Ideal.mul_mem_left _ _ (hcomap _ ?_)
    rw [← hαa]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exfalso
      apply hNa
      rw [Nat.cast_zero, zero_mul]
      exact Ideal.zero_mem _
    · have hαP : α ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem _ hα'
      exact Ideal.pow_mem_of_mem _ hαP _ hN

end Criterion

/-- **The Kummer criterion**, for all primes over `𝔭` at once. -/
theorem forall_ramificationIdx'_eq_one_of_pow_eq {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥)
    (α : 𝓞 L) (hα : Algebra.adjoin F {(α : L)} = ⊤) (N : ℕ) (a : 𝓞 F)
    (hαa : α ^ N = algebraMap (𝓞 F) (𝓞 L) a) (hNa : (N : 𝓞 F) * a ∉ 𝔭) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L), 𝔭.ramificationIdx' P = 1 := by
  intro P hP
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  exact ramificationIdx'_eq_one_of_pow_eq h𝔭 P α hα N a hαa hNa

/-! ### Towers -/

section Tower

variable (M : Type*) [Field M] [NumberField M] [Algebra F M] [Algebra M L] [IsScalarTower F M L]

omit [NumberField F] in
/-- **Unramifiedness in a tower**: if `F ⊆ M ⊆ L`, every prime of `M` over `𝔭` is
unramified over `F` and every prime of `L` over such a prime is unramified over `M`, then
every prime of `L` over `𝔭` is unramified over `F`. -/
theorem ramificationIdx'_eq_one_of_tower {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥)
    (h₁ : ∀ Q ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 M), 𝔭.ramificationIdx' Q = 1)
    (h₂ : ∀ Q ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 M),
      ∀ P ∈ IsDedekindDomain.primesOverFinset Q (𝓞 L), Q.ramificationIdx' P = 1)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭] : 𝔭.ramificationIdx' P = 1 := by
  set Q := P.under (𝓞 M)
  haveI : Q.LiesOver 𝔭 := Ideal.LiesOver.tower_bot P Q 𝔭
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 Q
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 M) :=
    (mem_primesOverFinset_iff' h𝔭).mpr ⟨inferInstance, inferInstance⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset Q (𝓞 L) :=
    (mem_primesOverFinset_iff' hQ0).mpr ⟨inferInstance, inferInstance⟩
  rw [Ideal.ramificationIdx'_algebra_tower' 𝔭 Q P, h₁ Q hQ, h₂ Q hQ P hP]

/-- **Adjoining two Kummer generators**: if `M = F[β]` with `β^N = a`, `L = M[γ]` with
`γ^{N'} = b`, where `a, b ∈ 𝓞 F` and `N·a, N'·b ∉ 𝔭`, then every prime of `L` over `𝔭` is
unramified over `F`. -/
theorem ramificationIdx'_eq_one_of_pow_eq_of_pow_eq {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal]
    (h𝔭 : 𝔭 ≠ ⊥) (β : 𝓞 M) (hβ : Algebra.adjoin F {(β : M)} = ⊤) (N : ℕ) (a : 𝓞 F)
    (hβa : β ^ N = algebraMap (𝓞 F) (𝓞 M) a) (hNa : (N : 𝓞 F) * a ∉ 𝔭)
    (γ : 𝓞 L) (hγ : Algebra.adjoin M {(γ : L)} = ⊤) (N' : ℕ) (b : 𝓞 F)
    (hγb : γ ^ N' = algebraMap (𝓞 F) (𝓞 L) b) (hNb : (N' : 𝓞 F) * b ∉ 𝔭)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭] : 𝔭.ramificationIdx' P = 1 := by
  refine ramificationIdx'_eq_one_of_tower M h𝔭
    (forall_ramificationIdx'_eq_one_of_pow_eq h𝔭 β hβ N a hβa hNa) ?_ P
  intro Q hQ
  obtain ⟨hQp, hQl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hQ
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 Q
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  refine forall_ramificationIdx'_eq_one_of_pow_eq hQ0 γ hγ N' (algebraMap (𝓞 F) (𝓞 M) b) ?_ ?_
  · rw [hγb, ← IsScalarTower.algebraMap_apply]
  · rw [← map_natCast (algebraMap (𝓞 F) (𝓞 M)), ← map_mul]
    exact algebraMap_notMem Q hNb

end Tower

end Heights.Different
