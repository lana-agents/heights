/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Different.Bounds
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Finite places of a number field over the finite places of a subfield

For number fields `F`, `L` with `[Algebra F L]`, a finite place `w` of `L` *lies over* a finite
place `u` of `F` if the prime of `w` lies over the prime of `u`
(`Heights.Different.PlaceLiesOver w u`, i.e. `w.maximalIdeal.asIdeal.LiesOver
u.maximalIdeal.asIdeal`). Writing `N(w) = Ideal.absNorm w.maximalIdeal.asIdeal`
(`Heights.Different.placeNorm`) and `e`, `f` for the ramification index and inertia degree of
the prime of `w` over the prime of `u`:

* `Heights.Different.apply_algebraMap_eq_pow`: `w (a) = u (a) ^ (e·f)` for `a ∈ F`;
* `Heights.Different.placeNorm_eq_pow`: `N(w) = N(u) ^ f`;
* `Heights.Different.placeBelow`, `Heights.Different.placeLiesOver_placeBelow` and
  `Heights.Different.eq_placeBelow`: every `w` lies over a unique `u`;
* `Heights.Different.placesOver L u`, the finite set of places of `L` over `u`, and
  `Heights.Different.sum_placesOver_eq`, which identifies sums over it with sums over
  `IsDedekindDomain.primesOverFinset`; `Heights.Different.sum_placesOver_mul_eq_finrank`:
  `∑_{w ∣ u} e·f = [L : F]`.

The comparison of absolute values is Mathlib's `HeightOneSpectrum.valuation_liesOver`,
`v(a)^e = w(a)` for the adic valuations; this file only transports it to the normalised
absolute values `w x = N(w)^{-ord_w x}` of `NumberField.FinitePlace` (the corresponding
computation in lana-agents/iut, `Iut.apply_algebraMap_eq_pow`, served as a model).
-/

namespace Heights.Different

open NumberField IsDedekindDomain Module

/-! ### The absolute norm of a finite place -/

section Norm

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm `N(w) = #(𝓞 K / 𝔭_w)` of a finite place. -/
noncomputable def placeNorm (w : FinitePlace K) : ℕ := Ideal.absNorm w.maximalIdeal.asIdeal

lemma one_lt_placeNorm (w : FinitePlace K) : 1 < placeNorm w :=
  one_lt_absNorm w.maximalIdeal

lemma log_placeNorm_pos (w : FinitePlace K) : 0 < Real.log (placeNorm w) :=
  Real.log_pos (by exact_mod_cast one_lt_placeNorm w)

lemma log_placeNorm_nonneg (w : FinitePlace K) : 0 ≤ Real.log (placeNorm w) :=
  (log_placeNorm_pos w).le

/-- `w x = N(w)^{-ord_w x}`, in the form of Mathlib's `toNNReal`. -/
lemma finitePlace_apply_eq (w : FinitePlace K) (x : K) :
    w x = (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero w.maximalIdeal)
      (w.maximalIdeal.valuation K x) : ℝ) := by
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding']

end Norm

/-! ### `toNNReal` under powers of the base -/

section ToNNReal

open WithZeroMulInt

lemma toNNReal_congr {e e' : NNReal} (h : e = e') (he : e ≠ 0) (he' : e' ≠ 0)
    (m : WithZero (Multiplicative ℤ)) :
    toNNReal he m = toNNReal he' m := by
  subst h
  rfl

/-- `toNNReal_{e^f}(m) = toNNReal_e(m)^f` for `f ≠ 0`. -/
lemma toNNReal_pow_base {e : NNReal} (he : e ≠ 0) {f : ℕ} (hf : f ≠ 0) (hef : e ^ f ≠ 0)
    (m : WithZero (Multiplicative ℤ)) : toNNReal hef m = toNNReal he m ^ f := by
  by_cases hm : m = 0
  · subst hm
    rw [map_zero, map_zero, zero_pow hf]
  · rw [toNNReal_neg_apply hef hm, toNNReal_neg_apply he hm, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]

end ToNNReal

/-! ### Places over places -/

section LiesOver

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-- The finite place `w` of `L` lies over the finite place `u` of `F`:
`𝔭_w ∩ 𝓞 F = 𝔭_u`. -/
abbrev PlaceLiesOver (w : FinitePlace L) (u : FinitePlace F) : Prop :=
  w.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal

lemma placeLiesOver_iff (w : FinitePlace L) (u : FinitePlace F) :
    PlaceLiesOver w u ↔
      w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) = u.maximalIdeal.asIdeal :=
  ⟨fun h => h.over.symm, fun h => ⟨h.symm⟩⟩

/-- The ramification index `e(w|u)`. -/
noncomputable abbrev placeRamIdx (w : FinitePlace L) (u : FinitePlace F) : ℕ :=
  u.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal

/-- The inertia degree `f(w|u)`. -/
noncomputable abbrev placeInertiaDeg (w : FinitePlace L) (u : FinitePlace F) : ℕ :=
  u.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal

lemma placeRamIdx_ne_zero {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    placeRamIdx w u ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ u.maximalIdeal.ne_bot

lemma placeInertiaDeg_ne_zero {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    placeInertiaDeg w u ≠ 0 := by
  haveI := u.maximalIdeal.isMaximal
  exact (Ideal.inertiaDeg'_pos _ _).ne'

/-- **`N(w) = N(u)^f`** for `w` over `u`. -/
theorem placeNorm_eq_pow {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    placeNorm w = placeNorm u ^ placeInertiaDeg w u :=
  Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver _ _ inferInstance u.maximalIdeal.ne_bot

/-- `log N(w) = f·log N(u)` for `w` over `u`. -/
lemma log_placeNorm_eq {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    Real.log (placeNorm w) = placeInertiaDeg w u * Real.log (placeNorm u) := by
  rw [placeNorm_eq_pow h, Nat.cast_pow, Real.log_pow]

/-- **`w (a) = u (a)^{e·f}`** for `a ∈ F` and `w` over `u`. -/
theorem apply_algebraMap_eq_pow {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u)
    (a : F) : w (algebraMap F L a) = u a ^ (placeRamIdx w u * placeInertiaDeg w u) := by
  rw [finitePlace_apply_eq, finitePlace_apply_eq,
    ← HeightOneSpectrum.valuation_liesOver L u.maximalIdeal w.maximalIdeal, map_pow]
  have hN : (Ideal.absNorm w.maximalIdeal.asIdeal : NNReal) =
      (Ideal.absNorm u.maximalIdeal.asIdeal : NNReal) ^ placeInertiaDeg w u := by
    exact_mod_cast placeNorm_eq_pow h
  rw [toNNReal_congr hN _ (pow_ne_zero _ (HeightOneSpectrum.absNorm_ne_zero _)),
    toNNReal_pow_base (HeightOneSpectrum.absNorm_ne_zero _) (placeInertiaDeg_ne_zero h),
    ← pow_mul, NNReal.coe_pow, mul_comm]

/-- `u (a) = 1 → w (a) = 1`, and more generally `1 < u a ↔ 1 < w a`. -/
lemma one_lt_apply_algebraMap_iff {w : FinitePlace L} {u : FinitePlace F}
    (h : PlaceLiesOver w u) (a : F) : 1 < w (algebraMap F L a) ↔ 1 < u a := by
  rw [apply_algebraMap_eq_pow h]
  exact one_lt_pow_iff_of_nonneg (apply_nonneg u a)
    (mul_ne_zero (placeRamIdx_ne_zero h) (placeInertiaDeg_ne_zero h))

/-! #### The place below -/

variable (L) in
/-- The finite place of `F` below a finite place of `L`. -/
noncomputable def placeBelow (w : FinitePlace L) : FinitePlace F :=
  FinitePlace.mk (primeBelow L w.maximalIdeal)

lemma placeBelow_maximalIdeal (w : FinitePlace L) :
    (placeBelow L w : FinitePlace F).maximalIdeal = primeBelow L w.maximalIdeal :=
  FinitePlace.maximalIdeal_mk _

/-- Every finite place of `L` lies over the place below it. -/
theorem placeLiesOver_placeBelow (w : FinitePlace L) :
    PlaceLiesOver w (placeBelow L w : FinitePlace F) := by
  rw [placeLiesOver_iff, placeBelow_maximalIdeal]
  rfl

/-- **The place below is unique**: if `w` lies over `u`, then `u` is the place below `w`. -/
theorem eq_placeBelow {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    u = placeBelow L w := by
  rw [← FinitePlace.maximalIdeal_inj]
  apply HeightOneSpectrum.ext
  rw [placeBelow_maximalIdeal]
  exact h.over

lemma placeLiesOver_iff_eq_placeBelow {w : FinitePlace L} {u : FinitePlace F} :
    PlaceLiesOver w u ↔ u = placeBelow L w :=
  ⟨eq_placeBelow, fun h => h ▸ placeLiesOver_placeBelow w⟩

/-! #### The places over a place -/

/-- The finite place of `L` of a prime of `𝓞 L` over `𝔭_u`. -/
noncomputable def placeOfPrimeOver (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) : FinitePlace L :=
  haveI := u.maximalIdeal.isMaximal
  FinitePlace.mk
    ⟨P, ((mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP).1, by
      obtain ⟨_, _⟩ := (mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP
      exact Ideal.ne_bot_of_liesOver_of_ne_bot u.maximalIdeal.ne_bot P⟩

lemma placeOfPrimeOver_maximalIdeal (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) :
    (placeOfPrimeOver u hP).maximalIdeal.asIdeal = P := by
  rw [placeOfPrimeOver, FinitePlace.maximalIdeal_mk]

lemma mem_primesOverFinset_of_placeLiesOver {w : FinitePlace L} {u : FinitePlace F}
    (h : PlaceLiesOver w u) :
    w.maximalIdeal.asIdeal ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L) := by
  haveI := u.maximalIdeal.isMaximal
  exact (mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mpr ⟨w.maximalIdeal.isPrime, h⟩

variable (L) in
/-- The finitely many places of `L` over `u`. -/
lemma finite_placeLiesOver (u : FinitePlace F) :
    {w : FinitePlace L | PlaceLiesOver w u}.Finite := by
  refine Set.Finite.of_finite_image ?_
    (f := fun w : FinitePlace L => w.maximalIdeal.asIdeal) ?_
  · refine (IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal
      (𝓞 L)).finite_toSet.subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact mem_primesOverFinset_of_placeLiesOver hw
  · intro w₁ _ w₂ _ h
    exact (FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h)

variable (L) in
/-- The finite set of places of `L` over `u`. -/
noncomputable def placesOver (u : FinitePlace F) : Finset (FinitePlace L) :=
  (finite_placeLiesOver L u).toFinset

lemma mem_placesOver {u : FinitePlace F} {w : FinitePlace L} :
    w ∈ placesOver L u ↔ PlaceLiesOver w u := by
  rw [placesOver, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

lemma placeLiesOver_placeOfPrimeOver (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) :
    PlaceLiesOver (placeOfPrimeOver u hP) u := by
  haveI := u.maximalIdeal.isMaximal
  unfold PlaceLiesOver
  rw [placeOfPrimeOver_maximalIdeal]
  exact ((mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP).2

/-- **The places over `u` correspond to `primesOverFinset`**: a sum over the places of `L`
over `u` of a function of the prime is the sum over the primes of `𝓞 L` over `𝔭_u`. -/
theorem sum_placesOver_eq {M : Type*} [AddCommMonoid M] (u : FinitePlace F)
    (g : Ideal (𝓞 L) → M) :
    ∑ w ∈ placesOver L u, g w.maximalIdeal.asIdeal =
      ∑ P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L), g P := by
  refine Finset.sum_bij (fun w _ => w.maximalIdeal.asIdeal)
    (fun w hw => mem_primesOverFinset_of_placeLiesOver (mem_placesOver.mp hw)) ?_ ?_
    (fun _ _ => rfl)
  · intro w₁ _ w₂ _ h
    exact (FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h)
  · intro P hP
    exact ⟨placeOfPrimeOver u hP, mem_placesOver.mpr (placeLiesOver_placeOfPrimeOver u hP),
      placeOfPrimeOver_maximalIdeal u hP⟩

/-- `∑_{w ∣ u} e(w|u)·f(w|u) = [L : F]`. -/
theorem sum_placesOver_mul_eq_finrank (u : FinitePlace F) :
    ∑ w ∈ placesOver L u, placeRamIdx w u * placeInertiaDeg w u = finrank F L := by
  haveI := u.maximalIdeal.isMaximal
  rw [sum_placesOver_eq u (fun P => u.maximalIdeal.asIdeal.ramificationIdx' P *
    u.maximalIdeal.asIdeal.inertiaDeg' P)]
  exact Ideal.sum_ramification_inertia (𝓞 L) F L u.maximalIdeal.ne_bot

end LiesOver

end Heights.Different
