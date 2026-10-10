/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.Curve.Integrality
import Heights.Local.Compactness
import Heights.Local.LimitPlace

/-!
# The compactness argument of [GenEll], Theorem 2.1

Let `x_n` be algebraic points of degree `≤ d` of a curve with function field `K`, and `V` a finite
set of primes. For every `n`, the field of definition `ℚ(x_n)` has at most `d` embeddings into
`ℚ̄_p` (`p ∈ V`) and into `ℂ`; each of them turns `x_n` into an `E`-valued place of `K`
(`Heights.Curve.pointEPlace`). By sequential compactness of `ℙ¹(ℚ̄_p)^{≤d}` and `ℙ¹(ℂ)` and
a diagonal argument over the countable field `K`, a subsequence converges at all these
embeddings simultaneously, in the sense that all values `f(x_n^τ)` converge in `ℙ¹`. The limits
are `E`-valued places; the ones with a nontrivial valuation ring give a finite set `T` of places
of `K` — the algebraic limit points of [GenEll], p. 13.

`Heights.Curve.exists_subseq_bounded`: there are such a subsequence and such a finite set `T`,
such that for every `φ ∈ K ∖ {0, 1}` that is regular and invertible, with `φ − 1` invertible,
at all places of `T` (a noncritical Belyi map maps `T` into `U_ℙ`), the values `φ(x_n)` are
bounded away from `0`, `1`, `∞` at all embeddings over `V ∪ {∞}`, uniformly along a tail of the
subsequence: this puts them into a compactly bounded subset of the tripod.
-/

namespace Heights.Curve

open Belyi.CurveField Heights.Absolute Heights.Local Filter Topology
open scoped IntermediateField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-! ### Points as `E`-valued places -/

section EPlaces

variable {E : Type*} [NormedField E]

/-- A point `x` together with an embedding `τ : ℚ(x) → E` is an `E`-valued place of `K`. -/
noncomputable def pointEPlace (x : QbarPoint K) (τ : x.fieldOf →+* E) : EPlace K E where
  O := x.P.1
  ψ := τ.comp (evalF x)
  eq_zero_iff f := by
    rw [RingHom.comp_apply, map_eq_zero_iff τ τ.injective]
    change x.residueFieldEquiv (x.P.residue f) = 0 ↔ _
    rw [map_eq_zero_iff _ x.residueFieldEquiv.injective, Place.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

omit [IsCurveField K] in
theorem pointEPlace_val_of_mem (x : QbarPoint K) (τ : x.fieldOf →+* E) {f : K}
    (hf : f ∈ x.P.1) : (pointEPlace x τ).val f = some (τ (evalF x ⟨f, hf⟩)) :=
  EPlace.val_of_mem _ hf

end EPlaces

/-- The degree over `ℚ_p` of the image of an algebraic number of degree `≤ d`. -/
theorem natDegree_minpoly_padic_le {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    (τ : F →+* PadicAlgCl p) (a : F) :
    (minpoly ℚ_[p] (τ a)).natDegree ≤ Module.finrank ℚ F := by
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hne : (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have hdvd : minpoly ℚ_[p] (τ a) ∣ (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) := by
    refine minpoly.dvd _ _ ?_
    rw [Polynomial.aeval_map_algebraMap]
    have := congrArg τ.toRatAlgHom (minpoly.aeval ℚ a)
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at this
    exact this
  calc (minpoly ℚ_[p] (τ a)).natDegree
      ≤ ((minpoly ℚ a).map (algebraMap ℚ ℚ_[p])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
    _ = (minpoly ℚ a).natDegree := Polynomial.natDegree_map _
    _ ≤ Module.finrank ℚ F := minpoly.natDegree_le a

/-- Curve fields are countable. -/
theorem countable_of_isCurveField : Countable K := by
  obtain ⟨t, ht, -⟩ := IsCurveField.exists_finite (K := K)
  haveI : FiniteDimensional ℚ⟮t⟯ K := finiteDimensional_adjoin ht
  haveI : Countable (Polynomial ℚ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Polynomial.cardinalMk_le_max (R := ℚ)).trans (by simp)
  haveI : Countable ℚ⟮t⟯ := by
    have hsurj : Function.Surjective fun pq : Polynomial ℚ × Polynomial ℚ =>
        (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) pq.1 /
          Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) pq.2 : ℚ⟮t⟯) := by
      rintro ⟨y, hy⟩
      obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ y).mp hy
      refine ⟨(r, s), Subtype.ext ?_⟩
      change ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) r : ℚ⟮t⟯) : K) /
          ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) s : ℚ⟮t⟯) : K) = _
      have h1 : ∀ f : Polynomial ℚ,
          ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) f : ℚ⟮t⟯) : K) =
            Polynomial.aeval t f := fun f => by
        have := Polynomial.aeval_algHom_apply (IntermediateField.val ℚ⟮t⟯)
          (IntermediateField.AdjoinSimple.gen ℚ t) f
        exact this.symm
      rw [h1, h1]
    exact hsurj.countable
  exact Finsupp.Countable.of_moduleFinite (R := ℚ⟮t⟯) (M := K)

/-! ### Enumerating embeddings -/

/-- A surjection `Fin d → (ℚ(x) →+* E)` onto the embeddings of the field of definition of a
point of degree `≤ d`. -/
theorem exists_surj_embeddings {E : Type*} [Field E] [CharZero E] [IsAlgClosed E]
    (x : QbarPoint K) {d : ℕ} (hd : x.deg ≤ d) :
    ∃ e : Fin d → (x.fieldOf →+* E), Function.Surjective e := by
  have hcard : Fintype.card (x.fieldOf →+* E) ≤ d := by
    rw [NumberField.Embeddings.card]
    exact hd
  haveI : Nonempty (x.fieldOf →+* E) := inferInstance
  refine ⟨fun i => if h : (i : ℕ) < Fintype.card (x.fieldOf →+* E) then
      (Fintype.equivFin (x.fieldOf →+* E)).symm ⟨i, h⟩ else Classical.arbitrary _, fun τ => ?_⟩
  set j := Fintype.equivFin (x.fieldOf →+* E) τ
  refine ⟨⟨j, lt_of_lt_of_le j.2 hcard⟩, ?_⟩
  simp only [j.2, dif_pos]
  exact (Fintype.equivFin (x.fieldOf →+* E)).symm_apply_apply τ

/-! ### Limit places -/

section LimitPlaces

variable {E : Type*} [NormedField E] [CharZero E]

omit [IsCurveField K] in
/-- `E`-valued places map rational numbers to themselves. -/
theorem EPlace.val_ratCast (y : EPlace K E) (hQ : ∀ q : ℚ, (q : K) ∈ y.O) (q : ℚ) :
    y.val (q : K) = some (q : E) := by
  rw [EPlace.val_of_mem y (hQ q)]
  congr 1
  have hden : ((q.den : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have h1 : y.ψ ⟨(q : K), hQ q⟩ * (q.den : E) = (q.num : E) := by
    have h2 : (⟨(q : K), hQ q⟩ : y.O) * (q.den : y.O) = (q.num : y.O) := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_intCast]
      exact_mod_cast Rat.mul_den_eq_num q
    have := congrArg y.ψ h2
    rwa [map_mul, map_natCast, map_intCast] at this
  have hq : (q : E) = (q.num : E) / (q.den : E) := Rat.cast_def q
  rw [hq, eq_div_iff hden]
  exact h1

variable {y : ℕ → EPlace K E} {ξ : K → Option E}

omit [IsCurveField K] in
/-- The limit of a convergent sequence of `E`-valued places with `ℚ ⊆ O` contains `ℚ`. -/
theorem ratCast_mem_limitSubring (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) (q : ℚ) : (q : K) ∈ limitSubring h := by
  rw [mem_limitSubring]
  have : ξ (q : K) = some (q : E) := (h (q : K)).unique
    ((tendstoP1_some_iff' (E := E)).mpr ⟨fun _ => (q : E),
      Eventually.of_forall fun n => EPlace.val_ratCast (y n) (hQ n) q, tendsto_const_nhds⟩)
  rw [this]
  exact Option.some_ne_none _

open Classical in
/-- The limit place (if the limit valuation ring is not everything). -/
noncomputable def limitPlace (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) : Option (Place K) :=
  if hT : limitSubring h = ⊤ then none
  else some ⟨limitSubring h, hT, ratCast_mem_limitSubring hQ h⟩

omit [IsCurveField K] in
/-- **Bounds away from `0`, `1`, `∞` along a convergent sequence**, for a function which is
regular, invertible, and with `φ − 1` invertible, at the limit place. -/
theorem eventually_bounded_of_limitPlace (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) {φ : K} (hφ0 : φ ≠ 0) (hφ1 : φ ≠ 1)
    (hP : ∀ P, limitPlace hQ h = some P → φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (y n).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := by
  have hmem : ∀ g, (g = φ ∨ g = φ⁻¹ ∨ g = (φ - 1)⁻¹) → ξ g ≠ none := by
    intro g hg
    rw [← mem_limitSubring h]
    by_cases hT : limitSubring h = ⊤
    · rw [hT]
      exact ValuationSubring.mem_top g
    · have := hP ⟨limitSubring h, hT, ratCast_mem_limitSubring hQ h⟩ (by
        simp only [limitPlace, dif_neg hT])
      rcases hg with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2
  obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (hmem φ (Or.inl rfl))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hmem φ⁻¹ (Or.inr (Or.inl rfl)) (limit_inv_of_eq_zero h hφ0 hβ)
  have hβ1 : β ≠ 1 := by
    rintro rfl
    have hm1 : ξ (-1) = some (-1) := limit_neg h (limit_one h)
    have h2 : ξ (φ - 1) = some 0 := by
      rw [sub_eq_add_neg, limit_add h hβ hm1, add_neg_cancel]
    exact hmem (φ - 1)⁻¹ (Or.inr (Or.inr rfl))
      (limit_inv_of_eq_zero h (sub_ne_zero.mpr hφ1) h2)
  exact eventually_abs_log_le h hβ hβ0 hβ1

end LimitPlaces

/-! ### The subsequence -/

section Subsequence

/-- One round of the diagonal argument, along a given subsequence. -/
theorem exists_subseq_limit {E : Type*} [NormedField E] {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    {d : ℕ} [NeZero d] (y : ℕ → Fin d → EPlace K E)
    (hgood : ∀ n i f α, (y n i).val f = some α → Good α) (D₀ : ℕ → ℕ) (hD₀ : StrictMono D₀) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ D = D₀ ∘ ψ) ∧
      ∃ ξ : Fin d → K → Option E, ∀ i f, TendstoP1 (fun n => (y (D n) i).val f) (ξ i f) := by
  haveI := countable_of_isCurveField (K := K)
  obtain ⟨ψ, hψ, ξ, hξ⟩ := exists_limit hcpt (fun n => y (D₀ n))
    (fun n i f α h => hgood _ _ _ _ h)
  exact ⟨D₀ ∘ ψ, hD₀.comp hψ, ⟨ψ, hψ, rfl⟩, ξ, hξ⟩

/-- Convergence is preserved along further subsequences. -/
theorem tendstoP1_comp_subseq {E : Type*} [NormedField E] {a : ℕ → Option E} {b : Option E}
    (h : TendstoP1 a b) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : TendstoP1 (a ∘ ψ) b :=
  h.comp_of_tendsto hψ.tendsto_atTop

end Subsequence

/-! ### The main compactness statement -/

section Main

/-- Primes carry their primality as an instance (local). -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

open Classical in
/-- **The compactness argument of [GenEll], Theorem 2.1**: for points `x_n` of degree `≤ d` and a
finite set `V` of primes, there are a subsequence and a finite set `T` of places of `K` (the
algebraic limit points at the places of `V ∪ {∞}`) such that every `φ ≠ 0, 1` regular and
invertible, with `φ − 1` invertible, at the places of `T` has values at all embeddings of the
fields of definition into `ℂ` and into `ℚ̄_p` (`p ∈ V`) bounded away from `0`, `1`, `∞`, along a
tail of the subsequence. -/
theorem exists_subseq_bounded (V : Finset Nat.Primes) {d : ℕ} (x : ℕ → QbarPoint K)
    (hx : ∀ n, (x n).deg ≤ d) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∃ T : Finset (Place K), ∀ φ : K, φ ≠ 0 → φ ≠ 1 →
      (∀ P ∈ T, φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) →
      ∃ C : ℝ, ∀ᶠ n in atTop, ∃ hφ : φ ∈ (x (D n)).P.1,
        evalF (x (D n)) ⟨φ, hφ⟩ ≠ 0 ∧ evalF (x (D n)) ⟨φ, hφ⟩ ≠ 1 ∧
        (∀ σ : (x (D n)).fieldOf →+* ℂ,
          |Real.log ‖σ (evalF (x (D n)) ⟨φ, hφ⟩)‖| ≤ C ∧
          |Real.log ‖σ (evalF (x (D n)) ⟨φ, hφ⟩) - 1‖| ≤ C) ∧
        ∀ p ∈ V, ∀ τ : (x (D n)).fieldOf →+* PadicAlgCl (p : ℕ),
          |Real.log ‖τ (evalF (x (D n)) ⟨φ, hφ⟩)‖| ≤ C ∧
          |Real.log ‖τ (evalF (x (D n)) ⟨φ, hφ⟩) - 1‖| ≤ C := by
  have hd : 0 < d := lt_of_lt_of_le (x 0).deg_pos (hx 0)
  haveI : NeZero d := ⟨hd.ne'⟩
  -- enumerate the embeddings
  choose eC heC using fun n => exists_surj_embeddings (E := ℂ) (x n) (hx n)
  choose eP heP using fun (p : Nat.Primes) n =>
    exists_surj_embeddings (E := PadicAlgCl (p : ℕ)) (x n) (hx n)
  set yC : ℕ → Fin d → EPlace K ℂ := fun n i => pointEPlace (x n) (eC n i) with hyC
  set yP : ∀ p : Nat.Primes, ℕ → Fin d → EPlace K (PadicAlgCl (p : ℕ)) :=
    fun p n i => pointEPlace (x n) (eP p n i) with hyP
  have hQ : ∀ n (q : ℚ), (q : K) ∈ (x n).P.1 := fun n q => (x n).P.ratCast_mem q
  have hgoodP : ∀ (p : Nat.Primes) n i f α, (yP p n i).val f = some α →
      (minpoly ℚ_[(p : ℕ)] α).natDegree ≤ d := by
    intro p n i f α h
    obtain ⟨hf, rfl⟩ := (EPlace.val_eq_some_iff _).mp h
    exact (natDegree_minpoly_padic_le _ _).trans (hx n)
  -- successive rounds
  have key : ∀ W : Finset Nat.Primes, ∃ D : ℕ → ℕ, StrictMono D ∧
      (∃ ξ : Fin d → K → Option ℂ, ∀ i f, TendstoP1 (fun n => (yC (D n) i).val f) (ξ i f)) ∧
      ∀ p ∈ W, ∃ ξ : Fin d → K → Option (PadicAlgCl (p : ℕ)),
        ∀ i f, TendstoP1 (fun n => (yP p (D n) i).val f) (ξ i f) := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      obtain ⟨D, hD, -, ξ, hξ⟩ := exists_subseq_limit (Good := fun _ : ℂ => True)
        (fun a _ => exists_tendsto_or_tendsto_norm_atTop a) yC (fun _ _ _ _ _ => trivial)
        id strictMono_id
      exact ⟨D, hD, ⟨ξ, hξ⟩, by simp⟩
    | insert p W hpW ih =>
      obtain ⟨D, hD, ⟨ξC, hξC⟩, hW⟩ := ih
      obtain ⟨D', hD', ⟨ψ, hψ, rfl⟩, ξ, hξ⟩ :=
        exists_subseq_limit (Good := fun α : PadicAlgCl (p : ℕ) =>
          (minpoly ℚ_[(p : ℕ)] α).natDegree ≤ d)
          (fun a ha => PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop d a ha) (yP p)
          (hgoodP p) D hD
      refine ⟨D ∘ ψ, hD', ⟨ξC, fun i f => tendstoP1_comp_subseq (hξC i f) hψ⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqW
      · exact ⟨ξ, hξ⟩
      · obtain ⟨ξq, hξq⟩ := hW q hqW
        exact ⟨ξq, fun i f => tendstoP1_comp_subseq (hξq i f) hψ⟩
  obtain ⟨D, hD, ⟨ξC, hC⟩, hPV⟩ := key V
  choose ξP hξP using hPV
  have hQC : ∀ i n (q : ℚ), (q : K) ∈ (yC (D n) i).O := fun i n q => hQ (D n) q
  have hQP : ∀ p i n (q : ℚ), (q : K) ∈ (yP p (D n) i).O := fun p i n q => hQ (D n) q
  -- the limit places
  set T : Finset (Place K) :=
    (Finset.univ.biUnion fun i => (limitPlace (hQC i) (hC i)).toFinset) ∪
      V.attach.biUnion fun p => Finset.univ.biUnion fun i =>
        (limitPlace (hQP p.1 i) (hξP p.1 p.2 i)).toFinset with hT
  refine ⟨D, hD, T, fun φ hφ0 hφ1 hφT => ?_⟩
  have hbC : ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (yC (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := fun i =>
    eventually_bounded_of_limitPlace (hQC i) (hC i) hφ0 hφ1 fun P hP => hφT P (by
      rw [hT, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inl ⟨i, Finset.mem_univ _, by simp [hP]⟩)
  have hbP : ∀ p : V, ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (yP p.1 (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := fun p i =>
    eventually_bounded_of_limitPlace (hQP p.1 i) (hξP p.1 p.2 i) hφ0 hφ1 fun P hP => hφT P (by
      rw [hT, Finset.mem_union, Finset.mem_biUnion]
      right
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_attach _ _, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hP]⟩⟩)
  choose CC hCC using hbC
  choose CP hCP using hbP
  set C : ℝ := ∑ i, |CC i| + ∑ p ∈ V.attach, ∑ i, |CP p i| with hCdef
  have hCC_le : ∀ i, CC i ≤ C := fun i => by
    have h1 : |CC i| ≤ ∑ i, |CC i| :=
      Finset.single_le_sum (f := fun i => |CC i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ p ∈ V.attach, ∑ i, |CP p i| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (CC i)]
  have hCP_le : ∀ p i, CP p i ≤ C := fun p i => by
    have h1 : |CP p i| ≤ ∑ i, |CP p i| :=
      Finset.single_le_sum (f := fun i => |CP p i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |CP p i| ≤ ∑ p ∈ V.attach, ∑ i, |CP p i| :=
      Finset.single_le_sum (f := fun p => ∑ i, |CP p i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_attach _ p)
    have h3 : 0 ≤ ∑ i, |CC i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (CP p i)]
  refine ⟨C, ?_⟩
  have hevC := Filter.eventually_all.mpr hCC
  have hevP : ∀ᶠ n in atTop, ∀ p ∈ V.attach, ∀ i, ∃ α, (yP p.1 (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ CP p i ∧ |Real.log ‖α - 1‖| ≤ CP p i ∧ α ≠ 0 ∧ α ≠ 1 :=
    (Filter.eventually_all_finset _).mpr fun p _ => Filter.eventually_all.mpr (hCP p)
  filter_upwards [hevC, hevP] with n hnC hnP
  obtain ⟨α₀, hα₀, -, -, hα₀0, hα₀1⟩ := hnC ⟨0, hd⟩
  obtain ⟨hφmem, hα₀eq⟩ := (EPlace.val_eq_some_iff _).mp hα₀
  have hv0 : evalF (x (D n)) ⟨φ, hφmem⟩ ≠ 0 := fun h0 => hα₀0 (by
    rw [← hα₀eq]
    change eC (D n) ⟨0, hd⟩ (evalF (x (D n)) ⟨φ, hφmem⟩) = 0
    rw [h0, map_zero])
  have hv1 : evalF (x (D n)) ⟨φ, hφmem⟩ ≠ 1 := fun h0 => hα₀1 (by
    rw [← hα₀eq]
    change eC (D n) ⟨0, hd⟩ (evalF (x (D n)) ⟨φ, hφmem⟩) = 1
    rw [h0, map_one])
  refine ⟨hφmem, hv0, hv1, fun σ => ?_, fun p hp τ => ?_⟩
  · obtain ⟨i, rfl⟩ := heC (D n) σ
    obtain ⟨α, hα, h1, h2, -, -⟩ := hnC i
    rw [show (yC (D n) i).val φ = some (eC (D n) i (evalF (x (D n)) ⟨φ, hφmem⟩)) from
      pointEPlace_val_of_mem _ _ hφmem] at hα
    cases hα
    exact ⟨h1.trans (hCC_le i), h2.trans (hCC_le i)⟩
  · obtain ⟨i, rfl⟩ := heP p (D n) τ
    obtain ⟨α, hα, h1, h2, -, -⟩ := hnP ⟨p, hp⟩ (Finset.mem_attach _ _) i
    rw [show (yP p (D n) i).val φ = some (eP p (D n) i (evalF (x (D n)) ⟨φ, hφmem⟩)) from
      pointEPlace_val_of_mem _ _ hφmem] at hα
    cases hα
    exact ⟨h1.trans (hCP_le ⟨p, hp⟩ i), h2.trans (hCP_le ⟨p, hp⟩ i)⟩

end Main

end Heights.Curve
