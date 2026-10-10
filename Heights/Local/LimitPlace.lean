/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Limits of `E`-valued places along subsequences

Let `K` be a countable field and `E` a normed field. An *`E`-valued place* of `K` is a
valuation subring `O ⊆ K` together with a ring homomorphism `ψ : O → E` whose kernel is the
maximal ideal of `O`; it evaluates every `f ∈ K` to a point `val f ∈ ℙ¹(E) = Option E`
(`none` = `∞` for `f ∉ O`).

Given a sequence of families `x n i` (`i : ι`, `ι` finite) of `E`-valued places whose values
lie in a sequentially compact part of `ℙ¹(E)` (for `E = ℚ̄_p`: the points of degree `≤ d`
over `ℚ_p`, `Heights.Local.PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop`; for `E = ℂ`:
everything), a diagonal argument over the countable set `K × ι` produces a subsequence along
which `val (x n i) f` converges in `ℙ¹(E)` for every `f` and `i`. The limit `ξ i : K → ℙ¹(E)`
is again an `E`-valued place in the following sense: `O_ξ = {f | ξ f ≠ ∞}` is a valuation
subring of `K` containing the image of `ℚ`-like constants on which the sequence converges,
`ξ` is additive and multiplicative on `O_ξ`, and `ξ f = 0` iff `ξ f⁻¹ = ∞`
(`Heights.Local.LimitPlace`).

This is the compactness step of the proof of [GenEll], Theorem 2.1: the limit places `O_ξ`
(when `≠ K`) are the finitely many places at which the noncritical Belyi map must not meet
`{0, 1, ∞}`; if `O_ξ = K` every nonconstant function has a limit value in `E ∖ {0}`.

## Main definitions and results

* `Heights.Local.EPlace`: `E`-valued places, `EPlace.val`.
* `Heights.Local.TendstoP1`: convergence in `ℙ¹(E)`.
* `Heights.Local.exists_diagonal`: the diagonal subsequence.
* `Heights.Local.LimitPlace`: the limit valuation subring and its properties.
-/

namespace Heights.Local

open Filter Topology

section Convergence

variable {E : Type*} [NormedField E]

/-- Convergence of a sequence of points of `ℙ¹(E) = Option E` (`none = ∞`). -/
def TendstoP1 (a : ℕ → Option E) : Option E → Prop
  | some β => ∀ ε > 0, ∀ᶠ n in atTop, ∃ α, a n = some α ∧ ‖α - β‖ < ε
  | none => ∀ R : ℝ, ∀ᶠ n in atTop, ∀ α, a n = some α → R < ‖α‖

theorem TendstoP1.comp_of_tendsto {a : ℕ → Option E} {b : Option E} (h : TendstoP1 a b)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) : TendstoP1 (a ∘ φ) b := by
  cases b with
  | none => exact fun R => hφ.eventually (h R)
  | some β => exact fun ε hε => hφ.eventually (h ε hε)

/-- Convergence only depends on the tail. -/
theorem TendstoP1.congr_eventually {a a' : ℕ → Option E} {b : Option E} (h : TendstoP1 a b)
    (h' : ∀ᶠ n in atTop, a n = a' n) : TendstoP1 a' b := by
  cases b with
  | none =>
    intro R
    filter_upwards [h R, h'] with n hn hn' α hα
    exact hn α (hn'.trans hα)
  | some β =>
    intro ε hε
    filter_upwards [h ε hε, h'] with n hn hn'
    obtain ⟨α, hα, hlt⟩ := hn
    exact ⟨α, hn' ▸ hα, hlt⟩

/-- Limits in `ℙ¹(E)` are unique. -/
theorem TendstoP1.unique {a : ℕ → Option E} {b b' : Option E} (h : TendstoP1 a b)
    (h' : TendstoP1 a b') : b = b' := by
  cases b with
  | none =>
    cases b' with
    | none => rfl
    | some β' =>
      exfalso
      obtain ⟨n, hn⟩ := ((h (‖β'‖ + 1)).and (h' 1 one_pos)).exists
      obtain ⟨α, hα, hlt⟩ := hn.2
      have h1 := hn.1 α hα
      have : ‖α‖ ≤ ‖β'‖ + ‖α - β'‖ := by
        calc ‖α‖ = ‖β' + (α - β')‖ := by rw [add_sub_cancel]
          _ ≤ ‖β'‖ + ‖α - β'‖ := norm_add_le _ _
      linarith
  | some β =>
    cases b' with
    | none =>
      exfalso
      obtain ⟨n, hn⟩ := ((h' (‖β‖ + 1)).and (h 1 one_pos)).exists
      obtain ⟨α, hα, hlt⟩ := hn.2
      have h1 := hn.1 α hα
      have : ‖α‖ ≤ ‖β‖ + ‖α - β‖ := by
        calc ‖α‖ = ‖β + (α - β)‖ := by rw [add_sub_cancel]
          _ ≤ ‖β‖ + ‖α - β‖ := norm_add_le _ _
      linarith
    | some β' =>
      congr 1
      by_contra hne
      have hd : 0 < ‖β - β'‖ / 2 := by
        have : 0 < ‖β - β'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        linarith
      obtain ⟨n, hn⟩ := ((h _ hd).and (h' _ hd)).exists
      obtain ⟨α, hα, hlt⟩ := hn.1
      obtain ⟨α', hα', hlt'⟩ := hn.2
      rw [hα] at hα'
      cases hα'
      have : ‖β - β'‖ ≤ ‖α - β‖ + ‖α - β'‖ := by
        calc ‖β - β'‖ = ‖(α - β') - (α - β)‖ := by congr 1; ring
          _ ≤ ‖α - β'‖ + ‖α - β‖ := norm_sub_le _ _
          _ = ‖α - β‖ + ‖α - β'‖ := add_comm _ _
      linarith

/-- Convergence to a finite value, in terms of `Tendsto`. -/
theorem tendstoP1_some_iff {a : ℕ → E} {β : E} :
    TendstoP1 (fun n => some (a n)) (some β) ↔ Tendsto a atTop (𝓝 β) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨α, hα, hlt⟩ := hN n hn
    cases hα
    rwa [dist_eq_norm]
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact eventually_atTop.mpr ⟨N, fun n hn => ⟨a n, rfl, by rw [← dist_eq_norm]; exact hN n hn⟩⟩

/-- **Sequential compactness in `ℙ¹(E)`**, from the dichotomy "convergent or unbounded" for
the finite values in a class `Good`. -/
theorem exists_tendstoP1 {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    (a : ℕ → Option E) (ha : ∀ n α, a n = some α → Good α) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b, TendstoP1 (a ∘ φ) b := by
  by_cases hinf : (setOf fun n => a n = none).Infinite
  · refine ⟨Nat.nth (fun n => a n = none), Nat.nth_strictMono hinf, none, fun R => ?_⟩
    exact Eventually.of_forall fun n α hα => by
      have : a (Nat.nth (fun n => a n = none) n) = none := Nat.nth_mem_of_infinite hinf n
      simp only [Function.comp] at hα
      rw [this] at hα
      cases hα
  · -- eventually all values are finite
    obtain ⟨N, hN⟩ := (Set.not_infinite.mp hinf).bddAbove
    have hsome : ∀ n, ∃ α, a (n + N + 1) = some α := by
      intro n
      cases h : a (n + N + 1) with
      | none =>
        have := hN (show n + N + 1 ∈ setOf fun n => a n = none from h)
        omega
      | some α => exact ⟨α, rfl⟩
    choose α hα using hsome
    obtain ⟨φ, hφ, hlim⟩ := hcpt α (fun n => ha _ _ (hα n))
    have hmono : StrictMono (fun n => φ n + N + 1) := fun m n hmn => by
      have := hφ hmn
      change φ m + N + 1 < φ n + N + 1
      omega
    refine ⟨fun n => φ n + N + 1, hmono, ?_⟩
    rcases hlim with ⟨b, hb⟩ | hinfty
    · refine ⟨some b, ?_⟩
      have : TendstoP1 (fun n => some (α (φ n))) (some b) := tendstoP1_some_iff.mpr hb
      refine this.congr_eventually (Eventually.of_forall fun n => ?_)
      simp [hα]
    · refine ⟨none, fun R => ?_⟩
      filter_upwards [hinfty.eventually_gt_atTop R] with n hn β hβ
      simp only [Function.comp, hα] at hβ
      cases hβ
      exact hn

end Convergence

section Diagonal

/-- A family of strictly monotone maps refining each other. -/
theorem exists_diagonal {P : ℕ → (ℕ → ℕ) → Prop}
    (hP : ∀ k (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P k (φ ∘ ψ)) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∀ k, ∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
      ∃ φ : ℕ → ℕ, P k φ ∧ ∀ n, k < n → D n = φ (χ n) := by
  classical
  -- the refining sequence
  let step : ℕ → {φ : ℕ → ℕ // StrictMono φ} → {φ : ℕ → ℕ // StrictMono φ} :=
    fun k φ => ⟨φ.1 ∘ (hP k φ.1 φ.2).choose, φ.2.comp (hP k φ.1 φ.2).choose_spec.1⟩
  let Φ : ℕ → {φ : ℕ → ℕ // StrictMono φ} := fun n =>
    Nat.rec ⟨id, strictMono_id⟩ (fun k φ => step k φ) n
  have hΦsucc : ∀ k, Φ (k + 1) = step k (Φ k) := fun k => rfl
  have hstepP : ∀ k, P k (Φ (k + 1)).1 := fun k => by
    rw [hΦsucc]
    exact (hP k (Φ k).1 (Φ k).2).choose_spec.2
  -- `Φ n = Φ k ∘ ρ` with `ρ` strictly monotone, for `k ≤ n`
  have hrefine : ∀ k n, k ≤ n → ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ (Φ n).1 = (Φ k).1 ∘ ρ := by
    intro k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ n hkn ih =>
      obtain ⟨ρ, hρ, hΦ⟩ := ih
      refine ⟨ρ ∘ (hP n (Φ n).1 (Φ n).2).choose, hρ.comp
        (hP n (Φ n).1 (Φ n).2).choose_spec.1, ?_⟩
      rw [hΦsucc]
      change (Φ n).1 ∘ _ = _
      funext m
      exact congrFun hΦ _
  set D : ℕ → ℕ := fun n => (Φ n).1 n with hD
  have hDmono : StrictMono D := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    obtain ⟨ρ, hρ, hΦ⟩ := hrefine n (n + 1) (Nat.le_succ n)
    change (Φ n).1 n < (Φ (n + 1)).1 (n + 1)
    rw [hΦ]
    exact (Φ n).2 (lt_of_lt_of_le (Nat.lt_succ_self n) (hρ.id_le (n + 1)))
  refine ⟨D, hDmono, fun k => ?_⟩
  -- along `D`, eventually a subsequence of `Φ (k+1)`
  choose ρ hρ hΦρ using fun n => (fun h => hrefine (k + 1) (max n (k + 1)) h)
    (le_max_right n (k + 1))
  refine ⟨fun n => ρ n (max n (k + 1)), ?_, (Φ (k + 1)).1, hstepP k, fun n hkn => ?_⟩
  · refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact (le_max_left n (k + 1)).trans ((hρ n).id_le _)
  · change (Φ n).1 n = (Φ (k + 1)).1 (ρ n (max n (k + 1)))
    have hn : k + 1 ≤ n := hkn
    have := congrFun (hΦρ n) n
    simp only [Function.comp] at this
    rw [max_eq_left hn] at this ⊢
    exact this

end Diagonal

section EPlace

variable {K : Type*} [Field K] {E : Type*} [NormedField E]

/-- An `E`-valued place of `K`: a valuation subring with a ring homomorphism to `E` whose
kernel is the maximal ideal. -/
structure EPlace (K E : Type*) [Field K] [NormedField E] where
  /-- The valuation subring. -/
  O : ValuationSubring K
  /-- The evaluation map. -/
  ψ : O →+* E
  /-- The kernel of `ψ` consists of the nonunits. -/
  eq_zero_iff : ∀ f : O, ψ f = 0 ↔ ¬ IsUnit f

namespace EPlace

open Classical in
/-- The value `f(x) ∈ ℙ¹(E)` of `f ∈ K` at an `E`-valued place (`none = ∞`). -/
noncomputable def val (x : EPlace K E) (f : K) : Option E :=
  if h : f ∈ x.O then some (x.ψ ⟨f, h⟩) else none

theorem val_of_mem (x : EPlace K E) {f : K} (h : f ∈ x.O) : x.val f = some (x.ψ ⟨f, h⟩) := by
  simp [val, h]

theorem val_of_notMem (x : EPlace K E) {f : K} (h : f ∉ x.O) : x.val f = none := by
  simp [val, h]

theorem val_eq_some_iff (x : EPlace K E) {f : K} {α : E} :
    x.val f = some α ↔ ∃ h : f ∈ x.O, x.ψ ⟨f, h⟩ = α := by
  by_cases h : f ∈ x.O
  · simp [val, h]
  · simp [val, h]

theorem val_add (x : EPlace K E) {f g : K} {α β : E} (hf : x.val f = some α)
    (hg : x.val g = some β) : x.val (f + g) = some (α + β) := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  obtain ⟨hg', rfl⟩ := (val_eq_some_iff x).mp hg
  rw [val_of_mem x (add_mem hf' hg')]
  congr 1
  rw [← map_add]
  rfl

theorem val_mul (x : EPlace K E) {f g : K} {α β : E} (hf : x.val f = some α)
    (hg : x.val g = some β) : x.val (f * g) = some (α * β) := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  obtain ⟨hg', rfl⟩ := (val_eq_some_iff x).mp hg
  rw [val_of_mem x (mul_mem hf' hg')]
  congr 1
  rw [← map_mul]
  rfl

theorem val_neg (x : EPlace K E) {f : K} {α : E} (hf : x.val f = some α) :
    x.val (-f) = some (-α) := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  rw [val_of_mem x (neg_mem hf')]
  congr 1
  rw [← map_neg]
  rfl

theorem val_one (x : EPlace K E) : x.val 1 = some 1 := by
  rw [val_of_mem x (one_mem _)]
  congr 1
  exact map_one x.ψ

theorem val_zero (x : EPlace K E) : x.val 0 = some 0 := by
  rw [val_of_mem x (zero_mem _)]
  congr 1
  exact map_zero x.ψ

/-- Inversion: if `f(x) = α ≠ 0` then `f⁻¹(x) = α⁻¹`. -/
theorem val_inv_of_ne_zero (x : EPlace K E) {f : K} {α : E} (hf : x.val f = some α)
    (hα : α ≠ 0) : x.val f⁻¹ = some α⁻¹ := by
  obtain ⟨hf', rfl⟩ := (val_eq_some_iff x).mp hf
  have hunit : IsUnit (⟨f, hf'⟩ : x.O) := by
    by_contra h
    exact hα ((x.eq_zero_iff _).mpr h)
  obtain ⟨g, hg⟩ := hunit.exists_right_inv
  have hfg : f * (g : K) = 1 := congrArg Subtype.val hg
  have hf0 : f ≠ 0 := left_ne_zero_of_mul_eq_one hfg
  have hgf : (g : K) = f⁻¹ := eq_inv_of_mul_eq_one_right hfg
  have hinv : f⁻¹ ∈ x.O := hgf ▸ g.2
  rw [val_of_mem x hinv]
  congr 1
  have h1 : x.ψ ⟨f, hf'⟩ * x.ψ ⟨f⁻¹, hinv⟩ = 1 := by
    rw [← map_mul, ← map_one x.ψ]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ hf0)
  exact eq_inv_of_mul_eq_one_right h1

/-- If `f(x) = 0` with `f ≠ 0`, then `f⁻¹(x) = ∞`. -/
theorem val_inv_of_eq_zero (x : EPlace K E) {f : K} (hf0 : f ≠ 0) (hf : x.val f = some 0) :
    x.val f⁻¹ = none := by
  obtain ⟨hf', hzero⟩ := (val_eq_some_iff x).mp hf
  have hnu : ¬ IsUnit (⟨f, hf'⟩ : x.O) := (x.eq_zero_iff _).mp hzero
  apply val_of_notMem
  intro hinv
  apply hnu
  exact ⟨⟨⟨f, hf'⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0),
    Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

/-- If `f(x) = ∞` then `f⁻¹(x) = 0`. -/
theorem val_inv_of_eq_none (x : EPlace K E) {f : K} (hf : x.val f = none) :
    x.val f⁻¹ = some 0 := by
  have hf' : f ∉ x.O := by
    intro h
    rw [val_of_mem x h] at hf
    cases hf
  have hinv : f⁻¹ ∈ x.O := (x.O.mem_or_inv_mem f).resolve_left hf'
  rw [val_of_mem x hinv]
  congr 1
  rw [x.eq_zero_iff]
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hfg : f⁻¹ * (g : K) = 1 := congrArg Subtype.val hg
  have hgf : (g : K) = f := by
    have := eq_inv_of_mul_eq_one_right hfg
    rwa [inv_inv] at this
  exact hf' (hgf ▸ g.2)

end EPlace

end EPlace

section Limit

variable {K : Type*} [Field K] {E : Type*} [NormedField E]

/-- Convergence to a finite value via eventually finite values. -/
theorem tendstoP1_some_iff' {a : ℕ → Option E} {β : E} :
    TendstoP1 a (some β) ↔ ∃ α : ℕ → E, (∀ᶠ n in atTop, a n = some (α n)) ∧
      Tendsto α atTop (𝓝 β) := by
  constructor
  · intro h
    have hev : ∀ᶠ n in atTop, ∃ α, a n = some α := by
      filter_upwards [h 1 one_pos] with n hn
      obtain ⟨α, hα, -⟩ := hn
      exact ⟨α, hα⟩
    classical
    let α : ℕ → E := fun n => if hn : ∃ α, a n = some α then hn.choose else 0
    have hα : ∀ᶠ n in atTop, a n = some (α n) := by
      filter_upwards [hev] with n hn
      simp only [α, dif_pos hn]
      exact hn.choose_spec
    refine ⟨α, hα, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((h ε hε).and hα)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨⟨α', hα', hlt⟩, hαn⟩ := hN n hn
    rw [hαn] at hα'
    cases hα'
    rwa [dist_eq_norm]
  · rintro ⟨α, hα, hlim⟩ ε hε
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim ε hε
    filter_upwards [hα, eventually_ge_atTop N] with n hn hnN
    exact ⟨α n, hn, by rw [← dist_eq_norm]; exact hN n hnN⟩

/-- **Diagonal subsequence**: for a sequence of families of `E`-valued places of a countable
field whose finite values lie in a sequentially compact class, there is a subsequence along
which all values converge in `ℙ¹(E)`. -/
theorem exists_limit [Countable K] {ι : Type*} [Countable ι] [Nonempty ι] {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    (x : ℕ → ι → EPlace K E) (hgood : ∀ n i f α, (x n i).val f = some α → Good α) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∃ ξ : ι → K → Option E,
      ∀ i f, TendstoP1 (fun n => (x (D n) i).val f) (ξ i f) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (ι × K)
  let P : ℕ → (ℕ → ℕ) → Prop := fun k φ =>
    ∃ b, TendstoP1 (fun n => (x (φ n) (e k).1).val (e k).2) b
  have hP : ∀ k (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P k (φ ∘ ψ) := by
    intro k φ _
    obtain ⟨ψ, hψ, b, hb⟩ := exists_tendstoP1 hcpt
      (fun n => (x (φ n) (e k).1).val (e k).2) (fun n α hα => hgood _ _ _ _ hα)
    exact ⟨ψ, hψ, b, hb⟩
  obtain ⟨D, hD, hDk⟩ := exists_diagonal hP
  have hlim : ∀ k, ∃ b, TendstoP1 (fun n => (x (D n) (e k).1).val (e k).2) b := by
    intro k
    obtain ⟨χ, hχ, φ, ⟨b, hb⟩, hDφ⟩ := hDk k
    refine ⟨b, (hb.comp_of_tendsto hχ).congr_eventually ?_⟩
    filter_upwards [eventually_gt_atTop k] with n hn
    simp only [Function.comp]
    rw [hDφ n hn]
  choose b hb using hlim
  refine ⟨D, hD, fun i f => b (he (i, f)).choose, fun i f => ?_⟩
  have := hb (he (i, f)).choose
  rw [(he (i, f)).choose_spec] at this
  exact this

variable {x : ℕ → EPlace K E} {ξ : K → Option E}

/-- Limits of values are additive. -/
theorem limit_add (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f g : K} {α β : E}
    (hf : ξ f = some α) (hg : ξ g = some β) : ξ (f + g) = some (α + β) := by
  have hf' := h f
  have hg' := h g
  rw [hf, tendstoP1_some_iff'] at hf'
  rw [hg, tendstoP1_some_iff'] at hg'
  obtain ⟨a, ha, hla⟩ := hf'
  obtain ⟨b, hb, hlb⟩ := hg'
  refine (h (f + g)).unique (tendstoP1_some_iff'.mpr ⟨fun n => a n + b n, ?_, hla.add hlb⟩)
  filter_upwards [ha, hb] with n hna hnb
  exact (x n).val_add hna hnb

/-- Limits of values are multiplicative. -/
theorem limit_mul (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f g : K} {α β : E}
    (hf : ξ f = some α) (hg : ξ g = some β) : ξ (f * g) = some (α * β) := by
  have hf' := h f
  have hg' := h g
  rw [hf, tendstoP1_some_iff'] at hf'
  rw [hg, tendstoP1_some_iff'] at hg'
  obtain ⟨a, ha, hla⟩ := hf'
  obtain ⟨b, hb, hlb⟩ := hg'
  refine (h (f * g)).unique (tendstoP1_some_iff'.mpr ⟨fun n => a n * b n, ?_, hla.mul hlb⟩)
  filter_upwards [ha, hb] with n hna hnb
  exact (x n).val_mul hna hnb

theorem limit_neg (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} {α : E}
    (hf : ξ f = some α) : ξ (-f) = some (-α) := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  refine (h (-f)).unique (tendstoP1_some_iff'.mpr ⟨fun n => -a n, ?_, hla.neg⟩)
  filter_upwards [ha] with n hna
  exact (x n).val_neg hna

theorem limit_one (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ξ 1 = some 1 :=
  (h 1).unique (tendstoP1_some_iff'.mpr ⟨fun _ => 1,
    Eventually.of_forall fun n => (x n).val_one, tendsto_const_nhds⟩)

theorem limit_zero (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ξ 0 = some 0 :=
  (h 0).unique (tendstoP1_some_iff'.mpr ⟨fun _ => 0,
    Eventually.of_forall fun n => (x n).val_zero, tendsto_const_nhds⟩)

/-- `ξ f = 0` implies `ξ f⁻¹ = ∞`. -/
theorem limit_inv_of_eq_zero (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K}
    (hf0 : f ≠ 0) (hf : ξ f = some 0) : ξ f⁻¹ = none := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  refine (h f⁻¹).unique fun R => ?_
  have hsmall : ∀ᶠ n in atTop, ‖a n‖ < (max R 1)⁻¹ := by
    have := (tendsto_norm_zero.comp hla).eventually (gt_mem_nhds (a := (max R 1)⁻¹)
      (by positivity))
    simpa using this
  filter_upwards [ha, hsmall] with n hn hsm α hα
  by_cases h0 : a n = 0
  · rw [h0] at hn
    rw [(x n).val_inv_of_eq_zero hf0 hn] at hα
    cases hα
  · rw [(x n).val_inv_of_ne_zero hn h0] at hα
    cases hα
    rw [norm_inv]
    have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr h0
    have h1 : 1 ≤ max R 1 := le_max_right _ _
    have h2 : max R 1 < ‖a n‖⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) hpos]
      exact hsm
    exact lt_of_le_of_lt (le_max_left _ _) h2

/-- `ξ f = ∞` implies `ξ f⁻¹ = 0`. -/
theorem limit_inv_of_eq_none (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K}
    (hf : ξ f = none) : ξ f⁻¹ = some 0 := by
  have hf' := h f
  rw [hf] at hf'
  refine (h f⁻¹).unique (fun ε hε => ?_)
  filter_upwards [hf' ε⁻¹] with n hn
  cases hv : (x n).val f with
  | none => exact ⟨0, (x n).val_inv_of_eq_none hv, by simpa using hε⟩
  | some α =>
    have hα := hn α hv
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp only [norm_zero] at hα
      have : 0 < ε⁻¹ := inv_pos.mpr hε
      linarith
    refine ⟨α⁻¹, (x n).val_inv_of_ne_zero hv hα0, ?_⟩
    rw [sub_zero, norm_inv]
    exact (inv_lt_comm₀ hε (norm_pos_iff.mpr hα0)).mp hα

/-- **The limit valuation subring** `O_ξ = {f | ξ f ≠ ∞}`. -/
def limitSubring (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ValuationSubring K where
  carrier := {f | ξ f ≠ none}
  add_mem' {f g} hf hg := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hg
    simp [limit_add h hα hβ]
  zero_mem' := by simp [limit_zero h]
  mul_mem' {f g} hf hg := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hg
    simp [limit_mul h hα hβ]
  one_mem' := by simp [limit_one h]
  neg_mem' {f} hf := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    simp [limit_neg h hα]
  mem_or_inv_mem' f := by
    by_cases hf : ξ f = none
    · right
      simp [limit_inv_of_eq_none h hf]
    · exact Or.inl hf

theorem mem_limitSubring (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} :
    f ∈ limitSubring h ↔ ξ f ≠ none := Iff.rfl

/-- **Bounds away from `0`, `1`, `∞`**: if `ξ f ∉ {0, 1, ∞}`, then eventually
`|log ‖f(x n)‖|` and `|log ‖f(x n) − 1‖|` are bounded. -/
theorem eventually_abs_log_le (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} {β : E}
    (hf : ξ f = some β) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (x n).val f = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  have hb0 : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
  have hb1 : 0 < ‖β - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hβ1)
  set δ := min ‖β‖ ‖β - 1‖ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hclose : ∀ᶠ n in atTop, ‖a n - β‖ < δ := by
    have := (Metric.tendsto_nhds.mp hla) δ hδpos
    simpa [dist_eq_norm] using this
  refine ⟨max (|Real.log (‖β‖ / 2)|) (|Real.log (‖β‖ * 2)|) +
    max (|Real.log (‖β - 1‖ / 2)|) (|Real.log (‖β - 1‖ * 2)|), ?_⟩
  filter_upwards [ha, hclose] with n hn hc
  have hδ1 : δ ≤ ‖β‖ / 2 := by
    rw [hδ]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ ‖β - 1‖ / 2 := by
    rw [hδ]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlog : ∀ {t A B : ℝ}, 0 < A → A ≤ t → t ≤ B → |Real.log t| ≤ max |Real.log A| |Real.log B| :=
    fun {t A B} hA hAt htB => abs_le_max_abs_abs (Real.log_le_log hA hAt)
      (Real.log_le_log (hA.trans_le hAt) htB)
  have hnear : ∀ {u v : E}, ‖u - v‖ < ‖v‖ / 2 → ‖v‖ / 2 ≤ ‖u‖ ∧ ‖u‖ ≤ ‖v‖ * 2 := by
    intro u v huv
    have h1 : ‖v‖ ≤ ‖u‖ + ‖u - v‖ := by
      calc ‖v‖ = ‖u - (u - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - v‖ := norm_sub_le _ _
    have h2 : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
      calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
        _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
    constructor <;> nlinarith [norm_nonneg v, norm_nonneg (u - v)]
  obtain ⟨h1, h2⟩ := hnear (u := a n) (v := β) (lt_of_lt_of_le hc hδ1)
  have hc' : ‖(a n - 1) - (β - 1)‖ < ‖β - 1‖ / 2 := by
    rw [sub_sub_sub_cancel_right]
    exact lt_of_lt_of_le hc hδ2
  obtain ⟨h3, h4⟩ := hnear hc'
  refine ⟨a n, hn, ?_, ?_, ?_, ?_⟩
  · have := hlog (by positivity) h1 h2
    have h0 : 0 ≤ max |Real.log (‖β - 1‖ / 2)| |Real.log (‖β - 1‖ * 2)| :=
      le_max_of_le_left (abs_nonneg _)
    linarith
  · have := hlog (by positivity) h3 h4
    have h0 : 0 ≤ max |Real.log (‖β‖ / 2)| |Real.log (‖β‖ * 2)| :=
      le_max_of_le_left (abs_nonneg _)
    linarith
  · intro h0
    rw [h0, norm_zero] at h1
    linarith
  · intro h0
    rw [h0, sub_self, norm_zero] at h3
    linarith

end Limit

end Heights.Local
