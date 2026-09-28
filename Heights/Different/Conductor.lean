/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Heights.Different.Places

/-!
# Log-conductors along extensions of number fields

For a number field `F` and a finite set `G ⊆ F`, the finite places *meeting* `G` are those
`w` with `1 < w g` for some `g ∈ G` (the poles of the elements of `G`;
`Heights.Different.meets G`), and the (normalised) *log-conductor* of `G` is
`cond G = (∑_{w ∈ meets G} log N(w)) / [F : ℚ]` (`Heights.Different.cond`), a finite sum by
`Heights.Different.meets_finite`.

The main result is the comparison of log-conductors along a finite extension, the number-field
core of the first half of [GenEll] Proposition 1.7 (S. Mochizuki, *Arithmetic elliptic curves
in general position*): for `[Algebra F L]`, `G' ⊆ F`, `G ⊆ L` with `G' ⊆ G`,

* `Heights.Different.cond_le_cond_add`:
  `cond G' ≤ cond G + log N(𝔇_{L/F}) / [L : ℚ]`;
* `Heights.Different.logDisc_add_cond_le`: `logDisc F + cond G' ≤ logDisc L + cond G`.

The proof is local: for a place `u` of `F` meeting `G'`, every place `w ∣ u` of `L` meets `G`
(`w(a) = u(a)^{e f}`), and
`log N(u)/[F : ℚ] = ∑_{w ∣ u} e f log N(u)/[L : ℚ] = ∑_{w ∣ u} log N(w)/[L : ℚ] +
∑_{w ∣ u} (e − 1) f log N(u)/[L : ℚ]`, where the last sum is at most the contribution
`diffContrib L u` of `u` to the different (`Heights.Different.sum_le_diffContrib`).
-/

namespace Heights.Different

open NumberField IsDedekindDomain Module

/-! ### The places meeting a finite set and the log-conductor -/

section Meets

variable {K : Type*} [Field K] [NumberField K]

/-- The finite places at which some element of `G` has a pole: `{w | ∃ g ∈ G, 1 < w g}`. -/
def meets (G : Finset K) : Set (FinitePlace K) := {w | ∃ g ∈ G, 1 < w g}

/-- Only finitely many finite places meet a finite set. -/
theorem meets_finite (G : Finset K) : (meets G).Finite := by
  have h : meets G = ⋃ g ∈ G, {w : FinitePlace K | 1 < w g} := by
    ext w
    simp [meets]
  rw [h]
  refine Set.Finite.biUnion G.finite_toSet fun g _ => ?_
  by_cases hg : g = 0
  · subst hg
    refine Set.finite_empty.subset fun w (hw : 1 < w 0) => ?_
    rw [map_zero] at hw
    exact absurd hw (by norm_num)
  · refine (FinitePlace.hasFiniteMulSupport hg).subset fun w hw => ?_
    exact ne_of_gt hw

/-- `meets G` as a finset. -/
noncomputable def meetsFinset (G : Finset K) : Finset (FinitePlace K) := (meets_finite G).toFinset

lemma mem_meetsFinset {G : Finset K} {w : FinitePlace K} :
    w ∈ meetsFinset G ↔ ∃ g ∈ G, 1 < w g := by
  rw [meetsFinset, Set.Finite.mem_toFinset]
  rfl

open scoped Classical in
/-- The log-conductor of a finite set `G ⊆ K`:
`cond G = (∑ᶠ w, [w ∈ meets G]·log N(w)) / [K : ℚ]`, with `N(w) = placeNorm w =
Ideal.absNorm w.maximalIdeal.asIdeal`. -/
noncomputable def cond (G : Finset K) : ℝ :=
  (∑ᶠ w : FinitePlace K, if w ∈ meets G then Real.log (placeNorm w) else 0) / finrank ℚ K

/-- `cond G` as a finite sum over the places meeting `G`. -/
theorem cond_eq_sum (G : Finset K) :
    cond G = (∑ w ∈ meetsFinset G, Real.log (placeNorm w)) / finrank ℚ K := by
  classical
  rw [cond, finsum_eq_sum_of_support_subset _ (s := meetsFinset G)]
  · congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [if_pos (by rw [mem_meetsFinset] at hw; exact hw)]
  · intro w hw
    rw [Function.mem_support] at hw
    rw [Finset.mem_coe, mem_meetsFinset]
    by_contra h
    exact hw (if_neg (by exact h))

lemma cond_nonneg (G : Finset K) : 0 ≤ cond G := by
  rw [cond_eq_sum]
  exact div_nonneg (Finset.sum_nonneg fun w _ => log_placeNorm_nonneg w) (by positivity)

end Meets

/-! ### The local comparison -/

section Local

variable {F : Type*} [Field F] [NumberField F] (L : Type*) [Field L] [NumberField L]
  [Algebra F L]

/-- **The local comparison at a place `u` of `F`**:
`log N(u)/[F : ℚ] ≤ ∑_{w ∣ u} log N(w)/[L : ℚ] + diffContrib L u`. -/
theorem log_placeNorm_div_le (u : FinitePlace F) :
    Real.log (placeNorm u) / finrank ℚ F ≤
      ∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
        diffContrib L u.maximalIdeal.asIdeal := by
  haveI := u.maximalIdeal.isMaximal
  set 𝔭 := u.maximalIdeal.asIdeal
  have hsum := sum_placesOver_mul_eq_finrank (L := L) u
  have hF := finrank_ℚ_pos F
  have hFL : (0 : ℝ) < finrank F L := by exact_mod_cast finrank_pos
  calc Real.log (placeNorm u) / finrank ℚ F
      = ∑ w ∈ placesOver L u, ((placeRamIdx w u * placeInertiaDeg w u : ℕ) : ℝ) *
          (Real.log (placeNorm u) / finrank ℚ L) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, hsum, ← finrank_mul_finrank ℚ F L, Nat.cast_mul]
        field_simp
    _ = ∑ w ∈ placesOver L u, (Real.log (placeNorm w) / finrank ℚ L +
          ((𝔭.ramificationIdx' w.maximalIdeal.asIdeal - 1 : ℕ) : ℝ) *
            𝔭.inertiaDeg' w.maximalIdeal.asIdeal * Real.log (Ideal.absNorm 𝔭) /
              finrank ℚ L) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have h := mem_placesOver.mp hw
        have he : 1 ≤ placeRamIdx w u := Nat.one_le_iff_ne_zero.mpr (placeRamIdx_ne_zero h)
        rw [log_placeNorm_eq h, Nat.cast_sub he]
        simp only [placeRamIdx, placeInertiaDeg, placeNorm, Nat.cast_mul, Nat.cast_one]
        ring
    _ = ∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
          ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
            ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) * 𝔭.inertiaDeg' P *
              Real.log (Ideal.absNorm 𝔭) / finrank ℚ L := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact sum_placesOver_eq u (fun P => ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) *
          𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) / finrank ℚ L)
    _ ≤ _ := add_le_add le_rfl (sum_le_diffContrib u.maximalIdeal.ne_bot)

end Local

/-! ### The global comparison -/

section Global

variable {F : Type*} [Field F] [NumberField F] {L : Type*} [Field L] [NumberField L]
  [Algebra F L]

variable (L) in
/-- A finite sum of the contributions `diffContrib L u` is at most `log N(𝔇_{L/F})/[L : ℚ]`. -/
theorem sum_diffContrib_le (T : Finset (FinitePlace F)) :
    ∑ u ∈ T, diffContrib L u.maximalIdeal.asIdeal ≤
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  classical
  have hinj : Set.InjOn (fun u : FinitePlace F => u.maximalIdeal) T :=
    fun _ _ _ _ h => (FinitePlace.maximalIdeal_inj _ _).mp h
  rw [← Finset.sum_image (g := fun u : FinitePlace F => u.maximalIdeal)
    (f := fun 𝔭 : HeightOneSpectrum (𝓞 F) => diffContrib L 𝔭.asIdeal) hinj,
    log_absNorm_differentIdeal_div_eq_finsum]
  set s := T.image (fun u : FinitePlace F => u.maximalIdeal) ∪
    (diffContrib_support_finite (F := F) L).toFinset
  rw [finsum_eq_sum_of_support_subset _ (s := s)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ => diffContrib_nonneg _
  · intro 𝔭 h𝔭
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr h𝔭

open scoped Classical in
/-- **(W7a) The comparison of log-conductors along an extension**: for `G' ⊆ F`, `G ⊆ L` with
`G' ⊆ G`, `cond G' ≤ cond G + log N(𝔇_{L/F})/[L : ℚ]`. -/
theorem cond_le_cond_add (G' : Finset F) (G : Finset L)
    (hG : G'.image (algebraMap F L) ⊆ G) :
    cond G' ≤ cond G + Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  classical
  set T' := meetsFinset G'
  set T := meetsFinset G
  have hdisj : Set.PairwiseDisjoint (T' : Set (FinitePlace F)) (placesOver L) := by
    intro u₁ _ u₂ _ hne
    refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => hne ?_
    rw [eq_placeBelow (mem_placesOver.mp hw₁), eq_placeBelow (mem_placesOver.mp hw₂)]
  have hsub : T'.biUnion (placesOver L) ⊆ T := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨g, hg, hug⟩ := mem_meetsFinset.mp hu
    refine mem_meetsFinset.mpr ⟨algebraMap F L g, hG (Finset.mem_image_of_mem _ hg), ?_⟩
    exact (one_lt_apply_algebraMap_iff (mem_placesOver.mp hwu) g).mpr hug
  rw [cond_eq_sum, cond_eq_sum, Finset.sum_div, Finset.sum_div]
  calc ∑ u ∈ T', Real.log (placeNorm u) / finrank ℚ F
      ≤ ∑ u ∈ T', (∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
          diffContrib L u.maximalIdeal.asIdeal) :=
        Finset.sum_le_sum fun u _ => log_placeNorm_div_le L u
    _ = ∑ w ∈ T'.biUnion (placesOver L), Real.log (placeNorm w) / finrank ℚ L +
          ∑ u ∈ T', diffContrib L u.maximalIdeal.asIdeal := by
        rw [Finset.sum_add_distrib, Finset.sum_biUnion hdisj]
    _ ≤ _ := add_le_add
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
          div_nonneg (log_placeNorm_nonneg w) (by positivity))
        (sum_diffContrib_le L T')

open scoped Classical in
/-- **(W7a) with the tower formula**: `logDisc F + cond G' ≤ logDisc L + cond G` for
`G' ⊆ G`. -/
theorem logDisc_add_cond_le (G' : Finset F) (G : Finset L)
    (hG : G'.image (algebraMap F L) ⊆ G) :
    logDisc F + cond G' ≤ logDisc L + cond G := by
  have h1 := cond_le_cond_add G' G hG
  have h2 := logDisc_eq_add F L
  linarith

end Global

end Heights.Different
