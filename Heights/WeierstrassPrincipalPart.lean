import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

set_option linter.style.header false

/-!
# Principal parts of the Weierstrass function

Mathlib's definitions split `℘` and `℘′` into their singular summand at a
lattice point and a power series analytic there.  This file records the
resulting limits in a form convenient for the classical addition theorem:
near a period `l`,

`(z - l)² ℘(z) → 1` and `(z - l)³ ℘′(z) → -2`.

These are local analytic inputs only.  In particular, no addition formula or
group-law compatibility is claimed here.
-/

open Set Filter Topology
open scoped Topology

noncomputable section
namespace Heights

/-- After subtracting its `z⁻²` principal part, `℘` tends to zero at the
origin. -/
theorem tendsto_weierstrassP_sub_inv_sq_zero (L : PeriodPair) :
    Tendsto (fun z : ℂ ↦ L.weierstrassP z - 1 / z ^ 2) (𝓝 0) (𝓝 0) := by
  have h := (L.analyticAt_weierstrassPExcept 0).continuousAt
  change Tendsto (L.weierstrassPExcept 0) (𝓝 0)
    (𝓝 (L.weierstrassPExcept 0 0)) at h
  convert h using 1
  · funext z
    rw [← L.weierstrassPExcept_add (0 : L.lattice)]
    simp
  · simp

/-- After subtracting its `-2z⁻³` principal part, `℘′` tends to zero at the
origin. -/
theorem tendsto_derivWeierstrassP_add_two_div_cube_zero (L : PeriodPair) :
    Tendsto (fun z : ℂ ↦ L.derivWeierstrassP z + 2 / z ^ 3) (𝓝 0) (𝓝 0) := by
  have h := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
  change Tendsto (L.derivWeierstrassPExcept 0) (𝓝 0)
    (𝓝 (L.derivWeierstrassPExcept 0 0)) at h
  convert h using 1
  · funext z
    rw [← L.derivWeierstrassPExcept_sub (0 : L.lattice)]
    simp
  · simp

/-- The normalized Weierstrass function tends to `1` at its pole at zero. -/
theorem tendsto_sq_mul_weierstrassP_zero (L : PeriodPair) :
    Tendsto (fun z : ℂ ↦ z ^ 2 * L.weierstrassP z) (𝓝[≠] 0) (𝓝 1) := by
  have hz : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hz2 : Tendsto (fun z : ℂ ↦ z ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hz.pow 2
  have hexc : Tendsto (L.weierstrassPExcept 0) (𝓝[≠] 0) (𝓝 0) := by
    have h := (L.analyticAt_weierstrassPExcept 0).continuousAt
    change Tendsto (L.weierstrassPExcept 0) (𝓝 0)
      (𝓝 (L.weierstrassPExcept 0 0)) at h
    have h' : Tendsto (L.weierstrassPExcept 0) (𝓝 0) (𝓝 0) := by
      simpa using h
    exact h'.mono_left inf_le_left
  have hlim : Tendsto
      (fun z : ℂ ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1)
      (𝓝[≠] 0) (𝓝 1) := by
    simpa using (hz2.mul hexc).add tendsto_const_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz0
  simp only [mem_compl_iff, mem_singleton_iff] at hz0
  rw [← L.weierstrassPExcept_add (0 : L.lattice)]
  simp
  field_simp

/-- The normalized derivative tends to `-2` at its pole at zero. -/
theorem tendsto_cube_mul_derivWeierstrassP_zero (L : PeriodPair) :
    Tendsto (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  have hz : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hz3 : Tendsto (fun z : ℂ ↦ z ^ 3) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hz.pow 3
  have hexc : Tendsto (L.derivWeierstrassPExcept 0) (𝓝[≠] 0) (𝓝 0) := by
    have h := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
    change Tendsto (L.derivWeierstrassPExcept 0) (𝓝 0)
      (𝓝 (L.derivWeierstrassPExcept 0 0)) at h
    have h' : Tendsto (L.derivWeierstrassPExcept 0) (𝓝 0) (𝓝 0) := by
      simpa using h
    exact h'.mono_left inf_le_left
  have hlim : Tendsto
      (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2)
      (𝓝[≠] 0) (𝓝 (-2)) := by
    simpa using (hz3.mul hexc).sub tendsto_const_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz0
  simp only [mem_compl_iff, mem_singleton_iff] at hz0
  rw [← L.derivWeierstrassPExcept_sub (0 : L.lattice)]
  simp
  field_simp

private theorem tendsto_sub_lattice_punctured (L : PeriodPair) (l : L.lattice) :
    Tendsto (fun z : ℂ ↦ z - (l : ℂ))
      (𝓝[≠] (l : ℂ)) (𝓝[≠] 0) := by
  apply tendsto_inf.2
  constructor
  · have h : Tendsto (fun z : ℂ ↦ z - (l : ℂ))
        (𝓝 (l : ℂ)) (𝓝 ((l : ℂ) - l)) :=
      continuousAt_id.sub continuousAt_const
    simpa using h.mono_left nhdsWithin_le_nhds
  · apply tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [mem_compl_iff, mem_singleton_iff, sub_ne_zero] using hz

/-- At every period `l`, the normalized Weierstrass function
`(z-l)²℘(z)` tends to `1`. -/
theorem tendsto_sq_mul_weierstrassP_at_lattice (L : PeriodPair) (l : L.lattice) :
    Tendsto (fun z : ℂ ↦ (z - l) ^ 2 * L.weierstrassP z)
      (𝓝[≠] (l : ℂ)) (𝓝 1) := by
  have h := (tendsto_sq_mul_weierstrassP_zero L).comp
    (tendsto_sub_lattice_punctured L l)
  apply h.congr'
  filter_upwards with z
  simp only [Function.comp_apply]
  rw [L.weierstrassP_sub_coe]

/-- At every period `l`, the normalized derivative
`(z-l)³℘′(z)` tends to `-2`. -/
theorem tendsto_cube_mul_derivWeierstrassP_at_lattice
    (L : PeriodPair) (l : L.lattice) :
    Tendsto (fun z : ℂ ↦ (z - l) ^ 3 * L.derivWeierstrassP z)
      (𝓝[≠] (l : ℂ)) (𝓝 (-2)) := by
  have h := (tendsto_cube_mul_derivWeierstrassP_zero L).comp
    (tendsto_sub_lattice_punctured L l)
  apply h.congr'
  filter_upwards with z
  simp only [Function.comp_apply]
  rw [L.derivWeierstrassP_sub_coe]

/-- The secant-formula candidate for the `x`-coordinate of adding a finite
point `(a,b/2)` extends across the point at infinity with value `a`.

This is the local cancellation needed to extend the usual Weierstrass addition
formula across `z = 0`.  It does not assert that the candidate equals
`℘(z+w)`; that global identity remains the addition-theorem frontier. -/
theorem tendsto_weierstrass_secant_addX_zero (L : PeriodPair) (a b : ℂ) :
    Tendsto (fun z : ℂ ↦
      ((L.derivWeierstrassP z - b) /
          (2 * (L.weierstrassP z - a))) ^ 2 -
        L.weierstrassP z - a) (𝓝[≠] 0) (𝓝 a) := by
  let e : ℂ → ℂ := fun z ↦ L.weierstrassP z - 1 / z ^ 2
  let d : ℂ → ℂ := fun z ↦ L.derivWeierstrassP z + 2 / z ^ 3
  let A : ℂ → ℂ := fun z ↦ 1 + (e z - a) * z ^ 2
  let C : ℂ → ℂ := fun z ↦ 2 * (e z - a) + (d z - b) * z
  let D : ℂ → ℂ := fun z ↦
    -4 + (d z - b) * z ^ 3 - 2 * (e z - a) * z ^ 2
  have hz : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have he : Tendsto e (𝓝[≠] 0) (𝓝 0) :=
    (tendsto_weierstrassP_sub_inv_sq_zero L).mono_left nhdsWithin_le_nhds
  have hd : Tendsto d (𝓝[≠] 0) (𝓝 0) :=
    (tendsto_derivWeierstrassP_add_two_div_cube_zero L).mono_left
      nhdsWithin_le_nhds
  have ha : Tendsto (fun _ : ℂ ↦ a) (𝓝[≠] 0) (𝓝 a) := tendsto_const_nhds
  have hb : Tendsto (fun _ : ℂ ↦ b) (𝓝[≠] 0) (𝓝 b) := tendsto_const_nhds
  have hfour : Tendsto (fun _ : ℂ ↦ (4 : ℂ)) (𝓝[≠] 0) (𝓝 4) :=
    tendsto_const_nhds
  have hnegfour : Tendsto (fun _ : ℂ ↦ (-4 : ℂ)) (𝓝[≠] 0) (𝓝 (-4)) :=
    tendsto_const_nhds
  have hea : Tendsto (fun z ↦ e z - a) (𝓝[≠] 0) (𝓝 (-a)) := by
    convert he.sub ha using 1
    all_goals ring
  have hdb : Tendsto (fun z ↦ d z - b) (𝓝[≠] 0) (𝓝 (-b)) := by
    convert hd.sub hb using 1
    all_goals ring
  have hA : Tendsto A (𝓝[≠] 0) (𝓝 1) := by
    dsimp [A]
    simpa using tendsto_const_nhds.add (hea.mul (hz.pow 2))
  have hC : Tendsto C (𝓝[≠] 0) (𝓝 (-2 * a)) := by
    dsimp [C]
    convert (hea.const_mul 2).add (hdb.mul hz) using 1
    all_goals ring
  have hD : Tendsto D (𝓝[≠] 0) (𝓝 (-4)) := by
    dsimp [D]
    convert (hnegfour.add (hdb.mul (hz.pow 3))).sub
      ((hea.mul (hz.pow 2)).const_mul 2) using 1
    · funext z
      ring
    · ring
  have hden : Tendsto (fun z ↦ 4 * A z ^ 2) (𝓝[≠] 0) (𝓝 4) := by
    convert hfour.mul (hA.pow 2) using 1
    all_goals ring
  have hfrac : Tendsto (fun z ↦ D z * C z / (4 * A z ^ 2))
      (𝓝[≠] 0) (𝓝 (2 * a)) := by
    have h := (hD.mul hC).div hden (by norm_num)
    have h' : Tendsto (fun z ↦ D z * C z / (4 * A z ^ 2))
        (𝓝[≠] 0) (𝓝 ((-4) * (-2 * a) / 4)) := by
      apply h.congr'
      filter_upwards with z
      simp only [Pi.div_apply]
    convert h' using 1
    ring
  have hG : Tendsto (fun z ↦ -e z - a + D z * C z / (4 * A z ^ 2))
      (𝓝[≠] 0) (𝓝 a) := by
    convert (he.neg.sub ha).add hfrac using 1
    all_goals ring
  apply hG.congr'
  have hAne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), A z ≠ 0 :=
    hA (eventually_ne_nhds one_ne_zero)
  filter_upwards [self_mem_nhdsWithin, hAne] with z hz0 hAz
  simp only [mem_compl_iff, mem_singleton_iff] at hz0
  have hAeq : A z = z ^ 2 * (L.weierstrassP z - a) := by
    dsimp [A, e]
    field_simp [hz0]
    ring
  have hpne : L.weierstrassP z - a ≠ 0 := by
    intro hp
    apply hAz
    rw [hAeq, hp, mul_zero]
  rw [hAeq]
  dsimp [C, D, e, d]
  field_simp [hz0, hpne]
  ring

end Heights
