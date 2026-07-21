import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Meromorphic.Order

set_option linter.style.header false

/-!
# The second-order Weierstrass differential equation

Mathlib proves the first-order cubic relation for the Weierstrass `℘`-function.
This file differentiates it and removes the apparent `℘′` factor globally on
the complement of the period lattice.  The removal is not pointwise division:
the identity theorem for analytic functions handles the ramification points
where `℘′` vanishes.

The resulting second-order equation is a useful analytic input toward the
Weierstrass addition theorem.  It does not itself prove that theorem, group-law
compatibility of the lattice point map, bijectivity, or uniformization.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace Heights

/-- Away from its poles, the second derivative of the Weierstrass function
satisfies `℘′′ = 6℘² - g₂/2`.

The proof differentiates mathlib's cubic equation.  Analytic functions on the
connected lattice complement have no zero divisors, so either `℘′` vanishes
identically or the desired second factor does.  The first alternative would
make `℘` constant off the lattice, contradicting its order-two pole. -/
theorem deriv_derivWeierstrassP (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z =
      6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  let U : Set ℂ := (L.lattice : Set ℂ)ᶜ
  have hU_open : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hU_pre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  let H : ℂ → ℂ := fun w ↦
    2 * deriv L.derivWeierstrassP w - 12 * L.weierstrassP w ^ 2 + L.g₂
  have hp_an : AnalyticOnNhd ℂ L.derivWeierstrassP U :=
    L.analyticOnNhd_derivWeierstrassP
  have hH_an : AnalyticOnNhd ℂ H U := by
    have hderiv_an : AnalyticOnNhd ℂ (deriv L.derivWeierstrassP) U :=
      hp_an.deriv_of_isOpen hU_open
    intro w hw
    have := hderiv_an w hw
    have := L.analyticOnNhd_weierstrassP w hw
    dsimp [H]
    fun_prop
  have hprod : ∀ w ∈ U, L.derivWeierstrassP w * H w = 0 := by
    intro w hw
    have hrel : Set.EqOn
        (fun u : ℂ ↦ L.derivWeierstrassP u ^ 2)
        (fun u : ℂ ↦ 4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃) U :=
      fun u hu ↦ L.derivWeierstrassP_sq u hu
    have hd := hrel.deriv hU_open hw
    have hp'_diff : DifferentiableAt ℂ L.derivWeierstrassP w :=
      (hp_an w hw).differentiableAt
    have hp_diff : DifferentiableAt ℂ L.weierstrassP w :=
      (L.analyticOnNhd_weierstrassP w hw).differentiableAt
    simp (discharger := fun_prop) only [deriv_fun_sub, deriv_const_mul,
      deriv_fun_pow, PeriodPair.deriv_weierstrassP, deriv_const] at hd
    dsimp [H]
    linear_combination hd
  rcases hp_an.eq_zero_or_eq_zero_of_mul_eq_zero hH_an hprod hU_pre with hp_zero | hH_zero
  · have hp_const : Set.EqOn L.weierstrassP
        (fun _ ↦ L.weierstrassP (L.ω₁ / 2)) U := by
      apply hU_open.eqOn_of_deriv_eq hU_pre
      · exact L.differentiableOn_weierstrassP
      · fun_prop
      · intro w hw
        rw [PeriodPair.deriv_weierstrassP]
        simpa using hp_zero w hw
      · exact L.ω₁_div_two_notMem_lattice
      · rfl
    have hevent : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun _ ↦ L.weierstrassP (L.ω₁ / 2)) := by
      have hlocal : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ),
          w ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ :=
        Filter.Eventually.filter_mono inf_le_left
          (L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ))
      filter_upwards [hlocal, self_mem_nhdsWithin] with w hw hw0
      apply hp_const
      intro hwl
      exact hw ⟨hwl, hw0⟩
    have horder := meromorphicOrderAt_congr hevent
    rw [L.order_weierstrassP 0 L.lattice.zero_mem,
      meromorphicOrderAt_const] at horder
    by_cases hc : L.weierstrassP (L.ω₁ / 2) = 0 <;> simp [hc] at horder
  · have h := hH_zero z hz
    dsimp [H] at h
    linear_combination h / 2

end Heights
