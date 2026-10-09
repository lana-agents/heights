/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.WeierstrassAdditionDifferential
import Heights.WeierstrassFibers
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option linter.style.header false

/-!
# The local Weierstrass addition theorem

The removable secant coordinates constructed in
`Heights.WeierstrassAdditionDifferential` solve the same polynomial first-order
ODE as `(℘, ℘′)`.  Real ODE uniqueness and the complex analytic identity
principle therefore identify them, near zero, with translation by the finite
point used in the secant construction.

This file proves only the local analytic identity.  Global continuation across
the remaining discrete exceptional set and compatibility of the descended map
with the elliptic-curve group law are separate steps.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace Heights

private def additionV (L : PeriodPair) : ℂ × ℂ → ℂ × ℂ :=
  fun q ↦ (q.2, 6 * q.1 ^ 2 - L.g₂ / 2)

private def secantState (L : PeriodPair) (a b : ℂ) : ℝ → ℂ × ℂ :=
  fun t ↦ (weierstrassSecantAddXAtZero L a b (Complex.ofRealCLM t),
    2 * weierstrassSecantAddYAtZero L a b (Complex.ofRealCLM t))

private def translateState (L : PeriodPair) (w : ℂ) : ℝ → ℂ × ℂ :=
  fun t ↦ (L.weierstrassP (w + Complex.ofRealCLM t),
    L.derivWeierstrassP (w + Complex.ofRealCLM t))

private theorem eventually_hasDerivAt_secantAddXAtZero
    (L : PeriodPair) (a b : ℂ)
    (hab : b ^ 2 = 4 * a ^ 3 - L.g₂ * a - L.g₃) :
    ∀ᶠ z : ℂ in 𝓝 0, HasDerivAt (weierstrassSecantAddXAtZero L a b)
      (2 * weierstrassSecantAddYAtZero L a b z) z := by
  have hx := analyticAt_weierstrassSecantAddXAtZero L a b hab
  have hy := analyticAt_weierstrassSecantAddYAtZero L a b hab
  have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      deriv (weierstrassSecantAddXAtZero L a b) z =
        2 * weierstrassSecantAddYAtZero L a b z := by
    filter_upwards [eventually_weierstrassSecant_domain L a,
      self_mem_nhdsWithin] with z hz hz0
    have hd := hasDerivAt_weierstrassSecantAddX L a b z hz.1 hz.2 hab
    have heq : weierstrassSecantAddXAtZero L a b =ᶠ[𝓝 z]
        weierstrassSecantAddX L a b := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with u hu
      simp [weierstrassSecantAddXAtZero, hu]
    have hd' := hd.congr_of_eventuallyEq heq
    rw [hd'.deriv]
    have hz0' : z ≠ 0 := by simpa using hz0
    simp [weierstrassSecantAddYAtZero, hz0']
  have hrhs : AnalyticAt ℂ
      (fun z ↦ 2 * weierstrassSecantAddYAtZero L a b z) 0 := by
    fun_prop
  have hderiv : deriv (weierstrassSecantAddXAtZero L a b) =ᶠ[𝓝 0]
      (fun z ↦ 2 * weierstrassSecantAddYAtZero L a b z) :=
    (hx.deriv.frequently_eq_iff_eventually_eq hrhs).mp hpunct.frequently
  filter_upwards [hx.eventually_analyticAt, hderiv] with z hz heq
  rw [← heq]
  exact hz.differentiableAt.hasDerivAt

private theorem eventually_hasDerivAt_secantAddYAtZero
    (L : PeriodPair) (a b : ℂ)
    (hab : b ^ 2 = 4 * a ^ 3 - L.g₂ * a - L.g₃) :
    ∀ᶠ z : ℂ in 𝓝 0, HasDerivAt (weierstrassSecantAddYAtZero L a b)
      (3 * weierstrassSecantAddXAtZero L a b z ^ 2 - L.g₂ / 4) z := by
  have hx := analyticAt_weierstrassSecantAddXAtZero L a b hab
  have hy := analyticAt_weierstrassSecantAddYAtZero L a b hab
  have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      deriv (weierstrassSecantAddYAtZero L a b) z =
        3 * weierstrassSecantAddXAtZero L a b z ^ 2 - L.g₂ / 4 := by
    filter_upwards [eventually_weierstrassSecant_domain L a,
      self_mem_nhdsWithin] with z hz hz0
    have hd := hasDerivAt_weierstrassSecantAddY L a b z hz.1 hz.2 hab
    have heq : weierstrassSecantAddYAtZero L a b =ᶠ[𝓝 z]
        weierstrassSecantAddY L a b := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with u hu
      simp [weierstrassSecantAddYAtZero, hu]
    have hd' := hd.congr_of_eventuallyEq heq
    rw [hd'.deriv]
    have hz0' : z ≠ 0 := by simpa using hz0
    simp [weierstrassSecantAddXAtZero, hz0']
  have hrhs : AnalyticAt ℂ
      (fun z ↦ 3 * weierstrassSecantAddXAtZero L a b z ^ 2 - L.g₂ / 4) 0 := by
    fun_prop
  have hderiv : deriv (weierstrassSecantAddYAtZero L a b) =ᶠ[𝓝 0]
      (fun z ↦ 3 * weierstrassSecantAddXAtZero L a b z ^ 2 - L.g₂ / 4) :=
    (hy.deriv.frequently_eq_iff_eventually_eq hrhs).mp hpunct.frequently
  filter_upwards [hy.eventually_analyticAt, hderiv] with z hz heq
  rw [← heq]
  exact hz.differentiableAt.hasDerivAt

private theorem eventually_hasDerivAt_secantState
    (L : PeriodPair) (a b : ℂ)
    (hab : b ^ 2 = 4 * a ^ 3 - L.g₂ * a - L.g₃) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (secantState L a b) (additionV L (secantState L a b t)) t := by
  have hx := (eventually_hasDerivAt_secantAddXAtZero L a b hab).filter_mono
    Complex.ofRealCLM.continuous.continuousAt.tendsto
  have hy := (eventually_hasDerivAt_secantAddYAtZero L a b hab).filter_mono
    Complex.ofRealCLM.continuous.continuousAt.tendsto
  filter_upwards [hx, hy] with t hxt hyt
  have hinner : HasDerivAt (fun s : ℝ ↦ Complex.ofRealCLM s) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have hxr := hxt.comp t hinner
  have hyr := hyt.comp t hinner
  change HasDerivAt
    (fun s : ℝ ↦ (weierstrassSecantAddXAtZero L a b (Complex.ofRealCLM s),
      2 * weierstrassSecantAddYAtZero L a b (Complex.ofRealCLM s)))
    (2 * weierstrassSecantAddYAtZero L a b (Complex.ofRealCLM t),
      6 * weierstrassSecantAddXAtZero L a b (Complex.ofRealCLM t) ^ 2 -
        L.g₂ / 2) t
  convert hxr.prodMk (hyr.const_mul 2) using 1
  · funext s
    simp only [Function.comp_apply]
  · apply Prod.ext <;> ring

private theorem eventually_translate_not_mem (L : PeriodPair) (w : ℂ)
    (hw : w ∉ L.lattice) :
    ∀ᶠ t : ℝ in 𝓝 0, w + Complex.ofRealCLM t ∉ L.lattice := by
  have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hc : Continuous (fun t : ℝ ↦ w + Complex.ofRealCLM t) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simpa using hw))

private theorem eventually_hasDerivAt_translateState (L : PeriodPair) (w : ℂ)
    (hw : w ∉ L.lattice) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (translateState L w) (additionV L (translateState L w t)) t := by
  filter_upwards [eventually_translate_not_mem L w hw] with t hwt
  have hp : HasDerivAt L.weierstrassP
      (L.derivWeierstrassP (w + Complex.ofRealCLM t))
      (w + Complex.ofRealCLM t) := by
    rw [← L.deriv_weierstrassP]
    exact (L.analyticOnNhd_weierstrassP _ hwt).differentiableAt.hasDerivAt
  have hpp : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP (w + Complex.ofRealCLM t) ^ 2 - L.g₂ / 2)
      (w + Complex.ofRealCLM t) := by
    rw [← deriv_derivWeierstrassP L (w + Complex.ofRealCLM t) hwt]
    exact (L.analyticOnNhd_derivWeierstrassP _ hwt).differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ ↦ w + Complex.ofRealCLM s) 1 t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_add w
  change HasDerivAt
    (fun s : ℝ ↦ (L.weierstrassP (w + Complex.ofRealCLM s),
      L.derivWeierstrassP (w + Complex.ofRealCLM s)))
    (L.derivWeierstrassP (w + Complex.ofRealCLM t),
      6 * L.weierstrassP (w + Complex.ofRealCLM t) ^ 2 - L.g₂ / 2) t
  simpa only [Function.comp_apply, mul_one] using
    (hp.comp t hinner).prodMk (hpp.comp t hinner)

private theorem secantState_eventuallyEq_translateState (L : PeriodPair) (w : ℂ)
    (hw : w ∉ L.lattice) :
    secantState L (L.weierstrassP w) (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      translateState L w := by
  have hab := L.derivWeierstrassP_sq w hw
  have hV : ContDiff ℝ 1 (additionV L) := by
    unfold additionV
    fun_prop
  obtain ⟨K, s, hs, hVs⟩ := hV.contDiffAt.exists_lipschitzOnWith
      (x := secantState L (L.weierstrassP w) (L.derivWeierstrassP w) 0)
  let S : ℝ → Set (ℂ × ℂ) := fun _ ↦ s
  have hv : ∀ᶠ t : ℝ in 𝓝 0, LipschitzOnWith K (additionV L) (S t) :=
    Eventually.of_forall fun _ ↦ hVs
  have hsec_mem : ∀ᶠ t : ℝ in 𝓝 0,
      secantState L (L.weierstrassP w) (L.derivWeierstrassP w) t ∈ s := by
    have hc : ContinuousAt
        (secantState L (L.weierstrassP w) (L.derivWeierstrassP w)) 0 := by
      unfold secantState
      have hx := (analyticAt_weierstrassSecantAddXAtZero L
        (L.weierstrassP w) (L.derivWeierstrassP w) hab).continuousAt
      have hy := (analyticAt_weierstrassSecantAddYAtZero L
        (L.weierstrassP w) (L.derivWeierstrassP w) hab).continuousAt
      have hi : ContinuousAt (fun t : ℝ ↦ Complex.ofRealCLM t) 0 :=
        Complex.ofRealCLM.continuous.continuousAt
      exact (hx.comp_of_eq hi (by norm_num)).prodMk
        ((hy.comp_of_eq hi (by norm_num)).const_mul 2)
    exact hc.preimage_mem_nhds (by simpa [secantState] using hs)
  have htrans_mem : ∀ᶠ t : ℝ in 𝓝 0, translateState L w t ∈ s := by
    have hc : ContinuousAt (translateState L w) 0 := by
      unfold translateState
      have hinner : ContinuousAt (fun t : ℝ ↦ w + Complex.ofRealCLM t) 0 := by
        fun_prop
      exact ((L.analyticOnNhd_weierstrassP w hw).continuousAt.comp_of_eq hinner
          (by norm_num)).prodMk
        ((L.analyticOnNhd_derivWeierstrassP w hw).continuousAt.comp_of_eq hinner
          (by norm_num))
    have hbase : translateState L w 0 =
        secantState L (L.weierstrassP w) (L.derivWeierstrassP w) 0 := by
      simp [translateState, secantState]
      ring
    rw [← hbase] at hs
    exact hc.preimage_mem_nhds hs
  apply ODE_solution_unique_of_eventually (v := fun _ ↦ additionV L) (s := S) hv
  · filter_upwards [eventually_hasDerivAt_secantState L _ _ hab,
      hsec_mem] with t ht hmem
    exact ⟨ht, hmem⟩
  · filter_upwards [eventually_hasDerivAt_translateState L w hw,
      htrans_mem] with t ht hmem
    exact ⟨ht, hmem⟩
  · simp [secantState, translateState]
    ring

private theorem frequently_eq_of_eventuallyEq_ofReal {f g : ℂ → ℂ}
    (h : (fun t : ℝ ↦ f (Complex.ofRealCLM t)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ g (Complex.ofRealCLM t))) :
    ∃ᶠ z : ℂ in 𝓝[≠] 0, f z = g z := by
  let r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let u : ℕ → ℂ := fun n ↦ Complex.ofRealCLM (r n)
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    simpa [r] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hu_lim : Tendsto u atTop (𝓝 (0 : ℂ)) :=
    Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hr_lim
  have hu_ne : ∀ n, u n ≠ 0 := by
    intro n
    dsimp [u, r]
    intro hn
    have hre := congr_arg Complex.re hn
    simp only [Complex.ofReal_re] at hre
    exact (one_div_ne_zero (by positivity)) hre
  have hu_lim' : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
    exact tendsto_inf.2 ⟨hu_lim,
      tendsto_principal.2 (Eventually.of_forall hu_ne)⟩
  have heq : ∀ᶠ n : ℕ in atTop, f (u n) = g (u n) := by
    filter_upwards [h.filter_mono hr_lim] with n hn
    exact hn
  rw [frequently_iff]
  intro q hq
  have hq' : ∀ᶠ n : ℕ in atTop, u n ∈ q := hu_lim' hq
  obtain ⟨n, hn, heqn⟩ := (hq'.and heq).exists
  exact ⟨u n, hn, heqn⟩

/-- Local form of the Weierstrass addition theorem for the `x`-coordinate.
For a non-pole `w`, the removable secant candidate for addition by the curve
point represented by `w` agrees near zero with `z ↦ ℘(w+z)`. -/
theorem weierstrassSecantAddXAtZero_eventuallyEq_translate
    (L : PeriodPair) (w : ℂ) (hw : w ∉ L.lattice) :
    weierstrassSecantAddXAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      (fun z ↦ L.weierstrassP (w + z)) := by
  have hstate := secantState_eventuallyEq_translateState L w hw
  have hreal : (fun t : ℝ ↦
      weierstrassSecantAddXAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w) (Complex.ofRealCLM t)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ L.weierstrassP (w + Complex.ofRealCLM t)) :=
    hstate.mono fun t ht ↦ congr_arg Prod.fst ht
  have hfreq := frequently_eq_of_eventuallyEq_ofReal
    (f := weierstrassSecantAddXAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w))
    (g := fun z ↦ L.weierstrassP (w + z)) hreal
  have hx := analyticAt_weierstrassSecantAddXAtZero L
    (L.weierstrassP w) (L.derivWeierstrassP w)
    (L.derivWeierstrassP_sq w hw)
  have ht : AnalyticAt ℂ (fun z ↦ L.weierstrassP (w + z)) 0 := by
    change AnalyticAt ℂ (L.weierstrassP ∘ fun z : ℂ ↦ w + z) 0
    have ho : AnalyticAt ℂ L.weierstrassP (w + 0) := by
      simpa using L.analyticOnNhd_weierstrassP w hw
    exact ho.comp (by fun_prop)
  exact (hx.frequently_eq_iff_eventually_eq ht).mp hfreq

/-- Local form of the Weierstrass addition theorem for the `y`-coordinate,
with the short-Weierstrass normalization `y = ℘′/2`. -/
theorem weierstrassSecantAddYAtZero_eventuallyEq_translate
    (L : PeriodPair) (w : ℂ) (hw : w ∉ L.lattice) :
    weierstrassSecantAddYAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      (fun z ↦ L.derivWeierstrassP (w + z) / 2) := by
  have hstate := secantState_eventuallyEq_translateState L w hw
  have hreal : (fun t : ℝ ↦
      weierstrassSecantAddYAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w) (Complex.ofRealCLM t)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ L.derivWeierstrassP (w + Complex.ofRealCLM t) / 2) := by
    filter_upwards [hstate] with t ht
    have hsecond := congr_arg Prod.snd ht
    dsimp [secantState, translateState] at hsecond
    have hs : 2 * weierstrassSecantAddYAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w) (Complex.ofRealCLM t) =
        L.derivWeierstrassP (w + Complex.ofRealCLM t) := by
      simpa only [Complex.ofRealCLM_apply] using hsecond
    calc
      _ = (2 * weierstrassSecantAddYAtZero L (L.weierstrassP w)
          (L.derivWeierstrassP w) (Complex.ofRealCLM t)) / 2 := by ring
      _ = _ := by rw [hs]
  have hfreq := frequently_eq_of_eventuallyEq_ofReal
    (f := weierstrassSecantAddYAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w))
    (g := fun z ↦ L.derivWeierstrassP (w + z) / 2) hreal
  have hy := analyticAt_weierstrassSecantAddYAtZero L
    (L.weierstrassP w) (L.derivWeierstrassP w)
    (L.derivWeierstrassP_sq w hw)
  have ht : AnalyticAt ℂ (fun z ↦ L.derivWeierstrassP (w + z) / 2) 0 := by
    have hc : AnalyticAt ℂ (fun z ↦ L.derivWeierstrassP (w + z)) 0 := by
      change AnalyticAt ℂ (L.derivWeierstrassP ∘ fun z : ℂ ↦ w + z) 0
      have ho : AnalyticAt ℂ L.derivWeierstrassP (w + 0) := by
        simpa using L.analyticOnNhd_derivWeierstrassP w hw
      exact ho.comp (by fun_prop)
    fun_prop
  exact (hy.frequently_eq_iff_eventually_eq ht).mp hfreq

/-- The global Weierstrass secant addition formula away from its genuine
exceptional points.  The hypotheses exclude poles of the two inputs and their
sum, and exclude a vertical secant. -/
theorem weierstrass_addition_coordinates (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
    (hne : L.weierstrassP z ≠ L.weierstrassP w) :
    weierstrassSecantAddX L (L.weierstrassP w) (L.derivWeierstrassP w) z =
        L.weierstrassP (z + w) ∧
      weierstrassSecantAddY L (L.weierstrassP w) (L.derivWeierstrassP w) z =
        L.derivWeierstrassP (z + w) / 2 := by
  let A : Set ℂ := (L.lattice : Set ℂ) \ {0}
  let Bm : Set ℂ := (fun u : ℂ ↦ u - w) ⁻¹' (L.lattice : Set ℂ)
  let Bp : Set ℂ := (fun u : ℂ ↦ u + w) ⁻¹' (L.lattice : Set ℂ)
  let C : Set ℂ := (fun u : ℂ ↦ u + w) ⁻¹' (L.lattice : Set ℂ)
  let D : Set ℂ := ((A ∪ Bm) ∪ Bp) ∪ C
  let U : Set ℂ := Dᶜ
  have hlattice : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hA : A.Countable := hlattice.mono sdiff_le
  have hBm : Bm.Countable := hlattice.preimage sub_left_injective
  have hBp : Bp.Countable := hlattice.preimage fun _ _ h ↦ add_right_cancel h
  have hC : C.Countable := hlattice.preimage fun _ _ h ↦ add_right_cancel h
  have hD : D.Countable := ((hA.union hBm).union hBp).union hC
  have hUpre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hD).2
  have h0U : (0 : ℂ) ∈ U := by
    simp [U, D, A, Bm, Bp, C, hw]
  have hzU : z ∈ U := by
    have hzA : z ∉ A := fun h ↦ hz h.1
    have hzBm : z ∉ Bm := by
      intro h
      exact hne <| (weierstrassP_eq_iff_sub_mem_or_add_mem L z w hz hw).2
        (Or.inl h)
    have hzBp : z ∉ Bp := by
      intro h
      exact hne <| (weierstrassP_eq_iff_sub_mem_or_add_mem L z w hz hw).2
        (Or.inr h)
    have hzC : z ∉ C := by
      simpa [C, add_comm] using hzw
    simpa only [U, D, mem_compl_iff, mem_union, not_or] using
      ⟨⟨⟨hzA, hzBm⟩, hzBp⟩, hzC⟩
  have hX : AnalyticOnNhd ℂ
      (weierstrassSecantAddXAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w)) U := by
    intro u hu
    by_cases hu0 : u = 0
    · simpa [hu0] using analyticAt_weierstrassSecantAddXAtZero L
        (L.weierstrassP w) (L.derivWeierstrassP w)
        (L.derivWeierstrassP_sq w hw)
    · have huD : u ∉ D := by simpa [U] using hu
      have huA : u ∉ A := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inl h)))
      have hul : u ∉ L.lattice := by
        intro h
        exact huA ⟨h, by simpa using hu0⟩
      have huBm : u ∉ Bm := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inr h)))
      have huBp : u ∉ Bp := by
        intro h
        exact huD (Or.inl (Or.inr h))
      have hpne : L.weierstrassP u ≠ L.weierstrassP w := by
        intro hp
        rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L u w hul hw).1 hp with
          hm | hp
        · exact huBm hm
        · exact huBp hp
      have hp : AnalyticAt ℂ L.weierstrassP u :=
        L.analyticOnNhd_weierstrassP u hul
      have hdp : AnalyticAt ℂ L.derivWeierstrassP u :=
        L.analyticOnNhd_derivWeierstrassP u hul
      have hm : AnalyticAt ℂ
          (weierstrassSecantSlope L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantSlope
        exact (hdp.sub analyticAt_const).div
          (analyticAt_const.mul (hp.sub analyticAt_const))
          (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hpne))
      have horig : AnalyticAt ℂ
          (weierstrassSecantAddX L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantAddX
        exact ((hm.pow 2).sub hp).sub analyticAt_const
      apply horig.congr
      filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
      simp [weierstrassSecantAddXAtZero, hv]
  have hY : AnalyticOnNhd ℂ
      (weierstrassSecantAddYAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w)) U := by
    intro u hu
    by_cases hu0 : u = 0
    · simpa [hu0] using analyticAt_weierstrassSecantAddYAtZero L
        (L.weierstrassP w) (L.derivWeierstrassP w)
        (L.derivWeierstrassP_sq w hw)
    · have huD : u ∉ D := by simpa [U] using hu
      have huA : u ∉ A := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inl h)))
      have hul : u ∉ L.lattice := by
        intro h
        exact huA ⟨h, by simpa using hu0⟩
      have huBm : u ∉ Bm := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inr h)))
      have huBp : u ∉ Bp := by
        intro h
        exact huD (Or.inl (Or.inr h))
      have hpne : L.weierstrassP u ≠ L.weierstrassP w := by
        intro hp
        rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L u w hul hw).1 hp with
          hm | hp
        · exact huBm hm
        · exact huBp hp
      have hp : AnalyticAt ℂ L.weierstrassP u :=
        L.analyticOnNhd_weierstrassP u hul
      have hdp : AnalyticAt ℂ L.derivWeierstrassP u :=
        L.analyticOnNhd_derivWeierstrassP u hul
      have hm : AnalyticAt ℂ
          (weierstrassSecantSlope L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantSlope
        exact (hdp.sub analyticAt_const).div
          (analyticAt_const.mul (hp.sub analyticAt_const))
          (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hpne))
      have hxorig : AnalyticAt ℂ
          (weierstrassSecantAddX L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantAddX
        exact ((hm.pow 2).sub hp).sub analyticAt_const
      have horig : AnalyticAt ℂ
          (weierstrassSecantAddY L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantAddY
        have hhalf : AnalyticAt ℂ (fun v ↦ L.derivWeierstrassP v / 2) u :=
          hdp.div_const
        exact (hm.mul (hp.sub hxorig)).sub hhalf
      apply horig.congr
      filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
      simp [weierstrassSecantAddYAtZero, hv]
  have hTX : AnalyticOnNhd ℂ (fun u ↦ L.weierstrassP (u + w)) U := by
    intro u hu
    have huD : u ∉ D := by simpa [U] using hu
    have huC : u ∉ C := by
      intro h
      exact huD (Or.inr h)
    change AnalyticAt ℂ (L.weierstrassP ∘ fun v : ℂ ↦ v + w) u
    have hi : AnalyticAt ℂ (fun v : ℂ ↦ v + w) u :=
      analyticAt_id.add analyticAt_const
    exact (L.analyticOnNhd_weierstrassP (u + w) huC).comp
      (f := fun v : ℂ ↦ v + w) hi
  have hTY : AnalyticOnNhd ℂ
      (fun u ↦ L.derivWeierstrassP (u + w) / 2) U := by
    intro u hu
    have huD : u ∉ D := by simpa [U] using hu
    have huC : u ∉ C := by
      intro h
      exact huD (Or.inr h)
    have hd : AnalyticAt ℂ (fun v ↦ L.derivWeierstrassP (v + w)) u := by
      change AnalyticAt ℂ (L.derivWeierstrassP ∘ fun v : ℂ ↦ v + w) u
      have hi : AnalyticAt ℂ (fun v : ℂ ↦ v + w) u :=
        analyticAt_id.add analyticAt_const
      exact (L.analyticOnNhd_derivWeierstrassP (u + w) huC).comp
        (f := fun v : ℂ ↦ v + w) hi
    fun_prop
  have hlocalX := weierstrassSecantAddXAtZero_eventuallyEq_translate L w hw
  have hlocalX' : weierstrassSecantAddXAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      (fun u ↦ L.weierstrassP (u + w)) := by
    filter_upwards [hlocalX] with u hu
    simpa [add_comm] using hu
  have hlocalY := weierstrassSecantAddYAtZero_eventuallyEq_translate L w hw
  have hlocalY' : weierstrassSecantAddYAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      (fun u ↦ L.derivWeierstrassP (u + w) / 2) := by
    filter_upwards [hlocalY] with u hu
    simpa [add_comm] using hu
  have hglobalX := hX.eqOn_of_preconnected_of_eventuallyEq hTX hUpre h0U hlocalX'
  have hglobalY := hY.eqOn_of_preconnected_of_eventuallyEq hTY hUpre h0U hlocalY'
  have hx0 : z ≠ 0 := by
    intro h
    subst z
    exact hz L.lattice.zero_mem
  constructor
  · simpa [weierstrassSecantAddXAtZero, hx0] using hglobalX hzU
  · simpa [weierstrassSecantAddYAtZero, hx0] using hglobalY hzU

end Heights
