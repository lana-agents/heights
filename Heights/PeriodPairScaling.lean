/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.WeierstrassPrincipalPart
import Heights.WeierstrassDifferential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option linter.style.header false

/-!
# Scaling and rigidity of complex period lattices

This file records how a period pair and its Weierstrass invariants change under
nonzero complex homothety.  It also proves that the two invariants `g₂` and
`g₃` determine the period lattice.  The rigidity proof uses the reciprocal
coordinates at the pole of `℘`; they solve a regular polynomial ODE with fixed
initial value, so ODE uniqueness and analytic continuation identify the two
Weierstrass functions and hence their pole lattices.
-/

open Set Filter Topology
open scoped Topology

noncomputable section
namespace Heights

/-- Scale both generators of a period pair by a nonzero complex number. -/
noncomputable def periodPairScale (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := LinearIndependent.pair_iff.mpr fun s t h ↦ by
    apply (LinearIndependent.pair_iff.mp L.indep) s t
    apply mul_left_cancel₀ ha
    rw [Complex.real_smul, Complex.real_smul]
    rw [Complex.real_smul, Complex.real_smul] at h
    linear_combination h

@[simp] theorem periodPairScale_ω₁ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (periodPairScale a ha L).ω₁ = a * L.ω₁ := rfl

@[simp] theorem periodPairScale_ω₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (periodPairScale a ha L).ω₂ = a * L.ω₂ := rfl

/-- Multiplication by the scale factor identifies the original and scaled lattices. -/
noncomputable def periodPairScaleLatticeEquiv (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    L.lattice ≃+ (periodPairScale a ha L).lattice where
  toFun x := ⟨a * (x : ℂ), by
    rw [PeriodPair.mem_lattice]
    obtain ⟨m, n, hx⟩ := PeriodPair.mem_lattice.mp x.property
    refine ⟨m, n, ?_⟩
    rw [← hx]
    simp [mul_add]
    ring⟩
  invFun x := ⟨a⁻¹ * (x : ℂ), by
    rw [PeriodPair.mem_lattice]
    obtain ⟨m, n, hx⟩ := PeriodPair.mem_lattice.mp x.property
    refine ⟨m, n, ?_⟩
    rw [← hx]
    simp only [periodPairScale_ω₁, periodPairScale_ω₂]
    field_simp⟩
  left_inv x := by
    apply Subtype.ext
    simp [ha]
  right_inv x := by
    apply Subtype.ext
    simp [ha]
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add]

@[simp] theorem periodPairScaleLatticeEquiv_coe (a : ℂ) (ha : a ≠ 0)
    (L : PeriodPair) (x : L.lattice) :
    ((periodPairScaleLatticeEquiv a ha L x : (periodPairScale a ha L).lattice) : ℂ) =
      a * (x : ℂ) := rfl

/-- Eisenstein lattice sums have their expected homogeneity under scaling. -/
theorem periodPairScale_G (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (k : ℕ) :
    (periodPairScale a ha L).G k = a⁻¹ ^ k * L.G k := by
  rw [PeriodPair.G, PeriodPair.G, ← tsum_mul_left]
  rw [← (periodPairScaleLatticeEquiv a ha L).toEquiv.tsum_eq]
  apply tsum_congr
  intro l
  change ((a * (l : ℂ)) ^ k)⁻¹ = _
  rw [mul_pow, mul_inv, inv_pow]

/-- The invariant `g₂` has weight `-4` under lattice scaling. -/
theorem periodPairScale_g₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (periodPairScale a ha L).g₂ = a⁻¹ ^ 4 * L.g₂ := by
  rw [PeriodPair.g₂, periodPairScale_G, PeriodPair.g₂]
  ring

/-- The invariant `g₃` has weight `-6` under lattice scaling. -/
theorem periodPairScale_g₃ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (periodPairScale a ha L).g₃ = a⁻¹ ^ 6 * L.g₃ := by
  rw [PeriodPair.g₃, periodPairScale_G, PeriodPair.g₃]
  ring

private noncomputable def reciprocalX (L : PeriodPair) (z : ℂ) : ℂ :=
  z ^ 2 / (1 + z ^ 2 * L.weierstrassPExcept 0 z)

private noncomputable def reciprocalY (L : PeriodPair) (z : ℂ) : ℂ :=
  z * (2 - z ^ 3 * L.derivWeierstrassPExcept 0 z) /
    (2 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 2)

private theorem analyticAt_reciprocalX (L : PeriodPair) :
    AnalyticAt ℂ (reciprocalX L) 0 := by
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  norm_num [reciprocalX]

private theorem analyticAt_reciprocalY (L : PeriodPair) :
    AnalyticAt ℂ (reciprocalY L) 0 := by
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  norm_num [reciprocalY]

@[simp] private theorem reciprocalX_zero (L : PeriodPair) : reciprocalX L 0 = 0 := by
  simp [reciprocalX]

@[simp] private theorem reciprocalY_zero (L : PeriodPair) : reciprocalY L 0 = 0 := by
  simp [reciprocalY]

private theorem reciprocalX_eq_inv (L : PeriodPair) (z : ℂ) (hz : z ≠ 0) :
    reciprocalX L z = (L.weierstrassP z)⁻¹ := by
  rw [reciprocalX, ← L.weierstrassPExcept_add (0 : L.lattice)]
  simp only [ZeroMemClass.coe_zero]
  field_simp
  ring

private theorem reciprocalY_eq (L : PeriodPair) (z : ℂ) (hz : z ≠ 0) :
    reciprocalY L z =
      -L.derivWeierstrassP z / (2 * L.weierstrassP z ^ 2) := by
  rw [reciprocalY, ← L.weierstrassPExcept_add (0 : L.lattice),
    ← L.derivWeierstrassPExcept_sub (0 : L.lattice)]
  simp only [ZeroMemClass.coe_zero, sub_zero]
  field_simp
  ring

private theorem eventually_reciprocal_nonzero (L : PeriodPair) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0, L.weierstrassP z ≠ 0 := by
  have h := (tendsto_sq_mul_weierstrassP_zero L)
    (eventually_ne_nhds one_ne_zero)
  filter_upwards [h, self_mem_nhdsWithin] with z hzP hz0
  exact fun hP ↦ hzP (by simp [hP])

private def reciprocalV (L : PeriodPair) : ℂ × ℂ → ℂ × ℂ :=
  fun q ↦ (2 * q.2, 1 - 3 * L.g₂ / 4 * q.1 ^ 2 - L.g₃ * q.1 ^ 3)

private theorem eventually_hasDerivAt_reciprocalX (L : PeriodPair) :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasDerivAt (reciprocalX L) (2 * reciprocalY L z) z := by
  have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      HasDerivAt (reciprocalX L) (2 * reciprocalY L z) z := by
    filter_upwards [eventually_reciprocal_nonzero L,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with z hP hzL hz0
    have hz : z ≠ 0 := by simpa using hz0
    have hnot : z ∉ L.lattice := by simp_all
    have hderiv : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
      rw [← L.deriv_weierstrassP]
      exact (L.analyticOnNhd_weierstrassP z hnot).differentiableAt.hasDerivAt
    have heq : reciprocalX L =ᶠ[𝓝 z] fun w ↦ (L.weierstrassP w)⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact reciprocalX_eq_inv L w hw
    have hi := (hderiv.inv hP).congr_of_eventuallyEq heq
    have hval : -L.derivWeierstrassP z / L.weierstrassP z ^ 2 =
        2 * reciprocalY L z := by
      rw [reciprocalY_eq L z hz]
      field_simp
    rw [← hval]
    exact hi
  have hrhs : AnalyticAt ℂ (fun z ↦ 2 * reciprocalY L z) 0 := by
    convert (analyticAt_reciprocalY L).const_smul (c := (2 : ℂ)) using 1
    ext z
    simp [Pi.smul_apply, smul_eq_mul]
  have hderiv : deriv (reciprocalX L) =ᶠ[𝓝 0]
      (fun z ↦ 2 * reciprocalY L z) :=
    ((analyticAt_reciprocalX L).deriv.frequently_eq_iff_eventually_eq hrhs).mp
      (hpunct.mono fun _ h ↦ h.deriv).frequently
  filter_upwards [(analyticAt_reciprocalX L).eventually_analyticAt, hderiv] with z hz heq
  rw [← heq]
  exact hz.differentiableAt.hasDerivAt

private theorem eventually_hasDerivAt_reciprocalY (L : PeriodPair) :
    ∀ᶠ z : ℂ in 𝓝 0, HasDerivAt (reciprocalY L)
      (1 - 3 * L.g₂ / 4 * reciprocalX L z ^ 2 -
        L.g₃ * reciprocalX L z ^ 3) z := by
  have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] 0, HasDerivAt (reciprocalY L)
      (1 - 3 * L.g₂ / 4 * reciprocalX L z ^ 2 -
        L.g₃ * reciprocalX L z ^ 3) z := by
    filter_upwards [eventually_reciprocal_nonzero L,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with z hP hzL hz0
    have hz : z ≠ 0 := by simpa using hz0
    have hnot : z ∉ L.lattice := by simp_all
    have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
      rw [← L.deriv_weierstrassP]
      exact (L.analyticOnNhd_weierstrassP z hnot).differentiableAt.hasDerivAt
    have hpp : HasDerivAt L.derivWeierstrassP
        (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
      rw [← deriv_derivWeierstrassP L z hnot]
      exact (L.analyticOnNhd_derivWeierstrassP z hnot).differentiableAt.hasDerivAt
    have heq : reciprocalY L =ᶠ[𝓝 z]
        fun w ↦ -L.derivWeierstrassP w / (2 * L.weierstrassP w ^ 2) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact reciprocalY_eq L w hw
    have hden : HasDerivAt (fun w ↦ 2 * L.weierstrassP w ^ 2)
        (2 * (2 * L.weierstrassP z * L.derivWeierstrassP z)) z := by
      have hd := HasDerivAt.const_mul 2 (hp.pow 2)
      norm_num at hd
      simpa only [Pi.pow_apply] using hd
    have hfrac := hpp.neg.div hden (mul_ne_zero (by norm_num) (pow_ne_zero _ hP))
    have hi := hfrac.congr_of_eventuallyEq heq
    have hx : reciprocalX L z = (L.weierstrassP z)⁻¹ :=
      reciprocalX_eq_inv L z hz
    have hval :
        ((-(6 * L.weierstrassP z ^ 2 - L.g₂ / 2)) *
              (2 * L.weierstrassP z ^ 2) -
            (-L.derivWeierstrassP z) *
              (2 * (2 * L.weierstrassP z * L.derivWeierstrassP z))) /
            (2 * L.weierstrassP z ^ 2) ^ 2 =
          1 - 3 * L.g₂ / 4 * reciprocalX L z ^ 2 -
            L.g₃ * reciprocalX L z ^ 3 := by
      rw [hx]
      field_simp
      ring_nf
      rw [L.derivWeierstrassP_sq z hnot]
      ring
    rw [← hval]
    exact hi
  have hrhs : AnalyticAt ℂ (fun z ↦
      1 - 3 * L.g₂ / 4 * reciprocalX L z ^ 2 -
        L.g₃ * reciprocalX L z ^ 3) 0 := by
    have hx := analyticAt_reciprocalX L
    fun_prop
  have hderiv : deriv (reciprocalY L) =ᶠ[𝓝 0] (fun z ↦
      1 - 3 * L.g₂ / 4 * reciprocalX L z ^ 2 -
        L.g₃ * reciprocalX L z ^ 3) :=
    ((analyticAt_reciprocalY L).deriv.frequently_eq_iff_eventually_eq hrhs).mp
      (hpunct.mono fun _ h ↦ h.deriv).frequently
  filter_upwards [(analyticAt_reciprocalY L).eventually_analyticAt, hderiv] with z hz heq
  rw [← heq]
  exact hz.differentiableAt.hasDerivAt

private def reciprocalState (L : PeriodPair) : ℝ → ℂ × ℂ :=
  fun t ↦ (reciprocalX L (Complex.ofRealCLM t),
    reciprocalY L (Complex.ofRealCLM t))

private theorem eventually_hasDerivAt_reciprocalState (L : PeriodPair) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (reciprocalState L)
        (reciprocalV L (reciprocalState L t)) t := by
  have hx := (eventually_hasDerivAt_reciprocalX L).filter_mono
    Complex.ofRealCLM.continuous.continuousAt.tendsto
  have hy := (eventually_hasDerivAt_reciprocalY L).filter_mono
    Complex.ofRealCLM.continuous.continuousAt.tendsto
  filter_upwards [hx, hy] with t hxt hyt
  have hinner : HasDerivAt (fun s : ℝ ↦ Complex.ofRealCLM s) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  change HasDerivAt
    (fun s : ℝ ↦ (reciprocalX L (Complex.ofRealCLM s),
      reciprocalY L (Complex.ofRealCLM s)))
    (2 * reciprocalY L (Complex.ofRealCLM t),
      1 - 3 * L.g₂ / 4 * reciprocalX L (Complex.ofRealCLM t) ^ 2 -
        L.g₃ * reciprocalX L (Complex.ofRealCLM t) ^ 3) t
  simpa only [Function.comp_apply, mul_one] using
    (hxt.comp t hinner).prodMk (hyt.comp t hinner)

private theorem reciprocalState_eventuallyEq (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    reciprocalState L =ᶠ[𝓝 0] reciprocalState M := by
  have hV : ContDiff ℝ 1 (reciprocalV L) := by
    unfold reciprocalV
    fun_prop
  obtain ⟨K, s, hs, hVs⟩ := hV.contDiffAt.exists_lipschitzOnWith
      (x := reciprocalState L 0)
  let S : ℝ → Set (ℂ × ℂ) := fun _ ↦ s
  have hv : ∀ᶠ t : ℝ in 𝓝 0, LipschitzOnWith K (reciprocalV L) (S t) :=
    Eventually.of_forall fun _ ↦ hVs
  have hLmem : ∀ᶠ t : ℝ in 𝓝 0, reciprocalState L t ∈ s := by
    have hc : ContinuousAt (reciprocalState L) 0 := by
      unfold reciprocalState
      exact ((analyticAt_reciprocalX L).continuousAt.comp_of_eq
        Complex.ofRealCLM.continuous.continuousAt (by norm_num)).prodMk
        ((analyticAt_reciprocalY L).continuousAt.comp_of_eq
          Complex.ofRealCLM.continuous.continuousAt (by norm_num))
    exact hc.preimage_mem_nhds (by simpa [reciprocalState] using hs)
  have hbase : reciprocalState M 0 = reciprocalState L 0 := by
    simp [reciprocalState]
  have hMmem : ∀ᶠ t : ℝ in 𝓝 0, reciprocalState M t ∈ s := by
    have hc : ContinuousAt (reciprocalState M) 0 := by
      unfold reciprocalState
      exact ((analyticAt_reciprocalX M).continuousAt.comp_of_eq
        Complex.ofRealCLM.continuous.continuousAt (by norm_num)).prodMk
        ((analyticAt_reciprocalY M).continuousAt.comp_of_eq
          Complex.ofRealCLM.continuous.continuousAt (by norm_num))
    rw [← hbase] at hs
    exact hc.preimage_mem_nhds hs
  apply ODE_solution_unique_of_eventually (v := fun _ ↦ reciprocalV L) (s := S) hv
  · filter_upwards [eventually_hasDerivAt_reciprocalState L, hLmem] with t ht hm
    exact ⟨ht, hm⟩
  · filter_upwards [eventually_hasDerivAt_reciprocalState M, hMmem] with t ht hm
    have hVL : reciprocalV M = reciprocalV L := by
      funext q
      simp [reciprocalV, h₂, h₃]
    rw [← hVL]
    exact ⟨ht, hm⟩
  · simp [reciprocalState]

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
  have hu_lim' : Tendsto u atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_inf.2 ⟨hu_lim, tendsto_principal.2 (Eventually.of_forall hu_ne)⟩
  have heq : ∀ᶠ n : ℕ in atTop, f (u n) = g (u n) := by
    filter_upwards [h.filter_mono hr_lim] with n hn
    exact hn
  rw [frequently_iff]
  intro q hq
  have hq' : ∀ᶠ n : ℕ in atTop, u n ∈ q := hu_lim' hq
  obtain ⟨n, hn, heqn⟩ := (hq'.and heq).exists
  exact ⟨u n, hn, heqn⟩

private theorem reciprocalX_eventuallyEq (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    reciprocalX L =ᶠ[𝓝 0] reciprocalX M := by
  have hstate := reciprocalState_eventuallyEq L M h₂ h₃
  have hreal : (fun t : ℝ ↦ reciprocalX L (Complex.ofRealCLM t)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ reciprocalX M (Complex.ofRealCLM t)) :=
    hstate.mono fun _ h ↦ congr_arg Prod.fst h
  exact ((analyticAt_reciprocalX L).frequently_eq_iff_eventually_eq
    (analyticAt_reciprocalX M)).mp
      (frequently_eq_of_eventuallyEq_ofReal hreal)

private theorem weierstrassP_eqOn_compl_lattices (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    Set.EqOn L.weierstrassP M.weierstrassP
      ((L.lattice : Set ℂ) ∪ (M.lattice : Set ℂ))ᶜ := by
  let D : Set ℂ := (L.lattice : Set ℂ) ∪ (M.lattice : Set ℂ) ∪ {0}
  have hLc : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hMc : (M.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := M.lattice)
  have hDc : D.Countable := (hLc.union hMc).union (countable_singleton 0)
  have hx := reciprocalX_eventuallyEq L M h₂ h₃
  have hxmem : {z : ℂ | reciprocalX L z = reciprocalX M z} ∈ 𝓝 0 := hx
  obtain ⟨O, hOsub, hOopen, h0O⟩ := mem_nhds_iff.mp hxmem
  obtain ⟨z₀, hz₀D, hz₀O⟩ := (hDc.dense_compl ℝ).exists_mem_open hOopen ⟨0, h0O⟩
  have hz₀0 : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact hz₀D (Or.inr (Set.mem_singleton 0))
  have hz₀L : z₀ ∉ L.lattice := by
    intro hz
    exact hz₀D (Or.inl (Or.inl hz))
  have hz₀M : z₀ ∉ M.lattice := by
    intro hz
    exact hz₀D (Or.inl (Or.inr hz))
  have hPgerm : L.weierstrassP =ᶠ[𝓝 z₀] M.weierstrassP := by
    filter_upwards [hOopen.mem_nhds hz₀O, isOpen_ne.mem_nhds hz₀0] with z hzO hz0
    have hq := hOsub hzO
    change reciprocalX L z = reciprocalX M z at hq
    rw [reciprocalX_eq_inv L z hz0, reciprocalX_eq_inv M z hz0] at hq
    exact inv_inj.mp hq
  let U : Set ℂ := ((L.lattice : Set ℂ) ∪ (M.lattice : Set ℂ))ᶜ
  have hUpre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (hLc.union hMc)).2
  have hLa : AnalyticOnNhd ℂ L.weierstrassP U := by
    intro z hz
    have hz' : z ∉ L.lattice ∧ z ∉ M.lattice := by simpa [U] using hz
    exact L.analyticOnNhd_weierstrassP z hz'.1
  have hMa : AnalyticOnNhd ℂ M.weierstrassP U := by
    intro z hz
    have hz' : z ∉ L.lattice ∧ z ∉ M.lattice := by simpa [U] using hz
    exact M.analyticOnNhd_weierstrassP z hz'.2
  exact hLa.eqOn_of_preconnected_of_eventuallyEq hMa hUpre
    (by simpa [U] using ⟨hz₀L, hz₀M⟩) hPgerm

/-- The two Weierstrass invariants determine the underlying period lattice. -/
theorem periodPair_lattice_eq_of_g₂_eq_g₃_eq (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    L.lattice = M.lattice := by
  have hP := weierstrassP_eqOn_compl_lattices L M h₂ h₃
  apply le_antisymm
  · intro z hz
    by_contra hzM
    let l : L.lattice := ⟨z, hz⟩
    have heq : L.weierstrassP =ᶠ[𝓝[≠] z] M.weierstrassP := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
          (L.compl_lattice_sdiff_singleton_mem_nhds z),
        mem_nhdsWithin_of_mem_nhds (M.isClosed_lattice.isOpen_compl.mem_nhds hzM),
        self_mem_nhdsWithin] with w hwL hwM hwz
      apply hP
      simp only [mem_compl_iff, mem_union, not_or]
      constructor
      · intro hw
        exact hwL ⟨hw, by simpa using hwz⟩
      · exact hwM
    have hLlim := tendsto_sq_mul_weierstrassP_at_lattice L l
    have hsub : Tendsto (fun w : ℂ ↦ w - z) (𝓝[≠] z) (𝓝 0) := by
      have hc : ContinuousAt (fun w : ℂ ↦ w - z) z := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hMcont : Tendsto M.weierstrassP (𝓝[≠] z)
        (𝓝 (M.weierstrassP z)) :=
      (M.analyticOnNhd_weierstrassP z hzM).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hMlim : Tendsto (fun w : ℂ ↦ (w - z) ^ 2 * M.weierstrassP w)
        (𝓝[≠] z) (𝓝 0) := by
      simpa using (hsub.pow 2).mul hMcont
    have hsame : Tendsto (fun w : ℂ ↦ (w - z) ^ 2 * L.weierstrassP w)
        (𝓝[≠] z) (𝓝 0) := hMlim.congr' <| heq.mono fun w hw ↦ by
      rw [← hw]
    have : (1 : ℂ) = 0 := tendsto_nhds_unique hLlim hsame
    norm_num at this
  · intro z hz
    by_contra hzL
    let l : M.lattice := ⟨z, hz⟩
    have heq : M.weierstrassP =ᶠ[𝓝[≠] z] L.weierstrassP := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
          (M.compl_lattice_sdiff_singleton_mem_nhds z),
        mem_nhdsWithin_of_mem_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hzL),
        self_mem_nhdsWithin] with w hwM hwL hwz
      symm
      apply hP
      simp only [mem_compl_iff, mem_union, not_or]
      constructor
      · exact hwL
      · intro hw
        exact hwM ⟨hw, by simpa using hwz⟩
    have hMlim := tendsto_sq_mul_weierstrassP_at_lattice M l
    have hsub : Tendsto (fun w : ℂ ↦ w - z) (𝓝[≠] z) (𝓝 0) := by
      have hc : ContinuousAt (fun w : ℂ ↦ w - z) z := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hLcont : Tendsto L.weierstrassP (𝓝[≠] z)
        (𝓝 (L.weierstrassP z)) :=
      (L.analyticOnNhd_weierstrassP z hzL).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hLlim : Tendsto (fun w : ℂ ↦ (w - z) ^ 2 * L.weierstrassP w)
        (𝓝[≠] z) (𝓝 0) := by
      simpa using (hsub.pow 2).mul hLcont
    have hsame : Tendsto (fun w : ℂ ↦ (w - z) ^ 2 * M.weierstrassP w)
        (𝓝[≠] z) (𝓝 0) := hLlim.congr' <| heq.mono fun w hw ↦ by
      rw [← hw]
    have : (1 : ℂ) = 0 := tendsto_nhds_unique hMlim hsame
    norm_num at this

end Heights
