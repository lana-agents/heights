import Heights.WeierstrassDifferential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option linter.style.header false

/-!
# Fibers of the Weierstrass function

The second-order Weierstrass equation gives a locally Lipschitz first-order
system for `(℘, ℘′)`. Real ODE uniqueness, followed by the complex analytic
identity theorem, shows that equal phase-space values have equal translates.
The order-two pole then forces the translation difference to lie in the period
lattice.

Consequently `℘(z) = ℘(w)` exactly when `z` and `w` agree up to a period and
sign, while the ordered pair `(℘, ℘′)` separates classes modulo the lattice.
These fiber theorems are a genuine injectivity input for uniformization. They
do not prove the Weierstrass addition formula, surjectivity, or arbitrary-curve
uniformization.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace Heights

private def wV (L : PeriodPair) : ℂ × ℂ → ℂ × ℂ :=
  fun q ↦ (q.2, 6 * q.1 ^ 2 - L.g₂ / 2)

private def wState (L : PeriodPair) (z : ℂ) : ℝ → ℂ × ℂ :=
  fun t ↦ (L.weierstrassP (z + Complex.ofRealCLM t),
    L.derivWeierstrassP (z + Complex.ofRealCLM t))

private theorem hasDerivAt_wState (L : PeriodPair) (z : ℂ) (t : ℝ)
    (hzt : z + Complex.ofRealCLM t ∉ L.lattice) :
    HasDerivAt (wState L z) (wV L (wState L z t)) t := by
  have hp : HasDerivAt L.weierstrassP
      (L.derivWeierstrassP (z + Complex.ofRealCLM t))
      (z + Complex.ofRealCLM t) := by
    rw [← L.deriv_weierstrassP]
    exact ((L.analyticOnNhd_weierstrassP _ hzt).differentiableAt).hasDerivAt
  have hpp : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP (z + Complex.ofRealCLM t) ^ 2 - L.g₂ / 2)
      (z + Complex.ofRealCLM t) := by
    rw [← deriv_derivWeierstrassP L (z + Complex.ofRealCLM t) hzt]
    exact ((L.analyticOnNhd_derivWeierstrassP _ hzt).differentiableAt).hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ ↦ z + Complex.ofRealCLM s) 1 t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_add z
  change HasDerivAt
    (fun s : ℝ ↦ (L.weierstrassP (z + Complex.ofRealCLM s),
      L.derivWeierstrassP (z + Complex.ofRealCLM s)))
    (L.derivWeierstrassP (z + Complex.ofRealCLM t),
      6 * L.weierstrassP (z + Complex.ofRealCLM t) ^ 2 - L.g₂ / 2) t
  simpa only [Function.comp_apply, mul_one] using
    (hp.comp t hinner).prodMk (hpp.comp t hinner)

private theorem wState_eventually_mem (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    ∀ᶠ t : ℝ in 𝓝 0, z + Complex.ofRealCLM t ∉ L.lattice := by
  have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hc : Continuous (fun t : ℝ ↦ z + Complex.ofRealCLM t) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simpa using hz))

private theorem wState_eventuallyEq (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h0 : L.weierstrassP z = L.weierstrassP w)
    (h1 : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    wState L z =ᶠ[𝓝 0] wState L w := by
  have hV : ContDiff ℝ 1 (wV L) := by
    unfold wV
    fun_prop
  obtain ⟨K, s, hs, hVs⟩ := hV.contDiffAt.exists_lipschitzOnWith
      (x := wState L z 0)
  let S : ℝ → Set (ℂ × ℂ) := fun _ ↦ s
  have hv : ∀ᶠ t : ℝ in 𝓝 0, LipschitzOnWith K (wV L) (S t) :=
    Eventually.of_forall fun _ ↦ hVs
  have hzlocal := wState_eventually_mem L z hz
  have hwlocal := wState_eventually_mem L w hw
  have hsz : ∀ᶠ t : ℝ in 𝓝 0, wState L z t ∈ s := by
    have hinner : ContinuousAt (fun t : ℝ ↦ z + Complex.ofRealCLM t) 0 := by fun_prop
    have hp : ContinuousAt L.weierstrassP z :=
      (L.analyticOnNhd_weierstrassP z hz).continuousAt
    have hpp : ContinuousAt L.derivWeierstrassP z :=
      (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    have hc : ContinuousAt (wState L z) 0 := by
      change ContinuousAt (fun t : ℝ ↦
        (L.weierstrassP (z + Complex.ofRealCLM t),
          L.derivWeierstrassP (z + Complex.ofRealCLM t))) 0
      exact (hp.comp_of_eq hinner (by norm_num)).prodMk
        (hpp.comp_of_eq hinner (by norm_num))
    exact hc.preimage_mem_nhds (by simpa [wState] using hs)
  have hsw : ∀ᶠ t : ℝ in 𝓝 0, wState L w t ∈ s := by
    have hinner : ContinuousAt (fun t : ℝ ↦ w + Complex.ofRealCLM t) 0 := by fun_prop
    have hp : ContinuousAt L.weierstrassP w :=
      (L.analyticOnNhd_weierstrassP w hw).continuousAt
    have hpp : ContinuousAt L.derivWeierstrassP w :=
      (L.analyticOnNhd_derivWeierstrassP w hw).continuousAt
    have hc : ContinuousAt (wState L w) 0 := by
      change ContinuousAt (fun t : ℝ ↦
        (L.weierstrassP (w + Complex.ofRealCLM t),
          L.derivWeierstrassP (w + Complex.ofRealCLM t))) 0
      exact (hp.comp_of_eq hinner (by norm_num)).prodMk
        (hpp.comp_of_eq hinner (by norm_num))
    have hbase : wState L w 0 = wState L z 0 := by
      simp only [wState, Prod.mk.injEq]
      norm_num
      exact ⟨h0.symm, h1.symm⟩
    rw [← hbase] at hs
    exact hc.preimage_mem_nhds hs
  apply ODE_solution_unique_of_eventually (v := fun _ ↦ wV L) (s := S) hv
  · filter_upwards [hzlocal, hsz] with t ht hst
    exact ⟨hasDerivAt_wState L z t ht, hst⟩
  · filter_upwards [hwlocal, hsw] with t ht hst
    exact ⟨hasDerivAt_wState L w t ht, hst⟩
  · simp only [wState, Prod.mk.injEq]
    norm_num
    exact ⟨h0, h1⟩

private theorem translate_eventuallyEq (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h0 : L.weierstrassP z = L.weierstrassP w)
    (h1 : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    (fun u : ℂ ↦ L.weierstrassP (z + u)) =ᶠ[𝓝 0]
      (fun u : ℂ ↦ L.weierstrassP (w + u)) := by
  have hstate := wState_eventuallyEq L z w hz hw h0 h1
  have hreal : ∀ᶠ t : ℝ in 𝓝 0,
      L.weierstrassP (z + Complex.ofRealCLM t) =
        L.weierstrassP (w + Complex.ofRealCLM t) :=
    hstate.mono fun t ht ↦ congr_arg Prod.fst ht
  let r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let u : ℕ → ℂ := fun n ↦ Complex.ofRealCLM (r n)
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    simpa [r] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hu_lim : Tendsto u atTop (𝓝 (0 : ℂ)) := by
    exact Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hr_lim
  have hu_ne : ∀ n, u n ≠ 0 := by
    intro n
    dsimp [u, r]
    intro h
    have hre := congr_arg Complex.re h
    simp only [Complex.ofReal_re] at hre
    exact (one_div_ne_zero (by positivity)) hre
  have hu_lim' : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_inf.2
    exact ⟨hu_lim, tendsto_principal.2 (Eventually.of_forall hu_ne)⟩
  have heq : ∀ᶠ n : ℕ in atTop,
      L.weierstrassP (z + u n) = L.weierstrassP (w + u n) := by
    have := hreal.filter_mono hr_lim
    simpa [u, r] using this
  have hfreq : ∃ᶠ u : ℂ in 𝓝[≠] 0,
      L.weierstrassP (z + u) = L.weierstrassP (w + u) := by
    rw [frequently_iff]
    intro s hs
    have hs' : ∀ᶠ n : ℕ in atTop, u n ∈ s := hu_lim' hs
    obtain ⟨n, hn, heqn⟩ := (hs'.and heq).exists
    exact ⟨u n, hn, heqn⟩
  have hf : AnalyticAt ℂ (fun u : ℂ ↦ L.weierstrassP (z + u)) 0 := by
    change AnalyticAt ℂ (L.weierstrassP ∘ fun u : ℂ ↦ z + u) 0
    have hi : AnalyticAt ℂ (fun u : ℂ ↦ z + u) 0 := by fun_prop
    have ho : AnalyticAt ℂ L.weierstrassP (z + 0) := by
      simpa using L.analyticOnNhd_weierstrassP z hz
    exact ho.comp hi
  have hg : AnalyticAt ℂ (fun u : ℂ ↦ L.weierstrassP (w + u)) 0 := by
    change AnalyticAt ℂ (L.weierstrassP ∘ fun u : ℂ ↦ w + u) 0
    have hi : AnalyticAt ℂ (fun u : ℂ ↦ w + u) 0 := by fun_prop
    have ho : AnalyticAt ℂ L.weierstrassP (w + 0) := by
      simpa using L.analyticOnNhd_weierstrassP w hw
    exact ho.comp hi
  exact (hf.frequently_eq_iff_eventually_eq hg).mp hfreq

/-- Equality of `℘` and `℘′` at two non-poles forces their difference to be a
period. This is the ODE-uniqueness input behind the fibers of `℘`. -/
theorem sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq (L : PeriodPair)
    (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h0 : L.weierstrassP z = L.weierstrassP w)
    (h1 : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    z - w ∈ L.lattice := by
  let A : Set ℂ := (fun u : ℂ ↦ z + u) ⁻¹' (L.lattice : Set ℂ)
  let B : Set ℂ := (fun u : ℂ ↦ w + u) ⁻¹' (L.lattice : Set ℂ)
  let U : Set ℂ := (A ∪ B)ᶜ
  have hlattice : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hA : A.Countable := hlattice.preimage fun _ _ h ↦ add_left_cancel h
  have hB : B.Countable := hlattice.preimage fun _ _ h ↦ add_left_cancel h
  have hUpre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (hA.union hB)).2
  have hAclosed : IsClosed A := L.isClosed_lattice.preimage (by fun_prop)
  have hBclosed : IsClosed B := L.isClosed_lattice.preimage (by fun_prop)
  have h0U : (0 : ℂ) ∈ U := by
    simp [U, A, B, hz, hw]
  have hf : AnalyticOnNhd ℂ (fun u : ℂ ↦ L.weierstrassP (z + u)) U := by
    intro u hu
    have hu' : z + u ∉ L.lattice ∧ w + u ∉ L.lattice := by
      simpa [U, A, B] using hu
    change AnalyticAt ℂ (L.weierstrassP ∘ fun v : ℂ ↦ z + v) u
    have hi : AnalyticAt ℂ (fun v : ℂ ↦ z + v) u := by fun_prop
    exact (L.analyticOnNhd_weierstrassP (z + u) hu'.1).comp hi
  have hg : AnalyticOnNhd ℂ (fun u : ℂ ↦ L.weierstrassP (w + u)) U := by
    intro u hu
    have hu' : z + u ∉ L.lattice ∧ w + u ∉ L.lattice := by
      simpa [U, A, B] using hu
    change AnalyticAt ℂ (L.weierstrassP ∘ fun v : ℂ ↦ w + v) u
    have hi : AnalyticAt ℂ (fun v : ℂ ↦ w + v) u := by fun_prop
    exact (L.analyticOnNhd_weierstrassP (w + u) hu'.2).comp hi
  have hlocal := translate_eventuallyEq L z w hz hw h0 h1
  have hglobal : Set.EqOn (fun u : ℂ ↦ L.weierstrassP (z + u))
      (fun u : ℂ ↦ L.weierstrassP (w + u)) U :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg hUpre h0U hlocal
  by_contra hd
  let u0 : ℂ := -w
  have hzu0 : z + u0 = z - w := by simp [u0, sub_eq_add_neg]
  have hwu0 : w + u0 = 0 := by simp [u0]
  have hAnear : ∀ᶠ u : ℂ in 𝓝 u0, u ∉ A := by
    have hopen : IsOpen Aᶜ := hAclosed.isOpen_compl
    exact hopen.mem_nhds (by simpa [A, hzu0] using hd)
  have hBnear : ∀ᶠ u : ℂ in 𝓝[≠] u0, u ∉ B := by
    have hlocalB : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ),
        t ∉ (L.lattice : Set ℂ) := by
      have hlocal' : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ),
          t ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ :=
        Filter.Eventually.filter_mono inf_le_left
          (L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ))
      filter_upwards [hlocal', self_mem_nhdsWithin] with t ht ht0
      intro htl
      exact ht ⟨htl, ht0⟩
    have htend : Tendsto (fun u : ℂ ↦ w + u) (𝓝[≠] u0) (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_inf.2
      constructor
      · rw [← hwu0]
        exact Filter.Tendsto.mono_left
          (continuousAt_const.add continuousAt_id :
            ContinuousAt (fun u : ℂ ↦ w + u) u0) inf_le_left
      · apply tendsto_principal.2
        filter_upwards [self_mem_nhdsWithin] with u hu
        intro hwu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu hwu
        apply hu
        dsimp [u0]
        linear_combination hwu
    exact hlocalB.filter_mono htend
  have hevent : (fun u : ℂ ↦ L.weierstrassP (z + u)) =ᶠ[𝓝[≠] u0]
      (fun u : ℂ ↦ L.weierstrassP (w + u)) := by
    have hAnear' : ∀ᶠ u : ℂ in 𝓝[≠] u0, u ∉ A :=
      Filter.Eventually.filter_mono inf_le_left hAnear
    filter_upwards [hAnear', hBnear] with u huA huB
    exact hglobal (by simp [U, huA, huB])
  have horder := meromorphicOrderAt_congr hevent
  have hfcomp : meromorphicOrderAt (fun u : ℂ ↦ L.weierstrassP (z + u)) u0 =
      meromorphicOrderAt L.weierstrassP (z - w) := by
    change meromorphicOrderAt (L.weierstrassP ∘ fun u : ℂ ↦ z + u) u0 = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
    simp [u0, sub_eq_add_neg]
  have hgcomp : meromorphicOrderAt (fun u : ℂ ↦ L.weierstrassP (w + u)) u0 =
      meromorphicOrderAt L.weierstrassP 0 := by
    change meromorphicOrderAt (L.weierstrassP ∘ fun u : ℂ ↦ w + u) u0 = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
    simp [u0]
  rw [hfcomp, hgcomp, L.order_weierstrassP 0 L.lattice.zero_mem] at horder
  have han : AnalyticAt ℂ L.weierstrassP (z - w) :=
    L.analyticOnNhd_weierstrassP (z - w) hd
  have hnonneg : (0 : WithTop ℤ) ≤
      meromorphicOrderAt L.weierstrassP (z - w) := by
    rw [han.meromorphicOrderAt_eq]
    cases analyticOrderAt L.weierstrassP (z - w) <;> simp
  rw [horder] at hnonneg
  have hneg : (-2 : WithTop ℤ) < 0 := WithTop.coe_lt_coe.mpr (by norm_num)
  exact (not_le_of_gt hneg) hnonneg

/-- The fibers of `℘` away from its poles are exactly the two classes related
by negation. -/
theorem weierstrassP_eq_iff_sub_mem_or_add_mem (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    L.weierstrassP z = L.weierstrassP w ↔
      z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  constructor
  · intro hp
    have hzrel := L.derivWeierstrassP_sq z hz
    have hwrel := L.derivWeierstrassP_sq w hw
    have hp' : L.derivWeierstrassP z ^ 2 = L.derivWeierstrassP w ^ 2 := by
      rw [hzrel, hwrel, hp]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp' with hp' | hp'
    · exact Or.inl <|
        sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq L z w hz hw hp hp'
    · have hnwp : -w ∉ L.lattice := by simpa only [neg_mem_iff] using hw
      apply Or.inr
      convert sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq L z (-w) hz hnwp
          (by simpa using hp) (by simpa using hp') using 1
      all_goals ring
  · rintro (hsub | hadd)
    · let l : L.lattice := ⟨z - w, hsub⟩
      have hzw : w + (l : ℂ) = z := by dsimp [l]; ring
      rw [← hzw, L.weierstrassP_add_coe]
    · let l : L.lattice := ⟨z + w, hadd⟩
      have hzw : -w + (l : ℂ) = z := by dsimp [l]; ring
      rw [← hzw, L.weierstrassP_add_coe, L.weierstrassP_neg]

/-- The ordered pair `(℘, ℘′)` separates classes modulo the period lattice. -/
theorem weierstrassP_deriv_eq_iff_sub_mem (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    (L.weierstrassP z = L.weierstrassP w ∧
      L.derivWeierstrassP z = L.derivWeierstrassP w) ↔
      z - w ∈ L.lattice := by
  constructor
  · rintro ⟨hp, hp'⟩
    exact sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq L z w hz hw hp hp'
  · intro hsub
    let l : L.lattice := ⟨z - w, hsub⟩
    have hzw : w + (l : ℂ) = z := by dsimp [l]; ring
    constructor
    · rw [← hzw, L.weierstrassP_add_coe]
    · rw [← hzw, L.derivWeierstrassP_add_coe]

end Heights
