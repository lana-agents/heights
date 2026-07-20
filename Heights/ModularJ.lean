import Mathlib

set_option linter.style.header false

/-!
# The modular discriminant and modular j-invariant

This file records the two analytic normalizations used in Silverman's height
formula. Mathlib's modular discriminant is `η ^ 24`, whereas Silverman's
analytic discriminant includes the additional factor `(2π) ^ 12`. The modular
`j`-function uses mathlib's normalized discriminant and has no factor of 1728
in front of `E₄ ^ 3 / Δ`.
-/

open scoped UpperHalfPlane MatrixGroups

open Filter Topology Asymptotics UpperHalfPlane
open Matrix.SpecialLinearGroup CongruenceSubgroup

namespace Heights

/-- Silverman's analytic modular discriminant. The `(2π) ^ 12` factor is
essential for the exact height formula, even though it affects asymptotic
comparisons only by an absolute additive constant. -/
noncomputable def silvermanModularDiscriminant (τ : ℍ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ 12 * ModularForm.discriminant τ

/-- The modular `j`-function in the `q⁻¹ + 744 + ⋯` normalization. -/
noncomputable def modularJ (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- The modular `j`-function is invariant under the integral special linear
group. This is the reduction needed to move a preimage into the standard
fundamental domain. -/
theorem modularJ_smul (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hE : ModularForm.E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * ModularForm.E₄ τ := by
    letI : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) Γ(1) 4 :=
      Gamma_one_coe_eq_SL ▸ inferInstance
    exact SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₄ (mem_Gamma_one γ) τ
  have hD : ModularForm.discriminant (γ • τ) =
      denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    letI : SlashInvariantFormClass (CuspForm 𝒮ℒ 12) Γ(1) 12 :=
      Gamma_one_coe_eq_SL ▸ inferInstance
    exact SlashInvariantForm.slash_action_eqn_SL'' CuspForm.discriminant (mem_Gamma_one γ) τ
  rw [modularJ, modularJ, hE, hD]
  field_simp [denom_ne_zero, ModularForm.discriminant_ne_zero]

/-- Surjectivity of modular `j` would already give a preimage in the standard
fundamental domain. Thus the certificate interface does not require a separate
fundamental-domain existence theorem once surjectivity is available. -/
theorem exists_mem_fd_modularJ_eq_of_surjective
    (hsurj : Function.Surjective modularJ) (z : ℂ) :
    ∃ τ : ℍ, τ ∈ ModularGroup.fd ∧ modularJ τ = z := by
  obtain ⟨τ, hτ⟩ := hsurj z
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨γ • τ, hγ, (modularJ_smul γ τ).trans hτ⟩

/-- Silverman's modular discriminant does not vanish on the upper half-plane. -/
theorem silvermanModularDiscriminant_ne_zero (τ : ℍ) :
    silvermanModularDiscriminant τ ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact ModularForm.discriminant_ne_zero τ

/-- In particular, the norm used as an argument of `Real.log` in the height
formula is strictly positive. -/
theorem silvermanModularDiscriminant_norm_pos (τ : ℍ) :
    0 < ‖silvermanModularDiscriminant τ‖ :=
  norm_pos_iff.mpr (silvermanModularDiscriminant_ne_zero τ)

/-- Clearing the nonzero discriminant denominator recovers `E₄ ^ 3`. -/
theorem modularJ_mul_discriminant (τ : ℍ) :
    modularJ τ * ModularForm.discriminant τ = ModularForm.E₄ τ ^ 3 := by
  exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)

/-- The only zeros of modular `j` on the upper half-plane are the zeros of
`E₄`; the modular discriminant contributes no zeros. -/
theorem modularJ_eq_zero_iff (τ : ℍ) :
    modularJ τ = 0 ↔ ModularForm.E₄ τ = 0 := by
  rw [modularJ, div_eq_zero_iff]
  simp [ModularForm.discriminant_ne_zero τ]

/-- The `q`-product formula with Silverman's normalization kept explicit. -/
theorem silvermanModularDiscriminant_eq_q_prod (τ : ℍ) :
    silvermanModularDiscriminant τ =
      (2 * (Real.pi : ℂ)) ^ 12 *
        (Function.Periodic.qParam 1 τ *
          ∏' n, (1 - ModularForm.eta_q n τ) ^ 24) := by
  rw [silvermanModularDiscriminant, ModularForm.discriminant_eq_q_prod]

/-- The algebraic identity confirming the normalization of the denominator in
`modularJ`. -/
theorem modularJ_denominator_eq_E₄_E₆ (τ : ℍ) :
    ModularForm.discriminant τ =
      (ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2) / 1728 :=
  ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ

/-- The normalized Eisenstein series `E₄` tends to its constant term `1` at
`i∞`. -/
theorem modularE₄_tendsto_atImInfty :
    Tendsto (fun τ : ℍ => ModularForm.E₄ τ) atImInfty (𝓝 1) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
    one_mem_strictPeriods_SL
  have hana := analyticAt_cuspFunction_zero one_pos hper
    (ModularFormClass.holo ModularForm.E₄)
    (ModularFormClass.bdd_at_infty ModularForm.E₄)
  have hvalue : valueAtInfty (ModularForm.E₄ : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos hana hper]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
  have hcusp : Tendsto (cuspFunction 1 (ModularForm.E₄ : ℍ → ℂ))
      (𝓝 0) (𝓝 1) := by
    convert hana.continuousAt.tendsto using 1
    rw [cuspFunction_apply_zero one_pos hana hper, hvalue]
  exact (hcusp.comp (qParam_tendsto_atImInfty one_pos)).congr'
    (Filter.Eventually.of_forall fun τ =>
      SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ
        one_mem_strictPeriods_SL one_ne_zero)

private noncomputable def modularDeltaJComparisonCore (τ : ℍ) : ℝ :=
  -Real.log ‖(2 * (Real.pi : ℂ)) ^ 12‖ -
    Real.log (max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖)

private theorem modularDeltaJComparisonCore_continuous :
    Continuous modularDeltaJComparisonCore := by
  have hE : Continuous (fun τ : ℍ => ‖ModularForm.E₄ τ ^ 3‖) :=
    ((ModularFormClass.continuous ModularForm.E₄).pow 3).norm
  have hD : Continuous (fun τ : ℍ => ‖ModularForm.discriminant τ‖) := by
    simpa only [CuspForm.coe_discriminant] using
      (ModularFormClass.continuous CuspForm.discriminant).norm
  exact continuous_const.sub ((hE.max hD).log fun τ => by
    exact ne_of_gt (lt_of_lt_of_le
      (norm_pos_iff.mpr (ModularForm.discriminant_ne_zero τ))
      (le_max_right _ _)))

private theorem modularDeltaJComparisonCore_tendsto :
    Tendsto modularDeltaJComparisonCore atImInfty
      (𝓝 (-Real.log ‖(2 * (Real.pi : ℂ)) ^ 12‖)) := by
  have hmax : Tendsto
      (fun τ : ℍ => max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖)
      atImInfty (𝓝 1) := by
    simpa using ((modularE₄_tendsto_atImInfty.pow 3).norm.max
      ModularForm.discriminant_isZeroAtImInfty.norm)
  have hlog : Tendsto
      (fun τ : ℍ => Real.log
        (max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖))
      atImInfty (𝓝 0) := by
    simpa using hmax.log one_ne_zero
  have hc : Tendsto
      (fun _ : ℍ => -Real.log ‖(2 * (Real.pi : ℂ)) ^ 12‖)
      atImInfty (𝓝 (-Real.log ‖(2 * (Real.pi : ℂ)) ^ 12‖)) :=
    tendsto_const_nhds
  change Tendsto (fun τ : ℍ =>
    -Real.log ‖(2 * (Real.pi : ℂ)) ^ 12‖ -
      Real.log (max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖))
    atImInfty (𝓝 (-Real.log ‖(2 * (Real.pi : ℂ)) ^ 12‖))
  simpa using hc.sub hlog

private theorem modularDeltaJComparison_eq_core (τ : ℍ) :
    (-Real.log ‖silvermanModularDiscriminant τ‖) -
      Real.log (max ‖modularJ τ‖ 1) = modularDeltaJComparisonCore τ := by
  have hd : ‖ModularForm.discriminant τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (ModularForm.discriminant_ne_zero τ)
  have hd0 : 0 ≤ ‖ModularForm.discriminant τ‖ := norm_nonneg _
  have ha : ‖(2 * (Real.pi : ℂ)) ^ 12‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact pow_ne_zero _ (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hm : max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖ ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le
      (norm_pos_iff.mpr (ModularForm.discriminant_ne_zero τ))
      (le_max_right _ _))
  have hmax :
      max (‖ModularForm.E₄ τ ^ 3‖ / ‖ModularForm.discriminant τ‖) 1 =
        max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖ /
          ‖ModularForm.discriminant τ‖ := by
    calc
      max (‖ModularForm.E₄ τ ^ 3‖ / ‖ModularForm.discriminant τ‖) 1 =
          max (‖ModularForm.E₄ τ ^ 3‖ / ‖ModularForm.discriminant τ‖)
            (‖ModularForm.discriminant τ‖ / ‖ModularForm.discriminant τ‖) := by
              rw [div_self hd]
      _ = _ := max_div_div_right hd0 _ _
  rw [silvermanModularDiscriminant, modularJ, norm_mul, norm_div, hmax,
    Real.log_mul ha hd, Real.log_div hm hd, modularDeltaJComparisonCore]
  ring

/-- On the standard fundamental domain, `-log |Δ_Silv|` and
`log max (|j|, 1)` differ by an absolute bounded amount. -/
theorem modularDeltaJ_fd_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      |(-Real.log ‖silvermanModularDiscriminant τ‖) -
          Real.log (max ‖modularJ τ‖ 1)| ≤ C := by
  have hO : modularDeltaJComparisonCore =O[atImInfty]
      (fun z : ℍ => z.im ^ (0 : ℝ)) := by
    simpa using modularDeltaJComparisonCore_tendsto.isBigO_one ℝ
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO
    modularDeltaJComparisonCore_continuous hO
  refine ⟨max F 0, le_max_right _ _, fun τ hτ => ?_⟩
  rw [modularDeltaJComparison_eq_core]
  calc
    |modularDeltaJComparisonCore τ| = ‖modularDeltaJComparisonCore τ‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ F := by simpa using hF τ hτ
    _ ≤ max F 0 := le_max_left _ _

private theorem scaledDiscriminant_tendsto_atImInfty : Tendsto
    (fun τ : ℍ => ‖ModularForm.discriminant τ‖ /
      Real.exp (-2 * Real.pi * τ.im)) atImInfty (𝓝 1) := by
  have hprod := ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.norm
  rw [show (1 : ℝ) = ‖(1 : ℂ)‖ by norm_num]
  refine hprod.congr' ?_
  filter_upwards with τ
  symm
  rw [ModularForm.discriminant_eq_q_prod, norm_mul]
  have hq : ‖Function.Periodic.qParam 1 τ‖ =
      Real.exp (-2 * Real.pi * τ.im) := by
    simp [Function.Periodic.qParam, Complex.norm_exp]
  rw [hq]
  field_simp

private theorem scaledModularJ_tendsto_atImInfty : Tendsto
    (fun τ : ℍ => ‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im))
    atImInfty (𝓝 1) := by
  have hquot : Tendsto
      (fun τ : ℍ => ‖ModularForm.E₄ τ ^ 3‖ /
        (‖ModularForm.discriminant τ‖ / Real.exp (-2 * Real.pi * τ.im)))
      atImInfty (𝓝 1) := by
    have hh := (modularE₄_tendsto_atImInfty.pow 3).norm.div
      scaledDiscriminant_tendsto_atImInfty (by norm_num)
    simpa only [Pi.div_def, norm_pow, norm_one, one_pow, one_div, inv_one] using hh
  apply hquot.congr'
  filter_upwards with τ
  rw [modularJ, norm_div]
  have he : Real.exp (-2 * Real.pi * τ.im) ≠ 0 := (Real.exp_pos _).ne'
  have hd : ‖ModularForm.discriminant τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (ModularForm.discriminant_ne_zero τ)
  field_simp

private theorem im_tendsto_atImInfty :
    Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := by
  exact tendsto_comap

private theorem exp_two_pi_im_tendsto_atImInfty : Tendsto
    (fun τ : ℍ => Real.exp (2 * Real.pi * τ.im)) atImInfty atTop := by
  exact Real.tendsto_exp_atTop.comp
    (im_tendsto_atImInfty.const_mul_atTop (mul_pos two_pos Real.pi_pos))

private theorem log_max_modularJ_div_im_tendsto : Tendsto
    (fun τ : ℍ => Real.log (max ‖modularJ τ‖ (Real.exp 1)) / τ.im)
    atImInfty (𝓝 (2 * Real.pi)) := by
  have hslog : Tendsto
      (fun τ : ℍ => Real.log
        (‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)))
      atImInfty (𝓝 0) := by
    simpa using scaledModularJ_tendsto_atImInfty.log one_ne_zero
  have hsmall : Tendsto
      (fun τ : ℍ =>
        Real.log (‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)) / τ.im)
      atImInfty (𝓝 0) := hslog.div_atTop im_tendsto_atImInfty
  have hform := (tendsto_const_nhds.add hsmall : Tendsto
    (fun τ : ℍ => 2 * Real.pi +
      Real.log (‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)) / τ.im)
    atImInfty (𝓝 (2 * Real.pi + 0)))
  have hs_half : ∀ᶠ τ in atImInfty,
      (1 / 2 : ℝ) < ‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im) :=
    scaledModularJ_tendsto_atImInfty.eventually (Ioi_mem_nhds (by norm_num))
  have he_large : ∀ᶠ τ in atImInfty,
      2 * Real.exp 1 < Real.exp (2 * Real.pi * τ.im) :=
    exp_two_pi_im_tendsto_atImInfty.eventually
      (eventually_gt_atTop (2 * Real.exp 1))
  rw [← add_zero (2 * Real.pi)]
  apply hform.congr'
  filter_upwards [hs_half, he_large] with τ hs he
  have hy : τ.im ≠ 0 := τ.im_ne_zero
  have hexp_neg : Real.exp (-2 * Real.pi * τ.im) ≠ 0 := (Real.exp_pos _).ne'
  have hj_ne : ‖modularJ τ‖ ≠ 0 := by
    intro hj
    rw [hj, zero_mul] at hs
    linarith
  have hj_eq : ‖modularJ τ‖ =
      (‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)) *
        Real.exp (2 * Real.pi * τ.im) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  have hj_gt : Real.exp 1 < ‖modularJ τ‖ := by
    rw [hj_eq]
    nlinarith [Real.exp_pos 1]
  rw [max_eq_left hj_gt.le]
  rw [Real.log_mul hj_ne hexp_neg, Real.log_exp]
  field_simp
  ring

private noncomputable def modularImLogLogJComparisonCore (τ : ℍ) : ℝ :=
  Real.log τ.im - Real.log (Real.log (max ‖modularJ τ‖ (Real.exp 1)))

private theorem modularImLogLogJComparisonCore_continuous :
    Continuous modularImLogLogJComparisonCore := by
  have hJ : Continuous modularJ := by
    exact (ModularFormClass.continuous ModularForm.E₄).pow 3 |>.div
      (by simpa only [CuspForm.coe_discriminant] using
        ModularFormClass.continuous CuspForm.discriminant)
      (fun τ => ModularForm.discriminant_ne_zero τ)
  have hmax : Continuous (fun τ : ℍ => max ‖modularJ τ‖ (Real.exp 1)) :=
    hJ.norm.max continuous_const
  have hlog_pos : ∀ τ : ℍ,
      0 < Real.log (max ‖modularJ τ‖ (Real.exp 1)) := by
    intro τ
    exact Real.log_pos (lt_of_lt_of_le
      (Real.one_lt_exp_iff.mpr zero_lt_one) (le_max_right _ _))
  exact continuous_im.log (fun τ => τ.im_ne_zero) |>.sub
    ((hmax.log fun τ => ne_of_gt
      (lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _))).log
      fun τ => (hlog_pos τ).ne')

private theorem modularImLogLogJComparisonCore_tendsto :
    Tendsto modularImLogLogJComparisonCore atImInfty
      (𝓝 (-Real.log (2 * Real.pi))) := by
  have hneglog : Tendsto
      (fun τ : ℍ => -Real.log
        (Real.log (max ‖modularJ τ‖ (Real.exp 1)) / τ.im))
      atImInfty (𝓝 (-Real.log (2 * Real.pi))) := by
    exact (log_max_modularJ_div_im_tendsto.log
      (ne_of_gt (mul_pos two_pos Real.pi_pos))).neg
  apply hneglog.congr'
  filter_upwards with τ
  rw [Real.log_div (ne_of_gt (Real.log_pos (lt_of_lt_of_le
      (Real.one_lt_exp_iff.mpr zero_lt_one) (le_max_right _ _)))) τ.im_ne_zero]
  simp only [modularImLogLogJComparisonCore]
  ring

/-- On the standard fundamental domain, `log (im τ)` differs by an absolute
bounded amount from `log log max (|j(τ)|, e)`. -/
theorem modularIm_logLogJ_fd_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      |Real.log τ.im -
        Real.log (Real.log (max ‖modularJ τ‖ (Real.exp 1)))| ≤ C := by
  have hO : modularImLogLogJComparisonCore =O[atImInfty]
      (fun z : ℍ => z.im ^ (0 : ℝ)) := by
    simpa using modularImLogLogJComparisonCore_tendsto.isBigO_one ℝ
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO
    modularImLogLogJComparisonCore_continuous hO
  refine ⟨max F 0, le_max_right _ _, fun τ hτ => ?_⟩
  change |modularImLogLogJComparisonCore τ| ≤ max F 0
  calc
    |modularImLogLogJComparisonCore τ| = ‖modularImLogLogJComparisonCore τ‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ F := by simpa using hF τ hτ
    _ ≤ max F 0 := le_max_left _ _

end Heights
