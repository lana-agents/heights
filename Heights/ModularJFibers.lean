/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.PeriodPairScaling
import Heights.LatticeWeierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

set_option linter.style.header false

/-!
# Fibers of the modular j-function

Equality of modular `j`-values gives an isomorphism between the corresponding
short lattice curves.  The transformation laws for `c₄` and `c₆`, together
with rigidity of the Weierstrass invariants, identify their period lattices up
to homothety.  Comparing integral bases then produces an element of
`SL(2, ℤ)` carrying one upper-half-plane parameter to the other.
-/

open scoped UpperHalfPlane MatrixGroups Manifold Modular
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup

noncomputable section
namespace Heights

/-- The lattice curve's `c₆` invariant is `216 g₃`. -/
theorem latticeWeierstrassCurve_c6 (τ : ℍ) :
    (latticeWeierstrassCurve τ).c₆ =
      216 * (periodPairOfUpperHalfPlane τ).g₃ := by
  simp [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, latticeWeierstrassCurve]
  ring

private theorem exists_scale_lattice_eq_of_modularJ_eq (τ τ' : ℍ)
    (hj : modularJ τ = modularJ τ') :
    ∃ (a : ℂ) (ha : a ≠ 0),
      (periodPairScale a ha (periodPairOfUpperHalfPlane τ)).lattice =
        (periodPairOfUpperHalfPlane τ').lattice := by
  have hcurves : (latticeWeierstrassCurve τ).j =
      (latticeWeierstrassCurve τ').j := by
    rw [latticeWeierstrassCurve_j, latticeWeierstrassCurve_j, hj]
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (latticeWeierstrassCurve τ) (latticeWeierstrassCurve τ') hcurves
  let a : ℂ := C.u
  have ha : a ≠ 0 := Units.ne_zero C.u
  refine ⟨a, ha, ?_⟩
  apply periodPair_lattice_eq_of_g₂_eq_g₃_eq
  · have hc := congrArg WeierstrassCurve.c₄ hC
    rw [WeierstrassCurve.variableChange_c₄, latticeWeierstrassCurve_c4,
      latticeWeierstrassCurve_c4] at hc
    rw [Units.val_inv_eq_inv_val] at hc
    rw [periodPairScale_g₂]
    dsimp [a]
    linear_combination hc / 12
  · have hc := congrArg WeierstrassCurve.c₆ hC
    rw [WeierstrassCurve.variableChange_c₆, latticeWeierstrassCurve_c6,
      latticeWeierstrassCurve_c6] at hc
    rw [Units.val_inv_eq_inv_val] at hc
    rw [periodPairScale_g₃]
    dsimp [a]
    linear_combination hc / 216

private theorem int_linear_combination_injective (τ : ℍ)
    {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = (m' : ℂ) * τ + n') :
    m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  norm_num at him
  have hm : m = m' := him.resolve_right τ.im_ne_zero
  subst m'
  norm_num at h
  exact ⟨rfl, h⟩

/-- Equal modular `j`-values lie in the same integral modular-group orbit. -/
theorem exists_smul_eq_of_modularJ_eq (τ τ' : ℍ)
    (hj : modularJ τ = modularJ τ') :
    ∃ γ : SL(2, ℤ), γ • τ' = τ := by
  obtain ⟨a, ha, hlat⟩ := exists_scale_lattice_eq_of_modularJ_eq τ τ' hj
  let L := periodPairOfUpperHalfPlane τ
  let L' := periodPairOfUpperHalfPlane τ'
  let S := periodPairScale a ha L
  have haτmem : a * (τ : ℂ) ∈ L'.lattice := by
    rw [← hlat]
    exact S.ω₁_mem_lattice
  have hamem : a ∈ L'.lattice := by
    rw [← hlat]
    simpa [L, S] using S.ω₂_mem_lattice
  obtain ⟨A, B, hA⟩ := PeriodPair.mem_lattice.mp haτmem
  obtain ⟨C, D, hC⟩ := PeriodPair.mem_lattice.mp hamem
  have hA' : (A : ℂ) * τ' + B = a * τ := by simpa [L'] using hA
  have hC' : (C : ℂ) * τ' + D = a := by simpa [L'] using hC
  have hτ'mem : (τ' : ℂ) ∈ S.lattice := by
    rw [hlat]
    exact L'.ω₁_mem_lattice
  have h1mem : (1 : ℂ) ∈ S.lattice := by
    rw [hlat]
    exact L'.ω₂_mem_lattice
  obtain ⟨P, Q, hP⟩ := PeriodPair.mem_lattice.mp hτ'mem
  obtain ⟨R, T, hR⟩ := PeriodPair.mem_lattice.mp h1mem
  have hP' : (P : ℂ) * (a * τ) + Q * a = τ' := by
    simpa [S, L] using hP
  have hR' : (R : ℂ) * (a * τ) + T * a = 1 := by
    simpa [S, L] using hR
  have hPA : P * A + Q * C = 1 ∧ P * B + Q * D = 0 := by
    apply int_linear_combination_injective τ'
    calc
      ((P * A + Q * C : ℤ) : ℂ) * τ' + (P * B + Q * D : ℤ) =
          (P : ℂ) * ((A : ℂ) * τ' + B) +
            (Q : ℂ) * ((C : ℂ) * τ' + D) := by push_cast; ring
      _ = (P : ℂ) * (a * τ) + Q * a := by rw [hA', hC']
      _ = (1 : ℤ) * (τ' : ℂ) + (0 : ℤ) := by simpa using hP'
  have hRA : R * A + T * C = 0 ∧ R * B + T * D = 1 := by
    apply int_linear_combination_injective τ'
    calc
      ((R * A + T * C : ℤ) : ℂ) * τ' + (R * B + T * D : ℤ) =
          (R : ℂ) * ((A : ℂ) * τ' + B) +
            (T : ℂ) * ((C : ℂ) * τ' + D) := by push_cast; ring
      _ = (R : ℂ) * (a * τ) + T * a := by rw [hA', hC']
      _ = (0 : ℤ) * (τ' : ℂ) + (1 : ℤ) := by simpa using hR'
  have hdetprod : (P * T - Q * R) * (A * D - B * C) = 1 := by
    rw [mul_sub, sub_mul]
    nlinarith [hPA.1, hPA.2, hRA.1, hRA.2]
  have hdet_cases : A * D - B * C = 1 ∨ A * D - B * C = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetprod with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hτeq : (τ : ℂ) =
      ((A : ℂ) * τ' + B) / ((C : ℂ) * τ' + D) := by
    rw [hC']
    field_simp [ha]
    simpa [mul_comm] using hA'.symm
  have hformula :
      (((A : ℂ) * τ' + B) / ((C : ℂ) * τ' + D)).im =
        ((A * D - B * C : ℤ) : ℝ) * τ'.im /
          Complex.normSq ((C : ℂ) * τ' + D) := by
    rw [Complex.div_im]
    norm_num
    ring
  have hdet : A * D - B * C = 1 := by
    rcases hdet_cases with h | h
    · exact h
    · exfalso
      rw [h] at hformula
      norm_num at hformula
      rw [← hτeq] at hformula
      have hnorm : 0 < Complex.normSq ((C : ℂ) * τ' + D) := by
        rw [hC']
        exact Complex.normSq_pos.mpr ha
      have hneg : -τ'.im / Complex.normSq ((C : ℂ) * τ' + D) < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos τ'.im_pos) hnorm
      have htneg : τ.im < 0 := by
        rw [← UpperHalfPlane.coe_im, hformula]
        exact hneg
      exact (not_lt_of_ge τ.im_pos.le) htneg
  let γ : SL(2, ℤ) := ⟨!![A, B; C, D], by
    simp [Matrix.det_fin_two, hdet]⟩
  refine ⟨γ, ?_⟩
  rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_specialLinearGroup_apply]
  change num γ τ' / denom γ τ' = (τ : ℂ)
  simp only [γ, num, denom, Matrix.SpecialLinearGroup.toGL]
  exact hτeq.symm

/-- Silverman's modular discriminant has weight twelve under the modular group. -/
theorem silvermanModularDiscriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    silvermanModularDiscriminant (γ • τ) =
      denom γ τ ^ (12 : ℕ) * silvermanModularDiscriminant τ := by
  have hD : ModularForm.discriminant (γ • τ) =
      denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    letI : SlashInvariantFormClass (CuspForm 𝒮ℒ 12) Γ(1) 12 :=
      Gamma_one_coe_eq_SL ▸ inferInstance
    exact SlashInvariantForm.slash_action_eqn_SL'' CuspForm.discriminant
      (mem_Gamma_one γ) τ
  rw [silvermanModularDiscriminant, silvermanModularDiscriminant, hD]
  ac_rfl

/-- The Petersson-normalized absolute discriminant is invariant under
`SL(2, ℤ)`. -/
theorem silvermanModularDiscriminant_norm_mul_im_pow_smul
    (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖silvermanModularDiscriminant (γ • τ)‖ * (γ • τ).im ^ 6 =
      ‖silvermanModularDiscriminant τ‖ * τ.im ^ 6 := by
  rw [silvermanModularDiscriminant_smul, norm_mul, norm_pow,
    ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have hn : ‖denom γ τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  field_simp

/-- The Petersson-normalized absolute discriminant depends only on the modular
`j`-value.  No fundamental-domain hypotheses are needed. -/
theorem silvermanModularDiscriminant_norm_mul_im_pow_eq_of_modularJ_eq
    (τ τ' : ℍ) (hj : modularJ τ = modularJ τ') :
    ‖silvermanModularDiscriminant τ‖ * τ.im ^ 6 =
      ‖silvermanModularDiscriminant τ'‖ * τ'.im ^ 6 := by
  obtain ⟨γ, rfl⟩ := exists_smul_eq_of_modularJ_eq τ τ' hj
  exact silvermanModularDiscriminant_norm_mul_im_pow_smul γ τ'

end Heights
