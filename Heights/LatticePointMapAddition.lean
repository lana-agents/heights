/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.WeierstrassAddition
import Heights.LatticePointMapInjectivity
import Heights.WeierstrassSurjectivity

set_option linter.style.header false

/-!
# Addition compatibility of the lattice point map

The global Weierstrass addition formula is matched here with mathlib's affine
elliptic-curve group law.  After recording the nonvertical secant case, the
tangent case is reduced to three generic secants by choosing an auxiliary
point outside a countable exceptional set.  The total map is therefore
additive in all cases, and its quotient descent is packaged as an additive
equivalence.
-/

open scoped UpperHalfPlane

noncomputable section
namespace Heights

/-- The total lattice point map respects addition when all three arguments are
finite and the corresponding secant is nonvertical. -/
theorem latticePointMap_add_of_notMem_of_weierstrassP_ne (τ : ℍ) (z w : ℂ)
    (hz : z ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hw : w ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hzw : z + w ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hne : (periodPairOfUpperHalfPlane τ).weierstrassP z ≠
      (periodPairOfUpperHalfPlane τ).weierstrassP w) :
    latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w := by
  let L := periodPairOfUpperHalfPlane τ
  have hadd := weierstrass_addition_coordinates L z w hz hw hzw hne
  rw [latticePointMap_of_notMem τ (z + w) hzw,
    latticePointMap_of_notMem τ z hz, latticePointMap_of_notMem τ w hw]
  unfold latticeAffinePoint
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hne]
  congr 1
  · dsimp only [L] at hadd ⊢
    simp only [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope_of_X_ne hne,
      latticeWeierstrassCurve_a₁, latticeWeierstrassCurve_a₂, zero_mul,
      sub_zero]
    rw [← hadd.1]
    unfold weierstrassSecantAddX weierstrassSecantSlope
    field_simp [hne]
    ring
  · dsimp only [L] at hadd ⊢
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope_of_X_ne hne,
      latticeWeierstrassCurve_a₁, latticeWeierstrassCurve_a₂,
      latticeWeierstrassCurve_a₃, zero_mul, sub_zero]
    rw [← hadd.2]
    unfold weierstrassSecantAddY weierstrassSecantAddX
      weierstrassSecantSlope
    field_simp [hne]
    ring

private theorem latticePointMap_add_self_of_notMem (τ : ℍ) (z : ℂ)
    (hz : z ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hzz : z + z ∉ (periodPairOfUpperHalfPlane τ).lattice) :
    latticePointMap τ (z + z) = latticePointMap τ z + latticePointMap τ z := by
  let L := periodPairOfUpperHalfPlane τ
  let A : Set ℂ := (L.lattice : Set ℂ)
  let B : Set ℂ := (fun r : ℂ ↦ z + r) ⁻¹' (L.lattice : Set ℂ)
  let C : Set ℂ := (fun r : ℂ ↦ z - r) ⁻¹' (L.lattice : Set ℂ)
  let D : Set ℂ := (fun r : ℂ ↦ r - z) ⁻¹' (L.lattice : Set ℂ)
  let E : Set ℂ := (fun r : ℂ ↦ r + z) ⁻¹' (L.lattice : Set ℂ)
  let F : Set ℂ := (fun r : ℂ ↦ r + r) ⁻¹' (L.lattice : Set ℂ)
  let S : Set ℂ := ((((A ∪ B) ∪ C) ∪ D) ∪ E) ∪ F
  have hL : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hA : A.Countable := hL
  have hB : B.Countable := hL.preimage (add_right_injective z)
  have hC : C.Countable := hL.preimage sub_right_injective
  have hD : D.Countable := hL.preimage sub_left_injective
  have hE : E.Countable := hL.preimage (add_left_injective z)
  have hF : F.Countable := hL.preimage fun x y h ↦ by
    linear_combination h / 2
  have hS : S.Countable := ((((hA.union hB).union hC).union hD).union hE).union hF
  have hex : ∃ t : ℝ, Complex.ofRealCLM t ∉ S := by
    by_contra h
    push Not at h
    have hpre : ((fun t : ℝ ↦ Complex.ofRealCLM t) ⁻¹' S).Countable :=
      hS.preimage Complex.ofReal_injective
    have hall : (fun t : ℝ ↦ Complex.ofRealCLM t) ⁻¹' S = Set.univ :=
      Set.eq_univ_of_forall h
    rw [hall] at hpre
    exact Set.not_countable_univ hpre
  obtain ⟨t, ht⟩ := hex
  let r : ℂ := Complex.ofRealCLM t
  have hrA : r ∉ A := by
    intro h
    exact ht (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  have hrB : r ∉ B := by
    intro h
    exact ht (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  have hrC : r ∉ C := by
    intro h
    exact ht (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have hrD : r ∉ D := by
    intro h
    exact ht (Or.inl (Or.inl (Or.inr h)))
  have hrE : r ∉ E := by
    intro h
    exact ht (Or.inl (Or.inr h))
  have hrF : r ∉ F := by
    intro h
    exact ht (Or.inr h)
  have hr : r ∉ L.lattice := hrA
  have hzr : z + r ∉ L.lattice := hrB
  have hzmr : z - r ∉ L.lattice := hrC
  have hrr : r + r ∉ L.lattice := hrF
  have hPr : L.weierstrassP z ≠ L.weierstrassP r := by
    intro hp
    rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L z r hz hr).1 hp with
      hm | hp
    · exact hrD (by simpa [D, sub_eq_neg_add, add_comm] using neg_mem hm)
    · exact hrE (by simpa [E, add_comm] using hp)
  have hPnr : L.weierstrassP z ≠ L.weierstrassP (-r) := by
    rw [L.weierstrassP_neg]
    exact hPr
  have hadd₁ := latticePointMap_add_of_notMem_of_weierstrassP_ne τ z r hz hr hzr hPr
  have hnrl : -r ∉ L.lattice := by simpa only [neg_mem_iff] using hr
  have hzneg : z + -r ∉ L.lattice := by simpa [sub_eq_add_neg] using hzmr
  have hadd₂ := latticePointMap_add_of_notMem_of_weierstrassP_ne τ z (-r)
    hz hnrl hzneg hPnr
  have hPsum : L.weierstrassP (z + r) ≠ L.weierstrassP (z - r) := by
    intro hp
    rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L (z + r) (z - r)
      hzr hzmr).1 hp with hm | hp
    · apply hrr
      convert hm using 1
      ring_nf
    · apply hzz
      convert hp using 1
      ring_nf
  have hsum : (z + r) + (z - r) ∉ L.lattice := by
    simpa only [show (z + r) + (z - r) = z + z by ring] using hzz
  have hadd₃ := latticePointMap_add_of_notMem_of_weierstrassP_ne τ
    (z + r) (z - r) hzr hzmr hsum hPsum
  calc
    latticePointMap τ (z + z) =
        latticePointMap τ ((z + r) + (z - r)) := by
      congr 1
      ring_nf
    _ = latticePointMap τ (z + r) + latticePointMap τ (z - r) := hadd₃
    _ = (latticePointMap τ z + latticePointMap τ r) +
        (latticePointMap τ z + latticePointMap τ (-r)) := by
      rw [hadd₁, show z - r = z + -r by ring, hadd₂]
    _ = latticePointMap τ z + latticePointMap τ z := by
      rw [latticePointMap_neg]
      abel

/-- The total lattice point map respects complex addition in all cases. -/
@[simp] theorem latticePointMap_add (τ : ℍ) (z w : ℂ) :
    latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w := by
  let L := periodPairOfUpperHalfPlane τ
  by_cases hz : z ∈ L.lattice
  · let l : L.lattice := ⟨z, hz⟩
    have h := latticePointMap_add_lattice τ w l
    rw [latticePointMap_of_mem τ z hz]
    change latticePointMap τ (z + w) =
      (0 : (latticeWeierstrassCurve τ).toAffine.Point) + latticePointMap τ w
    rw [zero_add]
    simpa [l, add_comm] using h
  by_cases hw : w ∈ L.lattice
  · let l : L.lattice := ⟨w, hw⟩
    rw [latticePointMap_of_mem τ w hw]
    change latticePointMap τ (z + w) = latticePointMap τ z +
      (0 : (latticeWeierstrassCurve τ).toAffine.Point)
    rw [add_zero]
    simpa [l] using latticePointMap_add_lattice τ z l
  by_cases hzw : z + w ∈ L.lattice
  · rw [latticePointMap_of_mem τ (z + w) hzw]
    have heq : latticePointMap τ w = latticePointMap τ (-z) := by
      apply (latticePointMap_eq_iff_sub_mem τ w (-z)).2
      convert hzw using 1
      ring_nf
    rw [heq, latticePointMap_neg, add_neg_cancel]
    rfl
  have hz' : z ∉ L.lattice := hz
  have hw' : w ∉ L.lattice := hw
  have hzw' : z + w ∉ L.lattice := hzw
  by_cases hp : L.weierstrassP z = L.weierstrassP w
  · have hsub : z - w ∈ L.lattice :=
      ((weierstrassP_eq_iff_sub_mem_or_add_mem L z w hz' hw').1 hp).resolve_right hzw
    have hmap : latticePointMap τ w = latticePointMap τ z := by
      symm
      exact (latticePointMap_eq_iff_sub_mem τ z w).2 hsub
    have hsum : latticePointMap τ (z + w) = latticePointMap τ (z + z) := by
      apply (latticePointMap_eq_iff_sub_mem τ (z + w) (z + z)).2
      have hneg : w - z ∈ L.lattice := by
        convert neg_mem hsub using 1
        ring_nf
      convert hneg using 1
      ring_nf
    rw [hsum, hmap]
    exact latticePointMap_add_self_of_notMem τ z hz' (by
      intro htwo
      change z + z ∈ L.lattice at htwo
      have hs : z + z - (z - w) ∈ L.lattice := sub_mem htwo hsub
      apply hzw'
      convert hs using 1
      ring_nf)
  · exact latticePointMap_add_of_notMem_of_weierstrassP_ne τ z w hz' hw' hzw' hp

/-- The descended point map, packaged as an additive equivalence from the
complex lattice quotient to the explicit affine elliptic curve. -/
noncomputable def latticeQuotientPointMapAddEquiv (τ : ℍ) :
    LatticeQuotient τ ≃+ (latticeWeierstrassCurve τ).toAffine.Point where
  toFun := latticeQuotientPointMap τ
  invFun := Function.invFun (latticeQuotientPointMap τ)
  left_inv := Function.leftInverse_invFun (latticeQuotientPointMap_injective τ)
  right_inv := Function.rightInverse_invFun (latticeQuotientPointMap_surjective τ)
  map_add' := by
    intro q₁ q₂
    induction q₁ using QuotientAddGroup.induction_on with
    | _ z =>
      induction q₂ using QuotientAddGroup.induction_on with
      | _ w =>
        change latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w
        exact latticePointMap_add τ z w

end Heights
