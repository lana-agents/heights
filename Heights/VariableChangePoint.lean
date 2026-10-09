/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option linter.style.header false

/-!
# Point maps induced by Weierstrass variable changes

An admissible variable change of Weierstrass equations induces the expected
coordinate equivalence on affine elliptic-curve points.  This file packages
that algebraic equivalence and proves compatibility with the group law.
-/

noncomputable section
namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- The Weierstrass equation transforms under the documented affine coordinate
map `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
theorem variableChange_equation_iff (W : WeierstrassCurve F)
    (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r)
        (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  rw [Affine.equation_iff, Affine.equation_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  constructor <;> intro h <;> linear_combination h

namespace VariableChange

variable (C : VariableChange F)

/-- The inverse x-coordinate for the affine coordinate map of `C`. -/
def inverseX (x : F) : F :=
  (C.u⁻¹ : F) ^ 2 * (x - C.r)

/-- The inverse y-coordinate for the affine coordinate map of `C`. -/
def inverseY (x y : F) : F :=
  (C.u⁻¹ : F) ^ 3 * (y - C.s * (x - C.r) - C.t)

@[simp] theorem forward_inverseX (x : F) :
    (C.u : F) ^ 2 * C.inverseX x + C.r = x := by
  simp only [inverseX]
  field_simp [Units.ne_zero]
  ring

@[simp] theorem forward_inverseY (x y : F) :
    (C.u : F) ^ 3 * C.inverseY x y +
        (C.u : F) ^ 2 * C.s * C.inverseX x + C.t = y := by
  simp only [inverseX, inverseY]
  field_simp [Units.ne_zero]
  ring

@[simp] theorem inverseX_forward (x : F) :
    C.inverseX ((C.u : F) ^ 2 * x + C.r) = x := by
  simp only [inverseX]
  field_simp [Units.ne_zero]
  ring

@[simp] theorem inverseY_forward (x y : F) :
    C.inverseY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) = y := by
  simp only [inverseY]
  field_simp [Units.ne_zero]
  ring

/-- Negation commutes with the affine coordinate transformation. -/
theorem negY_forward (W : WeierstrassCurve F) (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.negY x y +
        (C.u : F) ^ 2 * C.s * x + C.t := by
  simp only [Affine.negY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- The x-coordinate addition formula commutes with an admissible variable
change, provided the slope is transformed by `ℓ ↦ uℓ + s`. -/
theorem addX_forward (W : WeierstrassCurve F) (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s) =
      (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp only [Affine.addX, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- The y-coordinate addition formula commutes with an admissible variable
change, provided the slope is transformed by `ℓ ↦ uℓ + s`. -/
theorem addY_forward (W : WeierstrassCurve F) (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) * ℓ + C.s) =
      (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ +
        (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX,
    variableChange_a₁, variableChange_a₂, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- A nonvertical secant or tangent slope transforms by `ℓ ↦ uℓ + s`. -/
theorem slope_forward [DecidableEq F] (W : WeierstrassCurve F)
    (x₁ x₂ y₁ y₂ : F)
    (h₁ : (C • W).toAffine.Equation x₁ y₁)
    (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t) =
      (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h ↦ hxy ⟨hx, h⟩
    have hy_eq : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst x₂
    subst y₂
    have hY :
        (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t ≠
          W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [C.negY_forward W]
      intro h
      apply hy
      apply mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u))
      linear_combination h
    have hden : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hDen :
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) -
          W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ≠ 0 :=
      sub_ne_zero.mpr hY
    rw [Affine.slope_of_Y_ne rfl hY, Affine.slope_of_Y_ne rfl hy]
    apply (div_eq_iff hDen).2
    field_simp [hden, Units.ne_zero]
    simp only [Affine.negY, variableChange_a₁, variableChange_a₂,
      variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero]
    ring
  · have hX : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      intro h
      apply hx
      apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero C.u))
      linear_combination h
    rw [Affine.slope_of_X_ne hX, Affine.slope_of_X_ne hx]
    field_simp [Units.ne_zero, hx]
    ring

variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- The map on affine elliptic-curve points induced by an admissible variable
change. The point at infinity is fixed and finite coordinates transform by
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def pointMap : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((variableChange_equation_iff W C x y).mp h.1)

@[simp] theorem pointMap_zero : C.pointMap W .zero = .zero := rfl

@[simp] theorem pointMap_some (x y : F) (h : (C • W).toAffine.Nonsingular x y) :
    C.pointMap W (.some x y h) =
      .mk ((variableChange_equation_iff W C x y).mp h.1) := rfl

/-- The point map induced by an admissible variable change preserves the
elliptic-curve group law. -/
theorem pointMap_add [DecidableEq F] (P Q : (C • W).toAffine.Point) :
    C.pointMap W (P + Q) = C.pointMap W P + C.pointMap W Q := by
  classical
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · rfl
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · rfl
  let X₁ := (C.u : F) ^ 2 * x₁ + C.r
  let X₂ := (C.u : F) ^ 2 * x₂ + C.r
  let Y₁ := (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
  let Y₂ := (C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · have hX : X₁ = X₂ := by simp only [X₁, X₂, hxy.1]
    have hY : Y₁ = W.toAffine.negY X₂ Y₂ := by
      simp only [X₂, Y₁, Y₂]
      rw [C.negY_forward W, hxy.1, hxy.2]
    rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    simp only [pointMap_some, Affine.Point.mk]
    exact (Affine.Point.add_of_Y_eq hX hY).symm
  · have hX_of_eq : X₁ = X₂ → x₁ = x₂ := by
      intro h
      apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero C.u))
      dsimp only [X₁, X₂] at h
      linear_combination h
    have hXY : ¬(X₁ = X₂ ∧ Y₁ = W.toAffine.negY X₂ Y₂) := by
      rintro ⟨hX, hY⟩
      apply hxy
      have hx := hX_of_eq hX
      refine ⟨hx, ?_⟩
      dsimp only [X₁, X₂, Y₁, Y₂] at hY
      rw [C.negY_forward W] at hY
      apply mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u))
      rw [hx] at hY
      linear_combination hY
    rw [Affine.Point.add_some hxy]
    simp only [pointMap_some, Affine.Point.mk]
    rw [Affine.Point.add_some hXY]
    have hslope := C.slope_forward W x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    dsimp only [X₁, X₂, Y₁, Y₂] at hslope ⊢
    rw [Affine.Point.some.injEq]
    constructor
    · rw [hslope, C.addX_forward W]
    · rw [hslope, C.addY_forward W]

/-- The inverse point map, written in explicit affine coordinates. -/
def inversePointMap : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((variableChange_equation_iff W C (C.inverseX x) (C.inverseY x y)).mpr <| by
      simpa using h.1)

@[simp] theorem inversePointMap_zero : C.inversePointMap W .zero = .zero := rfl

@[simp] theorem inversePointMap_some (x y : F) (h : W.toAffine.Nonsingular x y) :
    C.inversePointMap W (.some x y h) =
      .mk ((variableChange_equation_iff W C (C.inverseX x) (C.inverseY x y)).mpr <| by
        simpa using h.1) := rfl

/-- The equivalence of affine point types induced by an admissible variable
change of Weierstrass equations. -/
def pointEquiv : (C • W).toAffine.Point ≃ W.toAffine.Point where
  toFun := C.pointMap W
  invFun := C.inversePointMap W
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · change Affine.Point.some
        (C.inverseX ((C.u : F) ^ 2 * x + C.r))
        (C.inverseY ((C.u : F) ^ 2 * x + C.r)
          ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)) _ =
          Affine.Point.some x y h
      congr <;> simp
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · change Affine.Point.some
        ((C.u : F) ^ 2 * C.inverseX x + C.r)
        ((C.u : F) ^ 3 * C.inverseY x y +
          (C.u : F) ^ 2 * C.s * C.inverseX x + C.t) _ =
          Affine.Point.some x y h
      congr <;> simp

@[simp] theorem pointEquiv_apply (P : (C • W).toAffine.Point) :
    C.pointEquiv W P = C.pointMap W P := rfl

@[simp] theorem pointEquiv_symm_apply (P : W.toAffine.Point) :
    (C.pointEquiv W).symm P = C.inversePointMap W P := rfl

/-- The additive equivalence of affine elliptic-curve points induced by an
admissible variable change. -/
def pointAddEquiv [DecidableEq F] :
    (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toEquiv := C.pointEquiv W
  map_add' := C.pointMap_add W

@[simp] theorem pointAddEquiv_apply [DecidableEq F]
    (P : (C • W).toAffine.Point) :
    C.pointAddEquiv W P = C.pointMap W P := rfl

@[simp] theorem pointAddEquiv_symm_apply [DecidableEq F]
    (P : W.toAffine.Point) :
    (C.pointAddEquiv W).symm P = C.inversePointMap W P := rfl

end VariableChange
end WeierstrassCurve
