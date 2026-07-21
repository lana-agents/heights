import Heights.WeierstrassFiniteManifold
import Mathlib.Geometry.Manifold.Diffeomorph

set_option linter.style.header false

/-!
# Analyticity of Weierstrass variable changes

An admissible change of Weierstrass variables is polynomial in both affine
coordinates, and its inverse is polynomial as well (the unit `u` is fixed).
This file packages the resulting ambient biholomorphism of `ℂ × ℂ` and proves
that the affine-locus homeomorphism constructed from the two equations is its
restriction.

The ambient maps restrict to a biholomorphism for the intrinsic finite
implicit-function manifolds.  This remains an affine result: it does not put a
complex-manifold structure on the one-point compactification and does not
claim that the global elliptic-curve point map is biholomorphic at infinity.
-/

open scoped ContDiff Manifold

noncomputable section

namespace Heights

/-- The ambient affine coordinate change
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` and its explicit inverse. -/
noncomputable def variableChangeAffineAmbientEquiv
    (C : WeierstrassCurve.VariableChange ℂ) :
    (ℂ × ℂ) ≃ (ℂ × ℂ) where
  toFun xy :=
    ((C.u : ℂ) ^ 2 * xy.1 + C.r,
      (C.u : ℂ) ^ 3 * xy.2 + (C.u : ℂ) ^ 2 * C.s * xy.1 + C.t)
  invFun xy := (C.inverseX xy.1, C.inverseY xy.1 xy.2)
  left_inv xy := by
    apply Prod.ext <;> simp
  right_inv xy := by
    apply Prod.ext <;> simp

/-- The ambient affine coordinate change is a complex-analytic
`Diffeomorph`, i.e. a biholomorphism of `ℂ × ℂ`. -/
noncomputable def variableChangeAffineAmbientBiholomorph
    (C : WeierstrassCurve.VariableChange ℂ) :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ) ω where
  toEquiv := variableChangeAffineAmbientEquiv C
  contMDiff_toFun := (show ContDiff ℂ ω
      (variableChangeAffineAmbientEquiv C) by
    dsimp [variableChangeAffineAmbientEquiv]
    fun_prop).contMDiff
  contMDiff_invFun := (show ContDiff ℂ ω
      (variableChangeAffineAmbientEquiv C).symm by
    dsimp [variableChangeAffineAmbientEquiv,
      WeierstrassCurve.VariableChange.inverseX,
      WeierstrassCurve.VariableChange.inverseY]
    fun_prop).contMDiff

@[simp] theorem variableChangeAffineAmbientBiholomorph_apply
    (C : WeierstrassCurve.VariableChange ℂ) (xy : ℂ × ℂ) :
    variableChangeAffineAmbientBiholomorph C xy =
      ((C.u : ℂ) ^ 2 * xy.1 + C.r,
        (C.u : ℂ) ^ 3 * xy.2 + (C.u : ℂ) ^ 2 * C.s * xy.1 + C.t) :=
  rfl

@[simp] theorem variableChangeAffineAmbientBiholomorph_symm_apply
    (C : WeierstrassCurve.VariableChange ℂ) (xy : ℂ × ℂ) :
    (variableChangeAffineAmbientBiholomorph C).symm xy =
      (C.inverseX xy.1, C.inverseY xy.1 xy.2) :=
  rfl

/-- The previously constructed homeomorphism of affine equation loci is
exactly the restriction of the ambient biholomorphism. -/
@[simp] theorem variableChangeAffineLocusHomeomorph_coe
    (W : WeierstrassCurve ℂ) (C : WeierstrassCurve.VariableChange ℂ)
    (xy : ComplexWeierstrassAffine (C • W)) :
    ((variableChangeAffineLocusHomeomorph W C xy :
        ComplexWeierstrassAffine W) : ℂ × ℂ) =
      variableChangeAffineAmbientBiholomorph C (xy : ℂ × ℂ) :=
  rfl

/-- The inverse affine-locus homeomorphism is the restriction of the inverse
ambient biholomorphism. -/
@[simp] theorem variableChangeAffineLocusHomeomorph_symm_coe
    (W : WeierstrassCurve ℂ) (C : WeierstrassCurve.VariableChange ℂ)
    (xy : ComplexWeierstrassAffine W) :
    (((variableChangeAffineLocusHomeomorph W C).symm xy :
        ComplexWeierstrassAffine (C • W)) : ℂ × ℂ) =
      (variableChangeAffineAmbientBiholomorph C).symm (xy : ℂ × ℂ) :=
  rfl

/-- An admissible variable change is analytic between the independently
constructed intrinsic finite manifolds. -/
theorem contMDiff_variableChangeAffineLocusHomeomorph
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (variableChangeAffineLocusHomeomorph W C) := by
  apply contMDiff_complexWeierstrassAffine_of_contMDiff_coe W
  have h := (variableChangeAffineAmbientBiholomorph C).contMDiff.comp
    (contMDiff_complexWeierstrassAffine_coe (C • W))
  simpa [Function.comp_def] using h

/-- The explicit inverse variable change is analytic between the intrinsic
finite manifolds. -/
theorem contMDiff_variableChangeAffineLocusHomeomorph_symm
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (variableChangeAffineLocusHomeomorph W C).symm := by
  apply contMDiff_complexWeierstrassAffine_of_contMDiff_coe (C • W)
  have h := (variableChangeAffineAmbientBiholomorph C).symm.contMDiff.comp
    (contMDiff_complexWeierstrassAffine_coe W)
  simpa [Function.comp_def] using h

/-- The finite affine-locus homeomorphism, bundled as a biholomorphism for the
intrinsic implicit-function manifold structures. -/
noncomputable def variableChangeAffineLocusBiholomorph
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (ComplexWeierstrassAffine (C • W)) (ComplexWeierstrassAffine W) ω where
  toEquiv := (variableChangeAffineLocusHomeomorph W C).toEquiv
  contMDiff_toFun := contMDiff_variableChangeAffineLocusHomeomorph W C
  contMDiff_invFun := contMDiff_variableChangeAffineLocusHomeomorph_symm W C

@[simp] theorem variableChangeAffineLocusBiholomorph_apply
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ)
    (P : ComplexWeierstrassAffine (C • W)) :
    variableChangeAffineLocusBiholomorph W C P =
      variableChangeAffineLocusHomeomorph W C P :=
  rfl

@[simp] theorem variableChangeAffineLocusBiholomorph_symm_apply
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ)
    (P : ComplexWeierstrassAffine W) :
    (variableChangeAffineLocusBiholomorph W C).symm P =
      (variableChangeAffineLocusHomeomorph W C).symm P :=
  rfl

end Heights
