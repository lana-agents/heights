import Heights.Certificates
import Heights.LatticePointMapAddition
import Heights.WeierstrassCurveTopology
import Heights.VariableChangePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

set_option linter.style.header false

/-!
# Algebraic realization of the archimedean parameters

An `ArchimedeanPeriodData K W` parameter has the same modular `j`-value as the
base change of `W` along the corresponding complex embedding.  Over `ℂ`, this
is stronger than an abstract equality of invariants: same-`j` classification
supplies an admissible change of Weierstrass variables from the embedded curve
to the explicit lattice curve.

This removes the possible twisting obstruction after base change to `ℂ`.
The induced point map is packaged below as an additive equivalence. Separately,
`WeierstrassCurveTopology` proves every admissible change is a homeomorphism
for the topology independently constructed from each equation. The repository
still has no complex-manifold atlas or invariant
holomorphic differential on an arbitrary Weierstrass curve, nor integration of
such a differential. Consequently this file does not identify the
formula-defined height with an independently constructed Arakelov/Faltings
height.
-/

open scoped NumberField UpperHalfPlane
open NumberField

noncomputable section
namespace Heights

/-- Under an admissible variable change, the denominator
`2y + a₁x + a₃` of the invariant Weierstrass differential scales by `u³`.
Together with the evident `u²` scaling of the derivative of the transformed
x-coordinate, this is the algebraic calculation behind the usual `u⁻¹`
scaling of the invariant differential.  No differential-form or integration
formalism is hidden in this identity. -/
theorem variableChange_invariantDifferentialDenominator
    {F : Type*} [Field F] (W : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) (x y : F) :
    2 * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
        W.a₁ * (C.u ^ 2 * x + C.r) + W.a₃ =
      C.u ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  simp only [WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]
  ring

/-- The coefficient of the pulled-back invariant differential scales exactly
by `u⁻¹`: the transformed x-coordinate contributes `u²`, while the preceding
denominator contributes `u³`. This is an identity of rational-function values,
including at zeros under Lean's totalized field division; it still does not
define or integrate a differential form. -/
theorem variableChange_invariantDifferentialCoefficient
    {F : Type*} [Field F] (W : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) (x y : F) :
    (C.u : F) ^ 2 /
        (2 * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
          W.a₁ * (C.u ^ 2 * x + C.r) + W.a₃) =
      (C.u⁻¹ : F) /
        (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  rw [variableChange_invariantDifferentialDenominator]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  field_simp [Units.ne_zero]

/-- Every qualifying archimedean parameter gives an actual admissible
algebraic change of variables from the embedded input curve to the explicit
lattice curve.  Thus twists do not survive the base change to `ℂ`.

The coordinate convention for `C • E` is that
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` maps the changed equation back to `E`.
Here `C • (W.map v.embedding)` is the lattice equation, so this coordinate map
runs from the explicit lattice curve to the embedded input curve. -/
theorem ArchimedeanPeriodData.exists_variableChange_to_latticeCurve
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    ∃ C : WeierstrassCurve.VariableChange ℂ,
      C • W.map v.embedding = latticeWeierstrassCurve (p.τ v) := by
  apply WeierstrassCurve.exists_variableChange_of_j_eq
  rw [WeierstrassCurve.map_j, latticeWeierstrassCurve_j]
  exact p.j_eq v

/-- A chosen admissible algebraic change from the embedded input curve to the
explicit lattice curve attached to `p.τ v`. -/
noncomputable def ArchimedeanPeriodData.variableChangeToLatticeCurve
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    WeierstrassCurve.VariableChange ℂ :=
  Classical.choose (p.exists_variableChange_to_latticeCurve W v)

/-- The chosen archimedean variable change really changes the embedded input
equation into the explicit lattice equation. -/
theorem ArchimedeanPeriodData.variableChangeToLatticeCurve_smul
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    p.variableChangeToLatticeCurve W v • W.map v.embedding =
      latticeWeierstrassCurve (p.τ v) :=
  Classical.choose_spec (p.exists_variableChange_to_latticeCurve W v)

/-- For the chosen algebraic realization, the invariant-differential
denominator on the embedded input equation is exactly `u³` times the one on
the lattice equation.  This isolates the routine scaling calculation from the
still-missing differential-form and integration infrastructure. -/
theorem ArchimedeanPeriodData.variableChangeToLatticeCurve_differentialDenominator
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) (x y : ℂ) :
    let C := p.variableChangeToLatticeCurve W v
    2 * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
        (W.map v.embedding).a₁ * (C.u ^ 2 * x + C.r) +
        (W.map v.embedding).a₃ =
      C.u ^ 3 * (2 * y +
        (latticeWeierstrassCurve (p.τ v)).a₁ * x +
        (latticeWeierstrassCurve (p.τ v)).a₃) := by
  dsimp only
  rw [← p.variableChangeToLatticeCurve_smul W v]
  exact variableChange_invariantDifferentialDenominator
    (W.map v.embedding) (p.variableChangeToLatticeCurve W v) x y

/-- The rational coefficient of the invariant differential for the chosen
algebraic realization scales by the expected unit `u⁻¹`. The left numerator is
the derivative coefficient of the transformed x-coordinate. -/
theorem ArchimedeanPeriodData.variableChangeToLatticeCurve_differentialCoefficient
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) (x y : ℂ) :
    let C := p.variableChangeToLatticeCurve W v
    (C.u : ℂ) ^ 2 /
        (2 * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
          (W.map v.embedding).a₁ * (C.u ^ 2 * x + C.r) +
          (W.map v.embedding).a₃) =
      (C.u⁻¹ : ℂ) /
        (2 * y + (latticeWeierstrassCurve (p.τ v)).a₁ * x +
          (latticeWeierstrassCurve (p.τ v)).a₃) := by
  dsimp only
  rw [← p.variableChangeToLatticeCurve_smul W v]
  exact variableChange_invariantDifferentialCoefficient
    (W.map v.embedding) (p.variableChangeToLatticeCurve W v) x y

/-- The chosen admissible variable change induces an additive equivalence from
points on the explicit lattice equation to points on the embedded input
equation. -/
noncomputable def ArchimedeanPeriodData.latticeCurvePointAddEquiv
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    (latticeWeierstrassCurve (p.τ v)).toAffine.Point ≃+
      (W.map v.embedding).toAffine.Point := by
  classical
  rw [← p.variableChangeToLatticeCurve_smul W v]
  exact (p.variableChangeToLatticeCurve W v).pointAddEquiv (W.map v.embedding)

/-- Algebraic uniformization at the level of additive groups: the explicit
lattice quotient maps additively and bijectively to the affine point type of
the embedded input curve. -/
noncomputable def ArchimedeanPeriodData.latticeQuotientToEmbeddedPointAddEquiv
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    LatticeQuotient (p.τ v) ≃+ (W.map v.embedding).toAffine.Point :=
  (latticeQuotientPointMapAddEquiv (p.τ v)).trans
    (p.latticeCurvePointAddEquiv W v)

end Heights
