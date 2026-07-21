import Heights.VariableChangePoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option linter.style.header false

/-!
# Intrinsic topology on complex Weierstrass curve points

For an arbitrary nonsingular Weierstrass equation over `ℂ`, this file equips a
named wrapper of its affine point type with the one-point-compactification
topology of the affine equation locus.  The construction depends only on the
equation.  It gives a compact `T4` space with an open affine chart.

Admissible variable changes act by their explicit polynomial coordinate maps
on the affine loci.  Those maps are mutually inverse homeomorphisms, and their
extensions fixing infinity give a homeomorphism of the independently
topologized point wrappers.

This is topology only.  No complex atlas, holomorphic structure, invariant
one-form, or analytic uniformization is constructed here.
-/

open scoped OnePoint

noncomputable section

namespace Heights

open Topology

/-- The affine equation locus of a nonsingular complex Weierstrass equation. -/
abbrev ComplexWeierstrassAffine (W : WeierstrassCurve ℂ) :=
  {xy : ℂ × ℂ // W.toAffine.Equation xy.1 xy.2}

/-- A named wrapper around the algebraic point type of a complex Weierstrass
curve.  Its topology below is constructed directly from the equation. -/
def ComplexWeierstrassPoint (W : WeierstrassCurve ℂ) :=
  W.toAffine.Point

/-- The algebraic point equivalence with the one-point extension of the affine
equation locus. -/
noncomputable def complexWeierstrassPointEquiv (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ComplexWeierstrassPoint W ≃ OnePoint (ComplexWeierstrassAffine W) :=
  W.toAffine.pointEquiv

/-- The equation-defined one-point-compactification topology on the wrapped
point type. -/
instance complexWeierstrassPointTopologicalSpace (W : WeierstrassCurve ℂ)
    [W.IsElliptic] : TopologicalSpace (ComplexWeierstrassPoint W) :=
  TopologicalSpace.induced (complexWeierstrassPointEquiv W) inferInstance

/-- The wrapped point type is homeomorphic to the one-point compactification
of its affine equation locus. -/
noncomputable def complexWeierstrassPointHomeomorph (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ComplexWeierstrassPoint W ≃ₜ OnePoint (ComplexWeierstrassAffine W) :=
  (complexWeierstrassPointEquiv W).toHomeomorphOfIsInducing
    (Topology.IsInducing.induced _)

/-- The distinguished point at infinity. -/
def complexWeierstrassPointInfinity (W : WeierstrassCurve ℂ) :
    ComplexWeierstrassPoint W :=
  .zero

/-- The affine chart map into the wrapped point type. -/
noncomputable def complexWeierstrassPointOfAffine (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ComplexWeierstrassAffine W → ComplexWeierstrassPoint W :=
  (complexWeierstrassPointHomeomorph W).symm ∘
    ((↑) : ComplexWeierstrassAffine W → OnePoint (ComplexWeierstrassAffine W))

@[simp] theorem complexWeierstrassPointHomeomorph_infinity
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    complexWeierstrassPointHomeomorph W (complexWeierstrassPointInfinity W) =
      (∞ : OnePoint (ComplexWeierstrassAffine W)) :=
  rfl

@[simp] theorem complexWeierstrassPointHomeomorph_affine
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (xy : ComplexWeierstrassAffine W) :
    complexWeierstrassPointHomeomorph W
        (complexWeierstrassPointOfAffine W xy) =
      (xy : OnePoint (ComplexWeierstrassAffine W)) := by
  simp [complexWeierstrassPointOfAffine]

@[simp] theorem complexWeierstrassPointOfAffine_eq_mk
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (xy : ComplexWeierstrassAffine W) :
    complexWeierstrassPointOfAffine W xy =
      WeierstrassCurve.Affine.Point.mk xy.2 := by
  rfl

@[simp] theorem complexWeierstrassPointHomeomorph_symm_infinity
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    (complexWeierstrassPointHomeomorph W).symm
        (∞ : OnePoint (ComplexWeierstrassAffine W)) =
      complexWeierstrassPointInfinity W :=
  rfl

/-- The affine chart is an open embedding. -/
theorem isOpenEmbedding_complexWeierstrassPointOfAffine
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    IsOpenEmbedding (complexWeierstrassPointOfAffine W) :=
  (complexWeierstrassPointHomeomorph W).symm.isOpenEmbedding.comp
    OnePoint.isOpenEmbedding_coe

/-- The affine equation locus is closed in `ℂ × ℂ`. -/
theorem isClosed_complexWeierstrassAffine (W : WeierstrassCurve ℂ) :
    IsClosed {xy : ℂ × ℂ | W.toAffine.Equation xy.1 xy.2} := by
  simp_rw [W.toAffine.equation_iff]
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- The affine equation locus is locally compact. -/
noncomputable instance complexWeierstrassAffineLocallyCompactSpace
    (W : WeierstrassCurve ℂ) :
    LocallyCompactSpace (ComplexWeierstrassAffine W) :=
  (isClosed_complexWeierstrassAffine W).locallyCompactSpace

/-- The wrapped point type is compact. -/
noncomputable instance complexWeierstrassPointCompactSpace
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    CompactSpace (ComplexWeierstrassPoint W) :=
  (complexWeierstrassPointHomeomorph W).symm.compactSpace

/-- The wrapped point type is `T1`. -/
noncomputable instance complexWeierstrassPointT1Space
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    T1Space (ComplexWeierstrassPoint W) :=
  (complexWeierstrassPointHomeomorph W).symm.t1Space

/-- The wrapped point type is `T4`, hence Hausdorff and regular. -/
noncomputable instance complexWeierstrassPointT4Space
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    T4Space (ComplexWeierstrassPoint W) :=
  (complexWeierstrassPointHomeomorph W).symm.t4Space

/-- The explicit polynomial coordinate homeomorphism between the affine loci
of variable-change-equivalent equations. -/
noncomputable def variableChangeAffineLocusHomeomorph (W : WeierstrassCurve ℂ)
    (C : WeierstrassCurve.VariableChange ℂ) :
    ComplexWeierstrassAffine (C • W) ≃ₜ ComplexWeierstrassAffine W where
  toFun xy :=
    ⟨((C.u : ℂ) ^ 2 * xy.1.1 + C.r,
      (C.u : ℂ) ^ 3 * xy.1.2 + (C.u : ℂ) ^ 2 * C.s * xy.1.1 + C.t),
      (WeierstrassCurve.variableChange_equation_iff W C _ _).mp xy.2⟩
  invFun xy :=
    ⟨(C.inverseX xy.1.1, C.inverseY xy.1.1 xy.1.2),
      (WeierstrassCurve.variableChange_equation_iff W C _ _).mpr (by
        simpa using xy.2)⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv xy := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    dsimp [WeierstrassCurve.VariableChange.inverseX,
      WeierstrassCurve.VariableChange.inverseY]
    fun_prop

/-- A homeomorphism extends to the one-point compactifications by fixing the
point at infinity. -/
noncomputable def onePointHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    OnePoint X ≃ₜ OnePoint Y where
  toFun := OnePoint.map e
  invFun := OnePoint.map e.symm
  left_inv x := by
    induction x using OnePoint.rec <;> simp
  right_inv y := by
    induction y using OnePoint.rec <;> simp
  continuous_toFun := OnePoint.continuous_map e.continuous (by
    change Filter.map e (Filter.coclosedCompact X) ≤ Filter.coclosedCompact Y
    exact le_of_eq e.map_coclosedCompact)
  continuous_invFun := OnePoint.continuous_map e.symm.continuous (by
    change Filter.map e.symm (Filter.coclosedCompact Y) ≤ Filter.coclosedCompact X
    exact le_of_eq e.symm.map_coclosedCompact)

/-- An admissible variable change induces a homeomorphism between point spaces
whose topologies were separately constructed from their equations. -/
noncomputable def variableChangePointHomeomorph (W : WeierstrassCurve ℂ)
    [W.IsElliptic] (C : WeierstrassCurve.VariableChange ℂ) :
    ComplexWeierstrassPoint (C • W) ≃ₜ ComplexWeierstrassPoint W :=
  (complexWeierstrassPointHomeomorph (C • W)).trans
    ((onePointHomeomorph (variableChangeAffineLocusHomeomorph W C)).trans
      (complexWeierstrassPointHomeomorph W).symm)

@[simp] theorem variableChangePointHomeomorph_zero (W : WeierstrassCurve ℂ)
    [W.IsElliptic] (C : WeierstrassCurve.VariableChange ℂ) :
    variableChangePointHomeomorph W C WeierstrassCurve.Affine.Point.zero =
      WeierstrassCurve.Affine.Point.zero :=
  rfl

/-- The topological variable-change map is the existing explicit algebraic
point map. -/
@[simp] theorem variableChangePointHomeomorph_apply (W : WeierstrassCurve ℂ)
    [W.IsElliptic] (C : WeierstrassCurve.VariableChange ℂ)
    (P : (C • W).toAffine.Point) :
    variableChangePointHomeomorph W C P = C.pointMap W P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · rfl

/-- The inverse of the topological variable-change map is the existing
explicit inverse algebraic point map. -/
@[simp] theorem variableChangePointHomeomorph_symm_apply
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ) (P : W.toAffine.Point) :
    (variableChangePointHomeomorph W C).symm P = C.inversePointMap W P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · rfl

end Heights
