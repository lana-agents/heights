import Heights.LatticeQuotientTopology
import Heights.WeierstrassCurveTopology

set_option linter.style.header false

/-!
# Topology on the explicit lattice curve point type

This file specializes the equation-defined topology from
`Heights.WeierstrassCurveTopology` to the explicit lattice curve attached to
`τ`.  The legacy lattice-specific names are retained for the analytic
uniformization files: the point space is compact and `T4`, and its affine
chart is an open embedding.

The construction is no longer restricted in substance to the lattice equation;
it is the specialization of an intrinsic construction available for every
nonsingular complex Weierstrass equation.  Nothing here supplies a complex
atlas or proves analyticity.
-/

open scoped UpperHalfPlane OnePoint

noncomputable section

namespace Heights

open Topology

/-- The affine equation locus of the explicit lattice Weierstrass curve. -/
abbrev LatticeCurveAffine (τ : ℍ) :=
  ComplexWeierstrassAffine (latticeWeierstrassCurve τ)

/-- The wrapped point type of the explicit lattice curve. -/
def LatticeCurvePoint (τ : ℍ) :=
  ComplexWeierstrassPoint (latticeWeierstrassCurve τ)

/-- The algebraic point equivalence with the one-point extension of the affine
locus. -/
noncomputable def latticeCurvePointEquiv (τ : ℍ) :
    LatticeCurvePoint τ ≃ OnePoint (LatticeCurveAffine τ) :=
  complexWeierstrassPointEquiv (latticeWeierstrassCurve τ)

/-- The equation-defined one-point-compactification topology. -/
instance latticeCurvePointTopologicalSpace (τ : ℍ) :
    TopologicalSpace (LatticeCurvePoint τ) :=
  complexWeierstrassPointTopologicalSpace (latticeWeierstrassCurve τ)

/-- The wrapper is homeomorphic to the one-point compactification of its
affine equation locus. -/
noncomputable def latticeCurvePointHomeomorph (τ : ℍ) :
    LatticeCurvePoint τ ≃ₜ OnePoint (LatticeCurveAffine τ) :=
  complexWeierstrassPointHomeomorph (latticeWeierstrassCurve τ)

/-- The distinguished point at infinity in the wrapped curve-point type. -/
def latticeCurvePointInfinity (τ : ℍ) : LatticeCurvePoint τ :=
  complexWeierstrassPointInfinity (latticeWeierstrassCurve τ)

/-- The affine chart map into the wrapped curve-point type. -/
noncomputable def latticeCurvePointOfAffine (τ : ℍ) :
    LatticeCurveAffine τ → LatticeCurvePoint τ :=
  complexWeierstrassPointOfAffine (latticeWeierstrassCurve τ)

@[simp] theorem latticeCurvePointHomeomorph_infinity (τ : ℍ) :
    latticeCurvePointHomeomorph τ (latticeCurvePointInfinity τ) =
      (∞ : OnePoint (LatticeCurveAffine τ)) :=
  complexWeierstrassPointHomeomorph_infinity (latticeWeierstrassCurve τ)

@[simp] theorem latticeCurvePointHomeomorph_affine (τ : ℍ)
    (xy : LatticeCurveAffine τ) :
    latticeCurvePointHomeomorph τ (latticeCurvePointOfAffine τ xy) =
      (xy : OnePoint (LatticeCurveAffine τ)) :=
  complexWeierstrassPointHomeomorph_affine (latticeWeierstrassCurve τ) xy

@[simp] theorem latticeCurvePointOfAffine_eq_mk (τ : ℍ)
    (xy : LatticeCurveAffine τ) :
    latticeCurvePointOfAffine τ xy =
      WeierstrassCurve.Affine.Point.mk xy.2 :=
  complexWeierstrassPointOfAffine_eq_mk (latticeWeierstrassCurve τ) xy

@[simp] theorem latticeCurvePointHomeomorph_symm_infinity (τ : ℍ) :
    (latticeCurvePointHomeomorph τ).symm
        (∞ : OnePoint (LatticeCurveAffine τ)) = latticeCurvePointInfinity τ :=
  complexWeierstrassPointHomeomorph_symm_infinity (latticeWeierstrassCurve τ)

/-- The affine chart is an open embedding. -/
theorem isOpenEmbedding_latticeCurvePointOfAffine (τ : ℍ) :
    IsOpenEmbedding (latticeCurvePointOfAffine τ) :=
  isOpenEmbedding_complexWeierstrassPointOfAffine (latticeWeierstrassCurve τ)

/-- The affine equation locus is closed in `ℂ × ℂ`. -/
theorem isClosed_latticeCurveAffine (τ : ℍ) :
    IsClosed {xy : ℂ × ℂ |
      (latticeWeierstrassCurve τ).toAffine.Equation xy.1 xy.2} :=
  isClosed_complexWeierstrassAffine (latticeWeierstrassCurve τ)

/-- As a closed subspace of `ℂ × ℂ`, the affine equation locus is locally
compact. -/
noncomputable instance latticeCurveAffineLocallyCompactSpace (τ : ℍ) :
    LocallyCompactSpace (LatticeCurveAffine τ) :=
  complexWeierstrassAffineLocallyCompactSpace (latticeWeierstrassCurve τ)

/-- The wrapped point type is compact. -/
noncomputable instance latticeCurvePointCompactSpace (τ : ℍ) :
    CompactSpace (LatticeCurvePoint τ) :=
  complexWeierstrassPointCompactSpace (latticeWeierstrassCurve τ)

/-- The wrapped point type is `T1`. -/
noncomputable instance latticeCurvePointT1Space (τ : ℍ) :
    T1Space (LatticeCurvePoint τ) :=
  complexWeierstrassPointT1Space (latticeWeierstrassCurve τ)

/-- The wrapped point type is `T4`, hence Hausdorff and regular. -/
noncomputable instance latticeCurvePointT4Space (τ : ℍ) :
    T4Space (LatticeCurvePoint τ) :=
  complexWeierstrassPointT4Space (latticeWeierstrassCurve τ)

end Heights
