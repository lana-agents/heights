import Heights.LatticeQuotientTopology
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option linter.style.header false

/-!
# Topology on the explicit lattice curve point type

For the Weierstrass curve attached to `τ`, mathlib identifies its algebraic
point type with the affine equation locus plus one distinguished point.  This
file introduces a named wrapper around that point type and transports the
one-point-compactification topology through the identification.  The resulting
space is compact and `T1`, and its affine chart is an open embedding.

This is deliberately restricted to the explicit lattice curve; no orphan
topology is installed on arbitrary elliptic-curve point types.  Nothing here
proves continuity or analyticity of `latticePointMap` at its poles, continuity
of the group law, a homeomorphism from `ℂ/L`, or arbitrary-curve
uniformization.
-/

open scoped UpperHalfPlane OnePoint

noncomputable section

namespace Heights

open Topology

/-- The affine equation locus of the explicit lattice Weierstrass curve. -/
abbrev LatticeCurveAffine (τ : ℍ) :=
  {xy : ℂ × ℂ //
    (latticeWeierstrassCurve τ).toAffine.Equation xy.1 xy.2}

/-- A conservative wrapper around the point type of the explicit lattice
curve.  Its separate name keeps the topology below local to this construction. -/
def LatticeCurvePoint (τ : ℍ) :=
  (latticeWeierstrassCurve τ).toAffine.Point

/-- The algebraic point equivalence, viewed as an equivalence with the
one-point extension of the affine equation locus. -/
noncomputable def latticeCurvePointEquiv (τ : ℍ) :
    LatticeCurvePoint τ ≃ OnePoint (LatticeCurveAffine τ) :=
  (latticeWeierstrassCurve τ).toAffine.pointEquiv

/-- The one-point-compactification topology transported to the wrapped
explicit lattice-curve point type. -/
instance latticeCurvePointTopologicalSpace (τ : ℍ) :
    TopologicalSpace (LatticeCurvePoint τ) :=
  TopologicalSpace.induced (latticeCurvePointEquiv τ) inferInstance

/-- The wrapper is homeomorphic to the one-point compactification of its
affine equation locus. -/
noncomputable def latticeCurvePointHomeomorph (τ : ℍ) :
    LatticeCurvePoint τ ≃ₜ OnePoint (LatticeCurveAffine τ) :=
  (latticeCurvePointEquiv τ).toHomeomorphOfIsInducing
    (Topology.IsInducing.induced _)

/-- The distinguished point at infinity in the wrapped curve-point type. -/
def latticeCurvePointInfinity (τ : ℍ) : LatticeCurvePoint τ :=
  .zero

/-- The affine chart map into the wrapped curve-point type. -/
noncomputable def latticeCurvePointOfAffine (τ : ℍ) :
    LatticeCurveAffine τ → LatticeCurvePoint τ :=
  (latticeCurvePointHomeomorph τ).symm ∘
    ((↑) : LatticeCurveAffine τ → OnePoint (LatticeCurveAffine τ))

@[simp] theorem latticeCurvePointHomeomorph_infinity (τ : ℍ) :
    latticeCurvePointHomeomorph τ (latticeCurvePointInfinity τ) =
      (∞ : OnePoint (LatticeCurveAffine τ)) :=
  rfl

@[simp] theorem latticeCurvePointHomeomorph_affine (τ : ℍ)
    (xy : LatticeCurveAffine τ) :
    latticeCurvePointHomeomorph τ (latticeCurvePointOfAffine τ xy) =
      (xy : OnePoint (LatticeCurveAffine τ)) := by
  simp [latticeCurvePointOfAffine]

@[simp] theorem latticeCurvePointOfAffine_eq_mk (τ : ℍ)
    (xy : LatticeCurveAffine τ) :
    latticeCurvePointOfAffine τ xy =
      WeierstrassCurve.Affine.Point.mk xy.2 := by
  rfl

@[simp] theorem latticeCurvePointHomeomorph_symm_infinity (τ : ℍ) :
    (latticeCurvePointHomeomorph τ).symm
        (∞ : OnePoint (LatticeCurveAffine τ)) = latticeCurvePointInfinity τ :=
  rfl

/-- The affine chart is an open embedding. -/
theorem isOpenEmbedding_latticeCurvePointOfAffine (τ : ℍ) :
    IsOpenEmbedding (latticeCurvePointOfAffine τ) :=
  (latticeCurvePointHomeomorph τ).symm.isOpenEmbedding.comp
    OnePoint.isOpenEmbedding_coe

/-- The one-point-compactification topology on the wrapped point type is
compact. -/
noncomputable instance latticeCurvePointCompactSpace (τ : ℍ) :
    CompactSpace (LatticeCurvePoint τ) :=
  (latticeCurvePointHomeomorph τ).symm.compactSpace

/-- The wrapped point type is `T1`; this uses only that its affine equation
locus is a subtype of the Hausdorff space `ℂ × ℂ`. -/
noncomputable instance latticeCurvePointT1Space (τ : ℍ) :
    T1Space (LatticeCurvePoint τ) :=
  (latticeCurvePointHomeomorph τ).symm.t1Space

end Heights
