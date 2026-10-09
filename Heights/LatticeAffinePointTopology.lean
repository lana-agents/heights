/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.LatticeCurveTopology

set_option linter.style.header false

/-!
# Continuity of the lattice point map away from its poles

For the explicit lattice curve attached to `τ`, this file expresses the
pole-free point map through the affine equation locus used to topologize
`LatticeCurvePoint τ`.  Differentiability of `℘` and `℘′` away from the period
lattice then proves continuity of the coordinate map and of the wrapped curve-
point map.

This is deliberately only a result on `LatticeComplement τ`.  It does not
prove continuity of `latticePointMap` at a lattice point, continuity of the
descended map on all of `ℂ/L`, analyticity across the point at infinity,
group-law compatibility, bijectivity, or uniformization.
-/

open scoped UpperHalfPlane OnePoint

noncomputable section

namespace Heights

/-- The pair `(℘(z), ℘′(z) / 2)`, valued in the affine equation locus of the
explicit lattice curve. -/
noncomputable def latticeAffineCoordinateMap (τ : ℍ) (z : LatticeComplement τ) :
    LatticeCurveAffine τ :=
  ⟨((periodPairOfUpperHalfPlane τ).weierstrassP z,
      (periodPairOfUpperHalfPlane τ).derivWeierstrassP z / 2),
    weierstrassP_on_latticeWeierstrassCurve τ z z.property⟩

/-- The existing pole-free algebraic point map, regarded as a map to the
wrapped topological curve-point type. -/
noncomputable def latticeAffineCurvePointMap (τ : ℍ) :
    LatticeComplement τ → LatticeCurvePoint τ :=
  latticeCurvePointOfAffine τ ∘ latticeAffineCoordinateMap τ

/-- The underlying coordinate pair of `latticeAffineCoordinateMap`. -/
@[simp] theorem latticeAffineCoordinateMap_val (τ : ℍ) (z : LatticeComplement τ) :
    (latticeAffineCoordinateMap τ z : ℂ × ℂ) =
      ((periodPairOfUpperHalfPlane τ).weierstrassP z,
       (periodPairOfUpperHalfPlane τ).derivWeierstrassP z / 2) :=
  rfl

/-- Repackaging through the affine equation locus does not change the existing
algebraic point map. -/
@[simp] theorem latticeAffineCurvePointMap_eq (τ : ℍ) (z : LatticeComplement τ) :
    latticeAffineCurvePointMap τ z = latticeAffinePointMap τ z := by
  rfl

/-- Under the target homeomorphism, the pole-free point map lies in the affine
chart with its explicit coordinate value. -/
@[simp] theorem latticeAffineCurvePointMap_homeomorph (τ : ℍ)
    (z : LatticeComplement τ) :
    latticeCurvePointHomeomorph τ (latticeAffineCurvePointMap τ z) =
      (latticeAffineCoordinateMap τ z : OnePoint (LatticeCurveAffine τ)) := by
  exact latticeCurvePointHomeomorph_affine τ _

/-- The coordinate-valued Weierstrass map is continuous away from the period
lattice. -/
@[fun_prop] theorem continuous_latticeAffineCoordinateMap (τ : ℍ) :
    Continuous (latticeAffineCoordinateMap τ) := by
  let L := periodPairOfUpperHalfPlane τ
  have hp : Continuous (fun z : LatticeComplement τ ↦ L.weierstrassP z) :=
    L.differentiableOn_weierstrassP.continuousOn.comp_continuous
      continuous_subtype_val (fun z ↦ z.property)
  have hp' : Continuous (fun z : LatticeComplement τ ↦ L.derivWeierstrassP z / 2) :=
    (L.differentiableOn_derivWeierstrassP.continuousOn.comp_continuous
      continuous_subtype_val (fun z ↦ z.property)).div_const 2
  exact (hp.prodMk hp').subtype_mk _

/-- The explicit lattice point map is continuous on the complement of its
poles, for the one-point-compactification topology on its target. -/
@[fun_prop] theorem continuous_latticeAffineCurvePointMap (τ : ℍ) :
    Continuous (latticeAffineCurvePointMap τ) :=
  (isOpenEmbedding_latticeCurvePointOfAffine τ).continuous.comp
    (continuous_latticeAffineCoordinateMap τ)

end Heights
