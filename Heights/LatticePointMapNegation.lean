import Heights.LatticeQuotientPoint

set_option linter.style.header false

/-!
# Negation compatibility of the lattice point map

This file records the first algebraic compatibility of the explicit
Weierstrass point map. Evenness of `℘` and oddness of `℘′` show that complex
negation maps to elliptic-curve negation, both before and after descent to
`ℂ/L`; the origin maps to the point at infinity.

This does not prove compatibility with addition, so it does not package the
map as a group homomorphism. It also does not prove injectivity, surjectivity,
or complex uniformization.
-/

open scoped UpperHalfPlane

noncomputable section

namespace Heights

/-- The origin of `ℂ` maps to the point at infinity. -/
@[simp] theorem latticePointMap_zero (τ : ℍ) :
    latticePointMap τ 0 = 0 :=
  latticePointMap_of_mem τ 0
    (periodPairOfUpperHalfPlane τ).lattice.zero_mem

/-- Complex negation agrees with elliptic-curve negation under the total
lattice point map. -/
@[simp] theorem latticePointMap_neg (τ : ℍ) (z : ℂ) :
    latticePointMap τ (-z) = -latticePointMap τ z := by
  classical
  by_cases hz : z ∈ (periodPairOfUpperHalfPlane τ).lattice
  · have hnz : -z ∈ (periodPairOfUpperHalfPlane τ).lattice := neg_mem hz
    rw [latticePointMap_of_mem τ z hz, latticePointMap_of_mem τ (-z) hnz]
    exact (WeierstrassCurve.Affine.Point.neg_zero).symm
  · have hnz : -z ∉ (periodPairOfUpperHalfPlane τ).lattice := by
      simpa only [neg_mem_iff] using hz
    rw [latticePointMap_of_notMem τ z hz, latticePointMap_of_notMem τ (-z) hnz]
    simp only [latticeAffinePoint, WeierstrassCurve.Affine.Point.mk,
      WeierstrassCurve.Affine.Point.neg_def, WeierstrassCurve.Affine.Point.neg]
    congr 1
    · exact (periodPairOfUpperHalfPlane τ).weierstrassP_neg z
    · rw [(periodPairOfUpperHalfPlane τ).derivWeierstrassP_neg]
      simp [WeierstrassCurve.Affine.negY]
      ring

/-- The zero class in `ℂ/L` maps to the point at infinity. -/
@[simp] theorem latticeQuotientPointMap_zero (τ : ℍ) :
    latticeQuotientPointMap τ 0 = 0 := by
  change latticeQuotientPointMap τ (QuotientAddGroup.mk' _ 0) = 0
  rw [latticeQuotientPointMap_mk, latticePointMap_zero]

/-- Negation on `ℂ/L` agrees with elliptic-curve negation under the descended
point map. -/
@[simp] theorem latticeQuotientPointMap_neg (τ : ℍ) (q : LatticeQuotient τ) :
    latticeQuotientPointMap τ (-q) = -latticeQuotientPointMap τ q := by
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    change latticeQuotientPointMap τ (QuotientAddGroup.mk' _ (-z)) =
      -latticeQuotientPointMap τ (QuotientAddGroup.mk' _ z)
    rw [latticeQuotientPointMap_mk, latticeQuotientPointMap_mk,
      latticePointMap_neg]

end Heights
