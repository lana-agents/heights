import Heights.WeierstrassFibers
import Heights.LatticePointMapNegation

set_option linter.style.header false

/-!
# Injectivity of the lattice point map

The fiber theorem for `(℘, ℘′)` proves that the total point-valued
Weierstrass map identifies exactly the complex numbers differing by a period.
It follows immediately that the descended map from `ℂ/L` to the explicit
elliptic curve is injective.

This is one half of set-theoretic uniformization. Surjectivity, the Weierstrass
addition theorem, group-law compatibility, and an arbitrary-curve
uniformization theorem remain open.
-/

open scoped UpperHalfPlane
noncomputable section
namespace Heights

/-- The total lattice point map identifies exactly the points differing by a period. -/
theorem latticePointMap_eq_iff_sub_mem (τ : ℍ) (z w : ℂ) :
    latticePointMap τ z = latticePointMap τ w ↔
      z - w ∈ (periodPairOfUpperHalfPlane τ).lattice := by
  let L := periodPairOfUpperHalfPlane τ
  constructor
  · intro heq
    by_cases hz : z ∈ L.lattice
    · by_cases hw : w ∈ L.lattice
      · exact sub_mem hz hw
      · rw [latticePointMap_of_mem τ z hz,
          latticePointMap_of_notMem τ w hw] at heq
        have hnzero : latticeAffinePoint τ w hw ≠ 0 := by
          apply WeierstrassCurve.Affine.Point.some_ne_zero
        exact (hnzero heq.symm).elim
    · by_cases hw : w ∈ L.lattice
      · rw [latticePointMap_of_notMem τ z hz,
          latticePointMap_of_mem τ w hw] at heq
        have hnzero : latticeAffinePoint τ z hz ≠ 0 := by
          apply WeierstrassCurve.Affine.Point.some_ne_zero
        exact (hnzero heq).elim
      · rw [latticePointMap_of_notMem τ z hz,
          latticePointMap_of_notMem τ w hw] at heq
        have hcoords := congr_arg
          (latticeWeierstrassCurve τ).toAffine.pointEquiv heq
        rw [latticeAffinePoint_pointEquiv, latticeAffinePoint_pointEquiv] at hcoords
        have hsubtype := Option.some.inj hcoords
        have hxy := congr_arg Subtype.val hsubtype
        apply (weierstrassP_deriv_eq_iff_sub_mem L z w hz hw).mp
        constructor
        · exact congr_arg Prod.fst hxy
        · have hy := congr_arg Prod.snd hxy
          linear_combination 2 * hy
  · intro hsub
    let l : L.lattice := ⟨z - w, hsub⟩
    have hzw : w + (l : ℂ) = z := by dsimp [l]; ring
    rw [← hzw, latticePointMap_add_lattice]

/-- The descended lattice point map is injective. -/
theorem latticeQuotientPointMap_injective (τ : ℍ) :
    Function.Injective (latticeQuotientPointMap τ) := by
  intro q r heq
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    induction r using QuotientAddGroup.induction_on with
    | _ w =>
      change latticePointMap τ z = latticePointMap τ w at heq
      change (QuotientAddGroup.mk'
        (periodPairOfUpperHalfPlane τ).lattice.toAddSubgroup z) =
          QuotientAddGroup.mk'
            (periodPairOfUpperHalfPlane τ).lattice.toAddSubgroup w
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      exact (latticePointMap_eq_iff_sub_mem τ z w).mp heq

end Heights
