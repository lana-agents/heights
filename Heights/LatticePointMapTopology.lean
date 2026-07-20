import Heights.LatticeAffinePointTopology
import Mathlib.Analysis.Meromorphic.Order

set_option linter.style.header false

/-!
# Continuity of the total lattice point map

This file extends the pole-free continuity theorem to the lattice points.  The
order-two pole theorem for `℘` implies that its norm escapes every compact set
near a lattice point.  Since the first coordinate of every compact subset of
the affine curve is compact, the pair `(℘, ℘′ / 2)` escapes every compact
subset of the affine equation locus.  This is exactly convergence to infinity
in its one-point compactification.

Consequently the total point map `ℂ → LatticeCurvePoint τ`, and then its descent
`ℂ/L → LatticeCurvePoint τ`, are continuous.  No analyticity across infinity,
group-law compatibility, bijectivity, complex-torus equivalence, or arbitrary-
curve uniformization is proved here.
-/

open scoped UpperHalfPlane OnePoint
open Set Filter Topology Bornology

noncomputable section

namespace Heights

/-- The total algebraic lattice point map, regarded as a map to the wrapped
topological curve-point type. -/
noncomputable def latticeCurvePointMap (τ : ℍ) : ℂ → LatticeCurvePoint τ :=
  latticePointMap τ

/-- The topological wrapper does not change the underlying total point map. -/
@[simp] theorem latticeCurvePointMap_eq (τ : ℍ) (z : ℂ) :
    latticeCurvePointMap τ z = latticePointMap τ z :=
  rfl

/-- At a period-lattice point, `℘` escapes every compact subset of `ℂ` along
the punctured neighborhood filter. -/
theorem tendsto_weierstrassP_cocompact_at_lattice (τ : ℍ)
    (l : (periodPairOfUpperHalfPlane τ).lattice) :
    Tendsto (periodPairOfUpperHalfPlane τ).weierstrassP (𝓝[≠] (l : ℂ))
      (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact]
  apply tendsto_cobounded_of_meromorphicOrderAt_neg
  rw [(periodPairOfUpperHalfPlane τ).order_weierstrassP l l.property]
  exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- Near a lattice point, the total point map converges to infinity under the
homeomorphism with the one-point compactification of the affine equation
locus. -/
theorem tendsto_latticeCurvePointMap_homeomorph_at_lattice (τ : ℍ)
    (l : (periodPairOfUpperHalfPlane τ).lattice) :
    Tendsto (fun z : ℂ ↦ latticeCurvePointHomeomorph τ (latticeCurvePointMap τ z))
      (𝓝[≠] (l : ℂ)) (𝓝 (∞ : OnePoint (LatticeCurveAffine τ))) := by
  rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
  intro K hK
  let first : LatticeCurveAffine τ → ℂ := fun xy ↦ (xy : ℂ × ℂ).1
  have hfirst : Continuous first := continuous_fst.comp continuous_subtype_val
  have hKfirst : IsCompact (first '' K) := hK.2.image hfirst
  have hP := (Filter.hasBasis_cocompact.tendsto_right_iff.mp
    (tendsto_weierstrassP_cocompact_at_lattice τ l)) (first '' K) hKfirst
  have hlocal : ∀ᶠ z : ℂ in 𝓝[≠] (l : ℂ),
      z ∈ (((periodPairOfUpperHalfPlane τ).lattice : Set ℂ) \ {(l : ℂ)})ᶜ :=
    Filter.Eventually.filter_mono inf_le_left
      ((periodPairOfUpperHalfPlane τ).compl_lattice_sdiff_singleton_mem_nhds l)
  filter_upwards [hP, hlocal, self_mem_nhdsWithin] with z hzP hzlocal hzl
  have hznot : z ∉ (periodPairOfUpperHalfPlane τ).lattice := by
    intro hz
    apply hzlocal
    exact ⟨hz, hzl⟩
  let xy := latticeAffineCoordinateMap τ ⟨z, hznot⟩
  have hxy : xy ∉ K := by
    intro hxyK
    apply hzP
    exact ⟨xy, hxyK, rfl⟩
  have hmap : latticeCurvePointHomeomorph τ (latticeCurvePointMap τ z) =
      (xy : OnePoint (LatticeCurveAffine τ)) := by
    rw [latticeCurvePointMap_eq, latticePointMap_of_notMem τ z hznot]
    change latticeCurvePointHomeomorph τ (latticeAffineCurvePointMap τ ⟨z, hznot⟩) = _
    exact latticeAffineCurvePointMap_homeomorph τ ⟨z, hznot⟩
  rw [hmap]
  exact Or.inl ⟨xy, hxy, rfl⟩

/-- The total point map is continuous at every period-lattice point. -/
theorem continuousAt_latticeCurvePointMap_of_mem (τ : ℍ) (z : ℂ)
    (hz : z ∈ (periodPairOfUpperHalfPlane τ).lattice) :
    ContinuousAt (latticeCurvePointMap τ) z := by
  rw [(latticeCurvePointHomeomorph τ).isInducing.continuousAt_iff]
  apply continuousAt_iff_punctured_nhds.mpr
  have hzinf : latticeCurvePointHomeomorph τ (latticeCurvePointMap τ z) =
      (∞ : OnePoint (LatticeCurveAffine τ)) := by
    rw [latticeCurvePointMap_eq, latticePointMap_of_mem τ z hz]
    exact latticeCurvePointHomeomorph_infinity τ
  rw [show ((latticeCurvePointHomeomorph τ) ∘ latticeCurvePointMap τ) z = ∞ by
    simpa [Function.comp_def] using hzinf]
  let l : (periodPairOfUpperHalfPlane τ).lattice := ⟨z, hz⟩
  simpa [Function.comp_def, l] using
    tendsto_latticeCurvePointMap_homeomorph_at_lattice τ l

/-- The total point map is continuous on the whole complex plane. -/
@[fun_prop] theorem continuous_latticeCurvePointMap (τ : ℍ) :
    Continuous (latticeCurvePointMap τ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ (periodPairOfUpperHalfPlane τ).lattice
  · exact continuousAt_latticeCurvePointMap_of_mem τ z hz
  · have hrestrict : Continuous
        ({z : ℂ | z ∉ (periodPairOfUpperHalfPlane τ).lattice}.restrict
          (latticeCurvePointMap τ)) := by
      change Continuous (fun w : LatticeComplement τ ↦ latticeCurvePointMap τ w)
      apply (continuous_latticeAffineCurvePointMap τ).congr
      intro w
      rw [latticeCurvePointMap_eq, latticePointMap_of_notMem τ w w.property]
      exact (latticeAffineCurvePointMap_eq τ w).symm
    have hon : ContinuousOn (latticeCurvePointMap τ)
        ((periodPairOfUpperHalfPlane τ).lattice : Set ℂ)ᶜ :=
      continuousOn_iff_continuous_restrict.mpr hrestrict
    exact hon.continuousAt
      ((periodPairOfUpperHalfPlane τ).isClosed_lattice.isOpen_compl.mem_nhds hz)

/-- The set-theoretically descended point map, regarded as a map between the
previously topologized lattice quotient and wrapped curve-point type. -/
noncomputable def latticeQuotientCurvePointMap (τ : ℍ) :
    LatticeQuotient τ → LatticeCurvePoint τ :=
  latticeQuotientPointMap τ

/-- The wrapped descended map computes as the wrapped total map on every
quotient representative. -/
@[simp] theorem latticeQuotientCurvePointMap_mk (τ : ℍ) (z : ℂ) :
    latticeQuotientCurvePointMap τ (latticeQuotientMk τ z) =
      latticeCurvePointMap τ z :=
  rfl

/-- The descended point map is continuous for the quotient topology on `ℂ/L`
and the one-point-compactification topology on the explicit target. -/
@[fun_prop] theorem continuous_latticeQuotientCurvePointMap (τ : ℍ) :
    Continuous (latticeQuotientCurvePointMap τ) := by
  rw [(isQuotientMap_latticeQuotientMk τ).continuous_iff]
  change Continuous (latticeCurvePointMap τ)
  exact continuous_latticeCurvePointMap τ

end Heights
