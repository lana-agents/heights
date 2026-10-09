/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.LatticeQuotientTopology

set_option linter.style.header false

/-!
# Compactness of the complex lattice quotient

A period lattice is a full `ℤ`-lattice in the real vector space `ℂ`.  Mathlib's
`IsZLattice.isCompact_range_of_periodic` theorem therefore makes the range of
the continuous quotient projection compact.  Since that projection is
surjective, this gives a `CompactSpace` instance on `ℂ/L`.

This concerns only the topology of the source quotient.  It does not prove
injectivity or bijectivity of the descended Weierstrass point map, group-law
compatibility, analyticity, a homeomorphism, or uniformization.
-/

open scoped UpperHalfPlane
open Set Topology

noncomputable section

namespace Heights

/-- The range of the projection from `ℂ` to its quotient by the period lattice
is compact. -/
theorem isCompact_range_latticeQuotientMk (τ : ℍ) :
    IsCompact (Set.range (latticeQuotientMk τ)) := by
  apply IsZLattice.isCompact_range_of_periodic
    (periodPairOfUpperHalfPlane τ).lattice (latticeQuotientMk τ)
    (continuous_latticeQuotientMk τ)
  intro z w hw
  change (↑(z + w) : ℂ ⧸ (periodPairOfUpperHalfPlane τ).lattice.toAddSubgroup) = ↑z
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa using hw

/-- The whole lattice quotient is compact. -/
theorem isCompact_univ_latticeQuotient (τ : ℍ) :
    IsCompact (Set.univ : Set (LatticeQuotient τ)) := by
  rw [← (QuotientAddGroup.mk'_surjective
    (periodPairOfUpperHalfPlane τ).lattice.toAddSubgroup).range_eq]
  exact isCompact_range_latticeQuotientMk τ

/-- The quotient `ℂ/L` by the full period lattice is a compact space. -/
noncomputable instance latticeQuotientCompactSpace (τ : ℍ) :
    CompactSpace (LatticeQuotient τ) :=
  isCompact_univ_iff.mp (isCompact_univ_latticeQuotient τ)

end Heights
