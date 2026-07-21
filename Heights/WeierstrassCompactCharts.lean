import Heights.WeierstrassFiniteManifold
import Heights.WeierstrassInfinityAnalytic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option linter.style.header false

/-!
# Topological charts on the compact complex Weierstrass curve

This file lifts the intrinsic finite implicit-function charts through the open
affine embedding and combines them with the independently constructed infinity
chart.  The resulting preferred chart at every compact curve point defines a
`ChartedSpace ℂ` whose topology is the equation-defined one-point-
compactification topology.

This is the topological compact-atlas assembly.  Compatibility of the mixed
finite/infinity transitions is not yet packaged as an `IsManifold` instance;
that remaining analytic gluing statement is kept explicit.
-/

open Filter Set
open scoped ContDiff Manifold OnePoint Topology

noncomputable section

namespace Heights

/-- A preferred finite chart, lifted from the affine equation locus to its
open image in the compact point space. -/
noncomputable def complexWeierstrassFinitePointChart
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    OpenPartialHomeomorph (ComplexWeierstrassPoint W) ℂ :=
  (complexWeierstrassAffineChartAt W P).lift_openEmbedding
    (isOpenEmbedding_complexWeierstrassPointOfAffine W)

/-- The affine point defining a lifted finite chart belongs to its source. -/
theorem complexWeierstrassPointOfAffine_mem_finitePointChart_source
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    complexWeierstrassPointOfAffine W P ∈
      (complexWeierstrassFinitePointChart W P).source := by
  rw [complexWeierstrassFinitePointChart,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨P, complexWeierstrassAffineChartAt_mem_source W P, rfl⟩

/-- A lifted finite chart has the same coordinate as its affine ancestor. -/
@[simp] theorem complexWeierstrassFinitePointChart_apply_affine
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P Q : ComplexWeierstrassAffine W) :
    complexWeierstrassFinitePointChart W P
        (complexWeierstrassPointOfAffine W Q) =
      complexWeierstrassAffineChartAt W P Q := by
  rw [complexWeierstrassFinitePointChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

private noncomputable def complexWeierstrassPointChartOfOnePoint
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (Q : OnePoint (ComplexWeierstrassAffine W)) :
    OpenPartialHomeomorph (ComplexWeierstrassPoint W) ℂ := by
  induction Q using OnePoint.rec with
  | infty => exact complexWeierstrassInfinityPointChart W
  | coe P => exact complexWeierstrassFinitePointChart W P

private theorem complexWeierstrassPointHomeomorph_symm_mem_chartOfOnePoint_source
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (Q : OnePoint (ComplexWeierstrassAffine W)) :
    (complexWeierstrassPointHomeomorph W).symm Q ∈
      (complexWeierstrassPointChartOfOnePoint W Q).source := by
  induction Q using OnePoint.rec with
  | infty =>
      exact complexWeierstrassPointInfinity_mem_infinityPointChart_source W
  | coe P =>
      exact complexWeierstrassPointOfAffine_mem_finitePointChart_source W P

/-- The preferred compact chart at a point: the projective `u`-chart at
infinity, and the preferred implicit finite chart at every affine point. -/
noncomputable def complexWeierstrassPointChartAt
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (Q : ComplexWeierstrassPoint W) :
    OpenPartialHomeomorph (ComplexWeierstrassPoint W) ℂ :=
  complexWeierstrassPointChartOfOnePoint W
    (complexWeierstrassPointHomeomorph W Q)

@[simp] theorem complexWeierstrassPointChartAt_infinity
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    complexWeierstrassPointChartAt W (complexWeierstrassPointInfinity W) =
      complexWeierstrassInfinityPointChart W := by
  rfl

@[simp] theorem complexWeierstrassPointChartAt_affine
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    complexWeierstrassPointChartAt W
        (complexWeierstrassPointOfAffine W P) =
      complexWeierstrassFinitePointChart W P := by
  change complexWeierstrassPointChartOfOnePoint W
    (complexWeierstrassPointHomeomorph W
      (complexWeierstrassPointOfAffine W P)) = _
  rw [complexWeierstrassPointHomeomorph_affine]
  rfl

@[simp] theorem complexWeierstrassPointChartAt_mem_source
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (Q : ComplexWeierstrassPoint W) :
    Q ∈ (complexWeierstrassPointChartAt W Q).source := by
  have h :=
    complexWeierstrassPointHomeomorph_symm_mem_chartOfOnePoint_source W
      (complexWeierstrassPointHomeomorph W Q)
  simpa [complexWeierstrassPointChartAt] using h

/-- The compact point space carries the charted-space structure formed by the
preferred finite charts and the projective infinity chart.  This declaration
does not itself assert analytic compatibility of mixed transitions. -/
noncomputable instance complexWeierstrassPointChartedSpace
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ChartedSpace ℂ (ComplexWeierstrassPoint W) where
  atlas := Set.range (complexWeierstrassPointChartAt W)
  chartAt := complexWeierstrassPointChartAt W
  mem_chart_source := complexWeierstrassPointChartAt_mem_source W
  chart_mem_atlas := fun Q => Set.mem_range_self Q

end Heights
