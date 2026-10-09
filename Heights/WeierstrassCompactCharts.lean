/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
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

The mixed finite/infinity transitions are the rational projective overlap
maps.  Proving both directions holomorphic on their whole overlaps completes
the assembly with a one-dimensional complex-analytic `IsManifold` instance.
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

private theorem complexWeierstrassFinitePointChart_infinityPointChart_apply
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) (z : ℂ)
    (hz : z ∈ ((complexWeierstrassFinitePointChart W P).symm.trans
      (complexWeierstrassInfinityPointChart W)).source) :
    ((complexWeierstrassFinitePointChart W P).symm.trans
      (complexWeierstrassInfinityPointChart W)) z =
      (((complexWeierstrassAffineChartAt W P).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ).1 /
      (((complexWeierstrassAffineChartAt W P).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ).2 := by
  rw [OpenPartialHomeomorph.trans_source] at hz
  let R : ComplexWeierstrassAffine W :=
    (complexWeierstrassAffineChartAt W P).symm z
  have hz2 := hz.2
  change complexWeierstrassPointOfAffine W R ∈
    (complexWeierstrassInfinityPointChart W).source at hz2
  rw [complexWeierstrassInfinityPointChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hz2
  rcases hz2 with ⟨Q, hQsource, hQR⟩
  rw [OpenPartialHomeomorph.trans_apply]
  change complexWeierstrassInfinityPointChart W
    (complexWeierstrassPointOfAffine W R) = _
  rw [← hQR, complexWeierstrassInfinityPointChart_apply_branch]
  have hv :=
    complexWeierstrassInfinityBranch_snd_ne_zero_of_toPoint_eq_affine W Q R hQR
  have hEq := complexWeierstrassAffine_coe_eq_of_branchToPoint_eq W Q R hQR
  have hx := congrArg Prod.fst hEq
  have hy := congrArg Prod.snd hEq
  dsimp only at hx hy
  rw [hx, hy]
  field_simp

/-- The transition from any preferred finite chart to the infinity chart is
analytic on its whole overlap. -/
theorem contDiffOn_complexWeierstrassFinitePointChart_infinityPointChart_transition
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    ContDiffOn ℂ ω
      ((complexWeierstrassFinitePointChart W P).symm.trans
        (complexWeierstrassInfinityPointChart W))
      ((complexWeierstrassFinitePointChart W P).symm.trans
        (complexWeierstrassInfinityPointChart W)).source := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  have hz1 : z ∈ (complexWeierstrassAffineChartAt W P).target := by
    simpa [complexWeierstrassFinitePointChart] using hz.1
  have ha :=
    contDiffAt_complexWeierstrassAffineChartAt_symm_coe_of_mem W P z hz1
  have hy : (((complexWeierstrassAffineChartAt W P).symm z :
      ComplexWeierstrassAffine W) : ℂ × ℂ).2 ≠ 0 := by
    have hz2 := hz.2
    let R : ComplexWeierstrassAffine W :=
      (complexWeierstrassAffineChartAt W P).symm z
    change complexWeierstrassPointOfAffine W R ∈
      (complexWeierstrassInfinityPointChart W).source at hz2
    rw [complexWeierstrassInfinityPointChart,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hz2
    rcases hz2 with ⟨Q, hQsource, hQR⟩
    have hv :=
      complexWeierstrassInfinityBranch_snd_ne_zero_of_toPoint_eq_affine W Q R hQR
    have hEq := complexWeierstrassAffine_coe_eq_of_branchToPoint_eq W Q R hQR
    rw [congrArg Prod.snd hEq]
    exact one_div_ne_zero hv
  apply (ha.fst.div ha.snd hy).contDiffWithinAt.congr_of_mem
  · intro w hw
    exact complexWeierstrassFinitePointChart_infinityPointChart_apply W P w hw
  · rw [OpenPartialHomeomorph.trans_source]
    exact hz

private theorem complexWeierstrassInfinityPointChart_finitePointChart_apply_implicitY
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W)
    (hP : complexWeierstrassEquationY W P.1 ≠ 0) (u : ℂ)
    (hu : u ∈ ((complexWeierstrassInfinityPointChart W).symm.trans
      (complexWeierstrassFinitePointChart W P)).source) :
    ((complexWeierstrassInfinityPointChart W).symm.trans
      (complexWeierstrassFinitePointChart W P)) u =
      (((complexWeierstrassInfinityBranchChart W).symm u :
        ComplexWeierstrassInfinityBranch W) : ℂ × ℂ).1 /
      (((complexWeierstrassInfinityBranchChart W).symm u :
        ComplexWeierstrassInfinityBranch W) : ℂ × ℂ).2 := by
  rw [OpenPartialHomeomorph.trans_source] at hu
  let Q : ComplexWeierstrassInfinityBranch W :=
    (complexWeierstrassInfinityBranchChart W).symm u
  have hu2 := hu.2
  change complexWeierstrassInfinityBranchToPoint W Q ∈
    (complexWeierstrassFinitePointChart W P).source at hu2
  rw [complexWeierstrassFinitePointChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hu2
  rcases hu2 with ⟨R, hRsource, hRQ⟩
  rw [OpenPartialHomeomorph.trans_apply]
  change complexWeierstrassFinitePointChart W P
    (complexWeierstrassInfinityBranchToPoint W Q) = _
  rw [← hRQ, complexWeierstrassFinitePointChart_apply_affine,
    complexWeierstrassAffineChartAt_eq_implicitY W P hP,
    complexWeierstrassImplicitYChart_apply]
  exact congrArg Prod.fst
    (complexWeierstrassAffine_coe_eq_of_branchToPoint_eq W Q R hRQ.symm)

private theorem complexWeierstrassInfinityPointChart_finitePointChart_apply_implicitX
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W)
    (hP : ¬ complexWeierstrassEquationY W P.1 ≠ 0) (u : ℂ)
    (hu : u ∈ ((complexWeierstrassInfinityPointChart W).symm.trans
      (complexWeierstrassFinitePointChart W P)).source) :
    ((complexWeierstrassInfinityPointChart W).symm.trans
      (complexWeierstrassFinitePointChart W P)) u =
      1 / (((complexWeierstrassInfinityBranchChart W).symm u :
        ComplexWeierstrassInfinityBranch W) : ℂ × ℂ).2 := by
  rw [OpenPartialHomeomorph.trans_source] at hu
  let Q : ComplexWeierstrassInfinityBranch W :=
    (complexWeierstrassInfinityBranchChart W).symm u
  have hu2 := hu.2
  change complexWeierstrassInfinityBranchToPoint W Q ∈
    (complexWeierstrassFinitePointChart W P).source at hu2
  rw [complexWeierstrassFinitePointChart,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hu2
  rcases hu2 with ⟨R, hRsource, hRQ⟩
  rw [OpenPartialHomeomorph.trans_apply]
  change complexWeierstrassFinitePointChart W P
    (complexWeierstrassInfinityBranchToPoint W Q) = _
  rw [← hRQ, complexWeierstrassFinitePointChart_apply_affine,
    complexWeierstrassAffineChartAt_eq_implicitX W P hP,
    complexWeierstrassImplicitXChart_apply]
  exact congrArg Prod.snd
    (complexWeierstrassAffine_coe_eq_of_branchToPoint_eq W Q R hRQ.symm)

/-- The transition from the infinity chart to any preferred finite chart is
analytic on its whole overlap. -/
theorem contDiffOn_complexWeierstrassInfinityPointChart_finitePointChart_transition
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    ContDiffOn ℂ ω
      ((complexWeierstrassInfinityPointChart W).symm.trans
        (complexWeierstrassFinitePointChart W P))
      ((complexWeierstrassInfinityPointChart W).symm.trans
        (complexWeierstrassFinitePointChart W P)).source := by
  intro u hu
  rw [OpenPartialHomeomorph.trans_source] at hu
  have hu1 : u ∈ (complexWeierstrassInfinityBranchChart W).target := by
    simpa [complexWeierstrassInfinityPointChart] using hu.1
  have ha :=
    contDiffAt_complexWeierstrassInfinityBranchChart_symm_coe_of_mem W u hu1
  have hv : (((complexWeierstrassInfinityBranchChart W).symm u :
      ComplexWeierstrassInfinityBranch W) : ℂ × ℂ).2 ≠ 0 := by
    let Q : ComplexWeierstrassInfinityBranch W :=
      (complexWeierstrassInfinityBranchChart W).symm u
    have hu2 := hu.2
    change complexWeierstrassInfinityBranchToPoint W Q ∈
      (complexWeierstrassFinitePointChart W P).source at hu2
    rw [complexWeierstrassFinitePointChart,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hu2
    rcases hu2 with ⟨R, hRsource, hRQ⟩
    exact
      complexWeierstrassInfinityBranch_snd_ne_zero_of_toPoint_eq_affine
        W Q R hRQ.symm
  by_cases hP : complexWeierstrassEquationY W P.1 ≠ 0
  · apply (ha.fst.div ha.snd hv).contDiffWithinAt.congr_of_mem
    · intro w hw
      exact
        complexWeierstrassInfinityPointChart_finitePointChart_apply_implicitY
          W P hP w hw
    · rw [OpenPartialHomeomorph.trans_source]
      exact hu
  · apply (contDiffAt_const.div ha.snd hv).contDiffWithinAt.congr_of_mem
    · intro w hw
      exact
        complexWeierstrassInfinityPointChart_finitePointChart_apply_implicitX
          W P hP w hw
    · rw [OpenPartialHomeomorph.trans_source]
      exact hu

private theorem complexWeierstrassPointChartAt_eq_infinity_or_finite
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (Q : ComplexWeierstrassPoint W) :
    complexWeierstrassPointChartAt W Q = complexWeierstrassInfinityPointChart W ∨
      ∃ P : ComplexWeierstrassAffine W,
        complexWeierstrassPointChartAt W Q =
          complexWeierstrassFinitePointChart W P := by
  generalize hq : complexWeierstrassPointHomeomorph W Q = q
  induction q using OnePoint.rec with
  | infty =>
      left
      have hQ : Q = complexWeierstrassPointInfinity W := by
        apply (complexWeierstrassPointHomeomorph W).injective
        rw [hq, complexWeierstrassPointHomeomorph_infinity]
      rw [hQ, complexWeierstrassPointChartAt_infinity]
  | coe P =>
      right
      refine ⟨P, ?_⟩
      have hQ : Q = complexWeierstrassPointOfAffine W P := by
        apply (complexWeierstrassPointHomeomorph W).injective
        rw [hq, complexWeierstrassPointHomeomorph_affine]
      rw [hQ, complexWeierstrassPointChartAt_affine]

private theorem contDiffOn_complexWeierstrassInfinityPointChart_transition
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ContDiffOn ℂ ω
      ((complexWeierstrassInfinityPointChart W).symm.trans
        (complexWeierstrassInfinityPointChart W))
      ((complexWeierstrassInfinityPointChart W).symm.trans
        (complexWeierstrassInfinityPointChart W)).source := by
  apply contDiffOn_id.congr
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  rw [OpenPartialHomeomorph.trans_apply]
  exact (complexWeierstrassInfinityPointChart W).right_inv hz.1

/-- The compact equation-defined Weierstrass point space, with its preferred
finite charts and projective infinity chart, is a one-dimensional complex
analytic manifold. -/
noncomputable instance complexWeierstrassPointIsManifold
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    IsManifold 𝓘(ℂ) ω (ComplexWeierstrassPoint W) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ @ChartedSpace.atlas ℂ _ (ComplexWeierstrassPoint W) _
    (complexWeierstrassPointChartedSpace W) at he
  rcases he with ⟨Q, rfl⟩
  change e' ∈ @ChartedSpace.atlas ℂ _ (ComplexWeierstrassPoint W) _
    (complexWeierstrassPointChartedSpace W) at he'
  rcases he' with ⟨Q', rfl⟩
  rcases complexWeierstrassPointChartAt_eq_infinity_or_finite W Q with
    hQ | ⟨P, hP⟩
  · rw [hQ]
    rcases complexWeierstrassPointChartAt_eq_infinity_or_finite W Q' with
      hQ' | ⟨P', hP'⟩
    · rw [hQ']
      simpa using contDiffOn_complexWeierstrassInfinityPointChart_transition W
    · rw [hP']
      simpa using
        contDiffOn_complexWeierstrassInfinityPointChart_finitePointChart_transition
          W P'
  · rw [hP]
    rcases complexWeierstrassPointChartAt_eq_infinity_or_finite W Q' with
      hQ' | ⟨P', hP'⟩
    · rw [hQ']
      simpa using
        contDiffOn_complexWeierstrassFinitePointChart_infinityPointChart_transition
          W P
    · rw [hP']
      simpa [complexWeierstrassFinitePointChart,
        OpenPartialHomeomorph.lift_openEmbedding_trans] using
          contDiffOn_complexWeierstrassAffineChartAt_transition W P P'

end Heights
