/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.WeierstrassFiniteAnalytic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option linter.style.header false

/-!
# Complex manifold on the finite Weierstrass locus

The implicit-function charts constructed in
`Heights.WeierstrassFiniteAnalytic` have holomorphic transition maps on their
whole overlaps.  This file packages those transitions and equips the affine
locus of a nonsingular complex Weierstrass equation with its intrinsic
one-dimensional complex-manifold structure.

This is only the finite affine manifold.  It does not construct a chart at
infinity or install a charted-space structure on the compact point type.
-/

open Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Heights

/-- Transition between two finite `x`-coordinate charts is analytic on the
whole overlap. -/
theorem contDiffOn_complexWeierstrassImplicitYChart_transition
    (W : WeierstrassCurve ℂ) (P Q : ComplexWeierstrassAffine W)
    (hP : complexWeierstrassEquationY W P.1 ≠ 0)
    (hQ : complexWeierstrassEquationY W Q.1 ≠ 0) :
    ContDiffOn ℂ ω
      ((complexWeierstrassImplicitYChart W P hP).symm.trans
        (complexWeierstrassImplicitYChart W Q hQ))
      ((complexWeierstrassImplicitYChart W P hP).symm.trans
        (complexWeierstrassImplicitYChart W Q hQ)).source := by
  apply contDiffOn_id.congr
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  rw [OpenPartialHomeomorph.trans_apply,
    complexWeierstrassImplicitYChart_apply]
  exact (complexWeierstrassImplicitYChart W P hP).right_inv hz.1

/-- Transition from an `x`-coordinate chart to a `y`-coordinate chart is
analytic on the whole overlap. -/
theorem contDiffOn_complexWeierstrassImplicitYChart_ImplicitXChart_transition
    (W : WeierstrassCurve ℂ) (P Q : ComplexWeierstrassAffine W)
    (hP : complexWeierstrassEquationY W P.1 ≠ 0)
    (hQ : complexWeierstrassEquationX W Q.1 ≠ 0) :
    ContDiffOn ℂ ω
      ((complexWeierstrassImplicitYChart W P hP).symm.trans
        (complexWeierstrassImplicitXChart W Q hQ))
      ((complexWeierstrassImplicitYChart W P hP).symm.trans
        (complexWeierstrassImplicitXChart W Q hQ)).source := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  have h : ContDiffWithinAt ℂ ω
      (fun z => (((complexWeierstrassImplicitYChart W P hP).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ).2)
      ((complexWeierstrassImplicitYChart W P hP).symm.trans
        (complexWeierstrassImplicitXChart W Q hQ)).source z :=
    (contDiffAt_complexWeierstrassImplicitYChart_symm_coe_of_mem
      W P hP z hz.1).snd.contDiffWithinAt
  have heq :
      (((complexWeierstrassImplicitYChart W P hP).symm.trans
        (complexWeierstrassImplicitXChart W Q hQ)) : ℂ → ℂ) =
      (fun z => (((complexWeierstrassImplicitYChart W P hP).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ).2) := by
    funext z
    rw [OpenPartialHomeomorph.trans_apply,
      complexWeierstrassImplicitXChart_apply]
  rw [heq]
  exact h

/-- Transition from a `y`-coordinate chart to an `x`-coordinate chart is
analytic on the whole overlap. -/
theorem contDiffOn_complexWeierstrassImplicitXChart_ImplicitYChart_transition
    (W : WeierstrassCurve ℂ) (P Q : ComplexWeierstrassAffine W)
    (hP : complexWeierstrassEquationX W P.1 ≠ 0)
    (hQ : complexWeierstrassEquationY W Q.1 ≠ 0) :
    ContDiffOn ℂ ω
      ((complexWeierstrassImplicitXChart W P hP).symm.trans
        (complexWeierstrassImplicitYChart W Q hQ))
      ((complexWeierstrassImplicitXChart W P hP).symm.trans
        (complexWeierstrassImplicitYChart W Q hQ)).source := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  have h : ContDiffWithinAt ℂ ω
      (fun z => (((complexWeierstrassImplicitXChart W P hP).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ).1)
      ((complexWeierstrassImplicitXChart W P hP).symm.trans
        (complexWeierstrassImplicitYChart W Q hQ)).source z :=
    (contDiffAt_complexWeierstrassImplicitXChart_symm_coe_of_mem
      W P hP z hz.1).fst.contDiffWithinAt
  have heq :
      (((complexWeierstrassImplicitXChart W P hP).symm.trans
        (complexWeierstrassImplicitYChart W Q hQ)) : ℂ → ℂ) =
      (fun z => (((complexWeierstrassImplicitXChart W P hP).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ).1) := by
    funext z
    rw [OpenPartialHomeomorph.trans_apply,
      complexWeierstrassImplicitYChart_apply]
  rw [heq]
  exact h

/-- Transition between two finite `y`-coordinate charts is analytic on the
whole overlap. -/
theorem contDiffOn_complexWeierstrassImplicitXChart_transition
    (W : WeierstrassCurve ℂ) (P Q : ComplexWeierstrassAffine W)
    (hP : complexWeierstrassEquationX W P.1 ≠ 0)
    (hQ : complexWeierstrassEquationX W Q.1 ≠ 0) :
    ContDiffOn ℂ ω
      ((complexWeierstrassImplicitXChart W P hP).symm.trans
        (complexWeierstrassImplicitXChart W Q hQ))
      ((complexWeierstrassImplicitXChart W P hP).symm.trans
        (complexWeierstrassImplicitXChart W Q hQ)).source := by
  apply contDiffOn_id.congr
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  rw [OpenPartialHomeomorph.trans_apply,
    complexWeierstrassImplicitXChart_apply]
  exact (complexWeierstrassImplicitXChart W P hP).right_inv hz.1

/-- A preferred finite implicit-function chart at each affine point.  We use
the `x`-coordinate wherever `∂F/∂y ≠ 0`, and otherwise the `y`-coordinate;
nonsingularity guarantees the latter choice is available. -/
noncomputable def complexWeierstrassAffineChartAt
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    OpenPartialHomeomorph (ComplexWeierstrassAffine W) ℂ :=
  if hP : complexWeierstrassEquationY W P.1 ≠ 0 then
    complexWeierstrassImplicitYChart W P hP
  else
    complexWeierstrassImplicitXChart W P
      ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP)

theorem complexWeierstrassAffineChartAt_eq_implicitY
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W)
    (hP : complexWeierstrassEquationY W P.1 ≠ 0) :
    complexWeierstrassAffineChartAt W P =
      complexWeierstrassImplicitYChart W P hP := by
  rw [complexWeierstrassAffineChartAt, dif_pos hP]

theorem complexWeierstrassAffineChartAt_eq_implicitX
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W)
    (hP : ¬ complexWeierstrassEquationY W P.1 ≠ 0) :
    complexWeierstrassAffineChartAt W P =
      complexWeierstrassImplicitXChart W P
        ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP) := by
  rw [complexWeierstrassAffineChartAt, dif_neg hP]

@[simp] theorem complexWeierstrassAffineChartAt_mem_source
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    P ∈ (complexWeierstrassAffineChartAt W P).source := by
  by_cases hP : complexWeierstrassEquationY W P.1 ≠ 0
  · rw [complexWeierstrassAffineChartAt_eq_implicitY W P hP]
    exact complexWeierstrassImplicitYChart_mem_source W P hP
  · rw [complexWeierstrassAffineChartAt_eq_implicitX W P hP]
    exact complexWeierstrassImplicitXChart_mem_source W P
      ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP)

/-- The finite affine locus carries the charted-space structure selected from
its two implicit coordinate directions.  The atlas is exactly the range of
the preferred chart function. -/
noncomputable instance complexWeierstrassAffineChartedSpace
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ChartedSpace ℂ (ComplexWeierstrassAffine W) where
  atlas := Set.range (complexWeierstrassAffineChartAt W)
  chartAt := complexWeierstrassAffineChartAt W
  mem_chart_source := complexWeierstrassAffineChartAt_mem_source W
  chart_mem_atlas := fun P => Set.mem_range_self P

/-- The inverse of a preferred finite chart is analytic in ambient
coordinates at every point of its target. -/
theorem contDiffAt_complexWeierstrassAffineChartAt_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) (z : ℂ)
    (hz : z ∈ (complexWeierstrassAffineChartAt W P).target) :
    ContDiffAt ℂ ω (fun z =>
      (((complexWeierstrassAffineChartAt W P).symm z :
        ComplexWeierstrassAffine W) : ℂ × ℂ)) z := by
  by_cases hP : complexWeierstrassEquationY W P.1 ≠ 0
  · rw [complexWeierstrassAffineChartAt_eq_implicitY W P hP] at hz ⊢
    exact contDiffAt_complexWeierstrassImplicitYChart_symm_coe_of_mem W P hP z hz
  · let hX :=
      (complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP
    rw [complexWeierstrassAffineChartAt_eq_implicitX W P hP] at hz ⊢
    exact contDiffAt_complexWeierstrassImplicitXChart_symm_coe_of_mem W P hX z hz

/-- Any transition between two preferred finite charts is analytic on its
whole overlap. -/
theorem contDiffOn_complexWeierstrassAffineChartAt_transition
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P Q : ComplexWeierstrassAffine W) :
    ContDiffOn ℂ ω
      ((complexWeierstrassAffineChartAt W P).symm.trans
        (complexWeierstrassAffineChartAt W Q))
      ((complexWeierstrassAffineChartAt W P).symm.trans
        (complexWeierstrassAffineChartAt W Q)).source := by
  by_cases hP : complexWeierstrassEquationY W P.1 ≠ 0
  · rw [complexWeierstrassAffineChartAt_eq_implicitY W P hP]
    by_cases hQ : complexWeierstrassEquationY W Q.1 ≠ 0
    · rw [complexWeierstrassAffineChartAt_eq_implicitY W Q hQ]
      exact contDiffOn_complexWeierstrassImplicitYChart_transition W P Q hP hQ
    · rw [complexWeierstrassAffineChartAt_eq_implicitX W Q hQ]
      exact contDiffOn_complexWeierstrassImplicitYChart_ImplicitXChart_transition
        W P Q hP
          ((complexWeierstrassAffine_derivative_ne_zero W Q).resolve_right hQ)
  · rw [complexWeierstrassAffineChartAt_eq_implicitX W P hP]
    by_cases hQ : complexWeierstrassEquationY W Q.1 ≠ 0
    · rw [complexWeierstrassAffineChartAt_eq_implicitY W Q hQ]
      exact contDiffOn_complexWeierstrassImplicitXChart_ImplicitYChart_transition
        W P Q
          ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP) hQ
    · rw [complexWeierstrassAffineChartAt_eq_implicitX W Q hQ]
      exact contDiffOn_complexWeierstrassImplicitXChart_transition W P Q
        ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP)
        ((complexWeierstrassAffine_derivative_ne_zero W Q).resolve_right hQ)

/-- The intrinsic finite affine charted space is a one-dimensional complex
analytic manifold.  Compatibility is proved from the four explicit
whole-overlap transition theorems above. -/
noncomputable instance complexWeierstrassAffineIsManifold
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    IsManifold 𝓘(ℂ) ω (ComplexWeierstrassAffine W) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ @ChartedSpace.atlas ℂ _ (ComplexWeierstrassAffine W) _
    (complexWeierstrassAffineChartedSpace W) at he
  rcases he with ⟨P, rfl⟩
  change e' ∈ @ChartedSpace.atlas ℂ _ (ComplexWeierstrassAffine W) _
    (complexWeierstrassAffineChartedSpace W) at he'
  rcases he' with ⟨Q, rfl⟩
  by_cases hP : complexWeierstrassEquationY W P.1 ≠ 0
  · rw [complexWeierstrassAffineChartAt_eq_implicitY W P hP]
    by_cases hQ : complexWeierstrassEquationY W Q.1 ≠ 0
    · rw [complexWeierstrassAffineChartAt_eq_implicitY W Q hQ]
      simpa using
        contDiffOn_complexWeierstrassImplicitYChart_transition W P Q hP hQ
    · rw [complexWeierstrassAffineChartAt_eq_implicitX W Q hQ]
      simpa using
        contDiffOn_complexWeierstrassImplicitYChart_ImplicitXChart_transition
          W P Q hP
            ((complexWeierstrassAffine_derivative_ne_zero W Q).resolve_right hQ)
  · rw [complexWeierstrassAffineChartAt_eq_implicitX W P hP]
    by_cases hQ : complexWeierstrassEquationY W Q.1 ≠ 0
    · rw [complexWeierstrassAffineChartAt_eq_implicitY W Q hQ]
      simpa using
        contDiffOn_complexWeierstrassImplicitXChart_ImplicitYChart_transition
          W P Q
            ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP) hQ
    · rw [complexWeierstrassAffineChartAt_eq_implicitX W Q hQ]
      simpa using
        contDiffOn_complexWeierstrassImplicitXChart_transition W P Q
          ((complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP)
          ((complexWeierstrassAffine_derivative_ne_zero W Q).resolve_right hQ)

/-- The intrinsic affine manifold embeds analytically in its ambient
coordinate plane.  This is proved in the preferred implicit chart at each
point, using the whole-target analyticity of both graph parametrizations. -/
theorem contMDiff_complexWeierstrassAffine_coe
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (fun P : ComplexWeierstrassAffine W => (P : ℂ × ℂ)) := by
  intro P
  rw [contMDiffAt_iff_source_of_mem_source
    (complexWeierstrassAffineChartAt_mem_source W P)]
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  by_cases hP : complexWeierstrassEquationY W P.1 ≠ 0
  · have hc : chartAt ℂ P = complexWeierstrassImplicitYChart W P hP :=
      complexWeierstrassAffineChartAt_eq_implicitY W P hP
    rw [extChartAt_coe_symm, extChartAt_coe, hc]
    simpa [Function.comp_def] using
      (contDiffAt_complexWeierstrassImplicitYChart_symm_coe W P hP).contDiffWithinAt
  · let hX := (complexWeierstrassAffine_derivative_ne_zero W P).resolve_right hP
    have hc : chartAt ℂ P = complexWeierstrassImplicitXChart W P hX :=
      complexWeierstrassAffineChartAt_eq_implicitX W P hP
    rw [extChartAt_coe_symm, extChartAt_coe, hc]
    simpa [Function.comp_def] using
      (contDiffAt_complexWeierstrassImplicitXChart_symm_coe W P hX).contDiffWithinAt

/-- A map into the intrinsic affine curve is analytic when its two ambient
coordinate functions are analytic.  The equation proof carried by the
subtype contributes no extra analytic data. -/
theorem contMDiff_complexWeierstrassAffine_of_contMDiff_coe
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (f : M → ComplexWeierstrassAffine W)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (fun x => (f x : ℂ × ℂ))) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  intro x
  rw [contMDiffAt_iff_target_of_mem_source
    (complexWeierstrassAffineChartAt_mem_source W (f x))]
  have hfcont : Continuous f := continuous_induced_rng.mpr hf.continuous
  have hf1 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x => (f x).1.1) :=
    (contDiff_fst.contMDiff :
      ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω Prod.fst).comp hf
  have hf2 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x => (f x).1.2) :=
    (contDiff_snd.contMDiff :
      ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω Prod.snd).comp hf
  refine ⟨hfcont.continuousAt, ?_⟩
  rw [extChartAt_coe]
  by_cases hP : complexWeierstrassEquationY W (f x).1 ≠ 0
  · have hc : chartAt ℂ (f x) =
        complexWeierstrassImplicitYChart W (f x) hP :=
      complexWeierstrassAffineChartAt_eq_implicitY W (f x) hP
    rw [hc]
    exact hf1.contMDiffAt
  · let hX :=
      (complexWeierstrassAffine_derivative_ne_zero W (f x)).resolve_right hP
    have hc : chartAt ℂ (f x) =
        complexWeierstrassImplicitXChart W (f x) hX :=
      complexWeierstrassAffineChartAt_eq_implicitX W (f x) hP
    rw [hc]
    exact hf2.contMDiffAt

end Heights
