import Heights.WeierstrassCurveTopology
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option linter.style.header false

/-!
# Finite analytic germs on complex Weierstrass curves

At a finite point of a nonsingular complex Weierstrass equation, at least one
of the two equation derivatives is nonzero.  This file computes the complex
Fréchet derivative of the affine equation and applies the complex implicit
function theorem in either coordinate.  The resulting implicit functions are
complex analytic at the base point, parametrize the equation in a
neighbourhood, and are locally unique.

These declarations are the analytic core of finite curve charts.  They do not
yet bundle the germs as `OpenPartialHomeomorph`s, choose compatible chart
sources, or install a `ChartedSpace` on the affine locus or compact point type.
In particular, no manifold structure is transported from a period lattice.
-/

open Filter
open scoped ContDiff Topology

noncomputable section

namespace Heights

/-- The affine Weierstrass polynomial, viewed as a complex-valued function on
`ℂ × ℂ`. -/
def complexWeierstrassEquation (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 -
    (p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)

/-- The partial derivative of the affine equation with respect to `x`. -/
def complexWeierstrassEquationX (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  W.a₁ * p.2 - (3 * p.1 ^ 2 + 2 * W.a₂ * p.1 + W.a₄)

/-- The partial derivative of the affine equation with respect to `y`. -/
def complexWeierstrassEquationY (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  2 * p.2 + W.a₁ * p.1 + W.a₃

@[simp] theorem complexWeierstrassEquation_eq_zero_iff
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquation W p = 0 ↔
      W.toAffine.Equation p.1 p.2 := by
  rw [WeierstrassCurve.Affine.equation_iff']
  rfl

@[simp] theorem complexWeierstrassEquationX_eq_polynomialX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquationX W p =
      W.toAffine.polynomialX.evalEval p.1 p.2 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialX]
  rfl

@[simp] theorem complexWeierstrassEquationY_eq_polynomialY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquationY W p =
      W.toAffine.polynomialY.evalEval p.1 p.2 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  rfl

/-- The affine equation is an entire function on `ℂ × ℂ`. -/
theorem contDiff_complexWeierstrassEquation (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassEquation W) := by
  unfold complexWeierstrassEquation
  fun_prop

/-- The exact complex Fréchet derivative of the affine equation. -/
theorem hasFDerivAt_complexWeierstrassEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassEquation W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p)) p := by
  have hx : HasFDerivAt (fun q : ℂ × ℂ => q.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℂ × ℂ => q.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
  have hyy := hy.pow 2
  have ha1xy := ((hasFDerivAt_const W.a₁ p).mul hx).mul hy
  have ha3y := (hasFDerivAt_const W.a₃ p).mul hy
  have hxxx := hx.pow 3
  have ha2xx := (hasFDerivAt_const W.a₂ p).mul (hx.pow 2)
  have ha4x := (hasFDerivAt_const W.a₄ p).mul hx
  have ha6 : HasFDerivAt (fun _ : ℂ × ℂ => W.a₆)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) p := hasFDerivAt_const W.a₆ p
  have h := ((hyy.add ha1xy).add ha3y).sub
      (((hxxx.add ha2xx).add ha4x).add ha6)
  change HasFDerivAt (complexWeierstrassEquation W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassEquation W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨z, w⟩
    simp [complexWeierstrassEquationX, complexWeierstrassEquationY]
    ring
  rwa [hfd] at hd

private theorem isInvertible_smulRight_id (a : ℂ) (ha : a ≠ 0) :
    ((ContinuousLinearMap.id ℂ ℂ).smulRight a).IsInvertible := by
  let u : ℂˣ := Units.mk0 a ha
  refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℂ) u, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  simp [u, mul_comm]

/-- If the `y`-derivative is nonzero, the partial Fréchet derivative in the
second factor is invertible. -/
theorem isInvertible_fderiv_inr_complexWeierstrassEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    (fderiv ℂ (complexWeierstrassEquation W) p ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassEquation W p).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationX W p) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationY W p)) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p) := by
    apply ContinuousLinearMap.ext
    intro z
    simp
  rw [heq]
  exact isInvertible_smulRight_id _ hy

/-- The implicit holomorphic `y`-coordinate near a point where `∂F/∂y ≠ 0`. -/
def complexWeierstrassImplicitY (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) : ℂ → ℂ :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

@[simp] theorem complexWeierstrassImplicitY_apply_self
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    complexWeierstrassImplicitY W p hy p.1 = p.2 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.implicitFunction_apply_self
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- Near its base point, the implicit `y`-function parametrizes the same level
set of the Weierstrass equation. -/
theorem eventually_complexWeierstrassEquation_iff_implicitY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ∀ᶠ q in 𝓝 p,
      complexWeierstrassEquation W q = complexWeierstrassEquation W p ↔
        complexWeierstrassImplicitY W p hy q.1 = q.2 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.eventually_apply_eq_iff_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- If the base point lies on the curve, the graph of the implicit `y`-function
lies on the curve near the base coordinate. -/
theorem eventually_complexWeierstrassImplicitY_equation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ∀ᶠ x in 𝓝 p.1,
      W.toAffine.Equation x (complexWeierstrassImplicitY W p hy x) := by
  have h :=
    (contDiff_complexWeierstrassEquation W).contDiffAt.eventually_apply_implicitFunction
      (u := p) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)
  have hp0 : complexWeierstrassEquation W p = 0 :=
    (complexWeierstrassEquation_eq_zero_iff W p).2 hp
  filter_upwards [h] with x hx
  apply (complexWeierstrassEquation_eq_zero_iff W
    (x, complexWeierstrassImplicitY W p hy x)).1
  simpa [hp0, complexWeierstrassImplicitY] using hx

/-- The implicit `y`-coordinate is complex analytic at its base coordinate. -/
theorem contDiffAt_complexWeierstrassImplicitY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ContDiffAt ℂ ω (complexWeierstrassImplicitY W p hy) p.1 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.contDiffAt_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- The affine equation with coordinates exchanged.  Its second variable is
`x`, so the ordinary product-domain implicit theorem solves for `x`. -/
def complexWeierstrassEquationSwap (W : WeierstrassCurve ℂ)
    (p : ℂ × ℂ) : ℂ :=
  complexWeierstrassEquation W (p.2, p.1)

/-- The swapped equation is entire. -/
theorem contDiff_complexWeierstrassEquationSwap (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassEquationSwap W) := by
  unfold complexWeierstrassEquationSwap
  exact (contDiff_complexWeierstrassEquation W).comp (by fun_prop)

/-- The exact derivative of the equation after exchanging coordinates. -/
theorem hasFDerivAt_complexWeierstrassEquationSwap
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassEquationSwap W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W (p.2, p.1)) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1))) p := by
  have hs : HasFDerivAt (fun q : ℂ × ℂ => (q.2, q.1))
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod
        (ContinuousLinearMap.fst ℂ ℂ ℂ)) p :=
    hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have h := (hasFDerivAt_complexWeierstrassEquation W (p.2, p.1)).comp p hs
  change HasFDerivAt (complexWeierstrassEquationSwap W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassEquationSwap W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W (p.2, p.1)) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1)) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨z, w⟩
    simp
    ring
  rwa [hfd] at hd

/-- If the `x`-derivative is nonzero, the second-factor derivative of the
swapped equation is invertible. -/
theorem isInvertible_fderiv_inr_complexWeierstrassEquationSwap
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W (p.2, p.1) ≠ 0) :
    (fderiv ℂ (complexWeierstrassEquationSwap W) p ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassEquationSwap W p).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationY W (p.2, p.1)) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationX W (p.2, p.1))) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp
  rw [heq]
  exact isInvertible_smulRight_id _ hx

/-- The implicit holomorphic `x`-coordinate near a point where `∂F/∂x ≠ 0`.
Its argument is the `y`-coordinate. -/
def complexWeierstrassImplicitX (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) : ℂ → ℂ :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

@[simp] theorem complexWeierstrassImplicitX_apply_self
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    complexWeierstrassImplicitX W p hx p.2 = p.1 :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.implicitFunction_apply_self
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

/-- Near its base point, the implicit `x`-function parametrizes the same level
set of the Weierstrass equation. -/
theorem eventually_complexWeierstrassEquation_iff_implicitX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ∀ᶠ q in 𝓝 p,
      complexWeierstrassEquation W q = complexWeierstrassEquation W p ↔
        complexWeierstrassImplicitX W p hx q.2 = q.1 := by
  have h :=
    (contDiff_complexWeierstrassEquationSwap W).contDiffAt.eventually_apply_eq_iff_implicitFunction
      (u := (p.2, p.1)) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W (p.2, p.1) hx)
  have hswap : Tendsto (fun q : ℂ × ℂ => (q.2, q.1)) (𝓝 p) (𝓝 (p.2, p.1)) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  filter_upwards [h.filter_mono hswap] with q hq
  simpa [complexWeierstrassEquationSwap, complexWeierstrassImplicitX] using hq

/-- If the base point lies on the curve, the graph of the implicit `x`-function
lies on the curve near the base coordinate. -/
theorem eventually_complexWeierstrassImplicitX_equation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hp : W.toAffine.Equation p.1 p.2)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ∀ᶠ y in 𝓝 p.2,
      W.toAffine.Equation (complexWeierstrassImplicitX W p hx y) y := by
  have h :=
    (contDiff_complexWeierstrassEquationSwap W).contDiffAt.eventually_apply_implicitFunction
      (u := (p.2, p.1)) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W (p.2, p.1) hx)
  have hp0 : complexWeierstrassEquationSwap W (p.2, p.1) = 0 := by
    apply (complexWeierstrassEquation_eq_zero_iff W p).2 hp
  filter_upwards [h] with y hy
  apply (complexWeierstrassEquation_eq_zero_iff W
    (complexWeierstrassImplicitX W p hx y, y)).1
  change complexWeierstrassEquationSwap W
    (y, complexWeierstrassImplicitX W p hx y) = 0
  exact hy.trans hp0

/-- The implicit `x`-coordinate is complex analytic at its base coordinate. -/
theorem contDiffAt_complexWeierstrassImplicitX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ContDiffAt ℂ ω (complexWeierstrassImplicitX W p hx) p.2 :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.contDiffAt_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

/-- At every finite point of a nonsingular complex Weierstrass equation, one
of the two analytic implicit-coordinate constructions applies. -/
theorem complexWeierstrassAffine_derivative_ne_zero
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    complexWeierstrassEquationX W P.1 ≠ 0 ∨
      complexWeierstrassEquationY W P.1 ≠ 0 := by
  have hns : W.toAffine.Nonsingular P.1.1 P.1.2 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp P.2
  simpa [complexWeierstrassEquationX_eq_polynomialX,
    complexWeierstrassEquationY_eq_polynomialY] using hns.2

/-- Every finite curve point admits an honest complex-analytic graph germ in
one of the two coordinate directions.  This packages the output needed to
construct the eventual finite chart, without pretending that an atlas has
already been assembled. -/
theorem complexWeierstrassAffine_exists_analytic_graph_germ
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (P : ComplexWeierstrassAffine W) :
    (∃ hy : complexWeierstrassEquationY W P.1 ≠ 0,
        ContDiffAt ℂ ω (complexWeierstrassImplicitY W P.1 hy) P.1.1 ∧
        complexWeierstrassImplicitY W P.1 hy P.1.1 = P.1.2 ∧
        ∀ᶠ x in 𝓝 P.1.1,
          W.toAffine.Equation x
            (complexWeierstrassImplicitY W P.1 hy x)) ∨
      (∃ hx : complexWeierstrassEquationX W P.1 ≠ 0,
        ContDiffAt ℂ ω (complexWeierstrassImplicitX W P.1 hx) P.1.2 ∧
        complexWeierstrassImplicitX W P.1 hx P.1.2 = P.1.1 ∧
        ∀ᶠ y in 𝓝 P.1.2,
          W.toAffine.Equation
            (complexWeierstrassImplicitX W P.1 hx y) y) := by
  rcases complexWeierstrassAffine_derivative_ne_zero W P with hx | hy
  · exact Or.inr ⟨hx, contDiffAt_complexWeierstrassImplicitX W P.1 hx,
      complexWeierstrassImplicitX_apply_self W P.1 hx,
      eventually_complexWeierstrassImplicitX_equation W P.1 P.2 hx⟩
  · exact Or.inl ⟨hy, contDiffAt_complexWeierstrassImplicitY W P.1 hy,
      complexWeierstrassImplicitY_apply_self W P.1 hy,
      eventually_complexWeierstrassImplicitY_equation W P.1 P.2 hy⟩

end Heights
