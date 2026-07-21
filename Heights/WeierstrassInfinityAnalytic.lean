import Heights.WeierstrassFiniteManifold
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.MetricSpace.Bounded

set_option linter.style.header false

/-!
# The projective analytic germ at Weierstrass infinity

In the projective chart where the homogeneous `Y`-coordinate is nonzero, put
`u = X / Y` and `v = Z / Y`.  The point at infinity is `(u,v) = (0,0)`, and
the homogenized Weierstrass equation becomes

`v + a₁uv + a₃v² = u³ + a₂u²v + a₄uv² + a₆v³`.

Its `v`-derivative at the origin is one.  This file constructs the resulting
implicit holomorphic branch `v = v(u)` and identifies its punctured part with
the ordinary affine equation by `(x,y) = (u/v,1/v)`.  The identification is a
homeomorphism for the independently defined subtype topologies and is
biholomorphic in ambient coordinates.

The branch is then identified with the open one-point-compactification
neighborhood obtained by deleting the compact affine locus `y = 0`.  The
reverse continuity at infinity is proved by an explicit properness estimate
for the cubic equation.  Thus this file supplies the honest infinity chart
needed to assemble the compact curve atlas; that assembly is kept separate.
-/

open Filter
open scoped ContDiff OnePoint Topology

noncomputable section

namespace Heights

/-- The homogenized Weierstrass equation in the projective `Y ≠ 0` chart. -/
def complexWeierstrassInfinityEquation (W : WeierstrassCurve ℂ)
    (p : ℂ × ℂ) : ℂ :=
  p.2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 ^ 2 -
    (p.1 ^ 3 + W.a₂ * p.1 ^ 2 * p.2 + W.a₄ * p.1 * p.2 ^ 2 +
      W.a₆ * p.2 ^ 3)

/-- The `u`-partial derivative of the projective-chart equation. -/
def complexWeierstrassInfinityEquationU (W : WeierstrassCurve ℂ)
    (p : ℂ × ℂ) : ℂ :=
  W.a₁ * p.2 -
    (3 * p.1 ^ 2 + 2 * W.a₂ * p.1 * p.2 + W.a₄ * p.2 ^ 2)

/-- The `v`-partial derivative of the projective-chart equation. -/
def complexWeierstrassInfinityEquationV (W : WeierstrassCurve ℂ)
    (p : ℂ × ℂ) : ℂ :=
  1 + W.a₁ * p.1 + 2 * W.a₃ * p.2 -
    (W.a₂ * p.1 ^ 2 + 2 * W.a₄ * p.1 * p.2 + 3 * W.a₆ * p.2 ^ 2)

@[simp] theorem complexWeierstrassInfinityEquation_zero
    (W : WeierstrassCurve ℂ) :
    complexWeierstrassInfinityEquation W (0, 0) = 0 := by
  simp [complexWeierstrassInfinityEquation]

@[simp] theorem complexWeierstrassInfinityEquationV_zero
    (W : WeierstrassCurve ℂ) :
    complexWeierstrassInfinityEquationV W (0, 0) = 1 := by
  simp [complexWeierstrassInfinityEquationV]

/-- The projective-chart equation is entire. -/
theorem contDiff_complexWeierstrassInfinityEquation
    (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassInfinityEquation W) := by
  unfold complexWeierstrassInfinityEquation
  fun_prop

/-- The exact complex Fréchet derivative of the projective-chart equation. -/
theorem hasFDerivAt_complexWeierstrassInfinityEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassInfinityEquation W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassInfinityEquationU W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassInfinityEquationV W p)) p := by
  have hu : HasFDerivAt (fun q : ℂ × ℂ => q.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
  have hv : HasFDerivAt (fun q : ℂ × ℂ => q.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
  have ha1uv := ((hasFDerivAt_const W.a₁ p).mul hu).mul hv
  have ha3vv := (hasFDerivAt_const W.a₃ p).mul (hv.pow 2)
  have huuu := hu.pow 3
  have ha2uuv := ((hasFDerivAt_const W.a₂ p).mul (hu.pow 2)).mul hv
  have ha4uvv := ((hasFDerivAt_const W.a₄ p).mul hu).mul (hv.pow 2)
  have ha6vvv := (hasFDerivAt_const W.a₆ p).mul (hv.pow 3)
  have h := ((hv.add ha1uv).add ha3vv).sub
    (((huuu.add ha2uuv).add ha4uvv).add ha6vvv)
  change HasFDerivAt (complexWeierstrassInfinityEquation W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassInfinityEquation W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassInfinityEquationU W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassInfinityEquationV W p) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    simp [complexWeierstrassInfinityEquationU,
      complexWeierstrassInfinityEquationV]
    ring
  rwa [hfd] at hd

private theorem isInvertible_smulRight_one :
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (1 : ℂ)).IsInvertible := by
  let u : ℂˣ := 1
  refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℂ) u, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  simp [u]

/-- The partial Fréchet derivative in the `v` direction is invertible at
projective infinity. -/
theorem isInvertible_fderiv_inr_complexWeierstrassInfinityEquation
    (W : WeierstrassCurve ℂ) :
    (fderiv ℂ (complexWeierstrassInfinityEquation W) (0, 0) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassInfinityEquation W (0, 0)).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassInfinityEquationU W (0, 0)) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassInfinityEquationV W (0, 0))) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight (1 : ℂ) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [complexWeierstrassInfinityEquationU]
  rw [heq]
  exact isInvertible_smulRight_one

/-- The holomorphic projective `v`-coordinate as a function of the local
parameter `u`, furnished by the complex implicit-function theorem. -/
def complexWeierstrassInfinityImplicitV (W : WeierstrassCurve ℂ) : ℂ → ℂ :=
  (contDiff_complexWeierstrassInfinityEquation W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassInfinityEquation W)

@[simp] theorem complexWeierstrassInfinityImplicitV_zero
    (W : WeierstrassCurve ℂ) :
    complexWeierstrassInfinityImplicitV W 0 = 0 :=
  (contDiff_complexWeierstrassInfinityEquation W).contDiffAt.implicitFunction_apply_self
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassInfinityEquation W)

/-- The implicit projective coordinate is holomorphic at infinity. -/
theorem contDiffAt_complexWeierstrassInfinityImplicitV
    (W : WeierstrassCurve ℂ) :
    ContDiffAt ℂ ω (complexWeierstrassInfinityImplicitV W) 0 :=
  (contDiff_complexWeierstrassInfinityEquation W).contDiffAt.contDiffAt_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassInfinityEquation W)

/-- Near zero, the graph of the implicit function lies on the homogenized
Weierstrass equation. -/
theorem eventually_complexWeierstrassInfinityImplicitV_equation
    (W : WeierstrassCurve ℂ) :
    ∀ᶠ u in 𝓝 0,
      complexWeierstrassInfinityEquation W
        (u, complexWeierstrassInfinityImplicitV W u) = 0 := by
  have h :=
    (contDiff_complexWeierstrassInfinityEquation W).contDiffAt.eventually_apply_implicitFunction
      (u := ((0, 0) : ℂ × ℂ)) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassInfinityEquation W)
  simpa [complexWeierstrassInfinityImplicitV] using h

/-- The equation-defined projective branch through infinity. -/
abbrev ComplexWeierstrassInfinityBranch (W : WeierstrassCurve ℂ) :=
  {uv : ℂ × ℂ // complexWeierstrassInfinityEquation W uv = 0}

/-- The point `(u,v)=(0,0)` on the projective branch. -/
def complexWeierstrassInfinityBranchOrigin (W : WeierstrassCurve ℂ) :
    ComplexWeierstrassInfinityBranch W :=
  ⟨(0, 0), complexWeierstrassInfinityEquation_zero W⟩

/-- The inverse-function-theorem neighborhood in ambient `ℂ × ℂ`.  Its
forward map is `(u,v) ↦ (G(u,v),u)`.  Restriction to the zero fiber below
produces the projective infinity chart. -/
def complexWeierstrassInfinityAmbientHomeomorph
    (W : WeierstrassCurve ℂ) : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  let e :=
    (((contDiff_complexWeierstrassInfinityEquation W).contDiffAt.hasStrictFDerivAt
      (by simp)).implicitFunctionDataOfProdDomain
        (isInvertible_fderiv_inr_complexWeierstrassInfinityEquation W)).toOpenPartialHomeomorph
  e.restrOpen {q | complexWeierstrassInfinityEquationV W q ≠ 0} (by
    apply isOpen_ne.preimage
    unfold complexWeierstrassInfinityEquationV
    fun_prop)

@[simp] theorem complexWeierstrassInfinityAmbientHomeomorph_apply
    (W : WeierstrassCurve ℂ) (q : ℂ × ℂ) :
    complexWeierstrassInfinityAmbientHomeomorph W q =
      (complexWeierstrassInfinityEquation W q, q.1) :=
  rfl

theorem complexWeierstrassInfinityAmbientHomeomorph_origin_mem_source
    (W : WeierstrassCurve ℂ) :
    (0, 0) ∈ (complexWeierstrassInfinityAmbientHomeomorph W).source := by
  rw [complexWeierstrassInfinityAmbientHomeomorph,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _, by simp⟩

/-- The inverse ambient map is holomorphic at every point of the restricted
target. -/
theorem contDiffAt_complexWeierstrassInfinityAmbientHomeomorph_symm
    (W : WeierstrassCurve ℂ) (z : ℂ × ℂ)
    (hz : z ∈ (complexWeierstrassInfinityAmbientHomeomorph W).target) :
    ContDiffAt ℂ ω (complexWeierstrassInfinityAmbientHomeomorph W).symm z := by
  let e := complexWeierstrassInfinityAmbientHomeomorph W
  let q := e.symm z
  have hqsource : q ∈ e.source := e.map_target hz
  have hqv : complexWeierstrassInfinityEquationV W q ≠ 0 := hqsource.2
  have hinv :
      (fderiv ℂ (complexWeierstrassInfinityEquation W) q ∘L
        ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [(hasFDerivAt_complexWeierstrassInfinityEquation W q).fderiv]
    have heq :
        (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
              (complexWeierstrassInfinityEquationU W q) +
          (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
              (complexWeierstrassInfinityEquationV W q)) ∘L
            ContinuousLinearMap.inr ℂ ℂ ℂ) =
          (ContinuousLinearMap.id ℂ ℂ).smulRight
            (complexWeierstrassInfinityEquationV W q) := by
      apply ContinuousLinearMap.ext
      intro w
      simp
    rw [heq]
    let a : ℂˣ := Units.mk0 _ hqv
    refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℂ) a, ?_⟩
    apply ContinuousLinearMap.ext
    intro w
    simp [a]
  let φ :=
    ((contDiff_complexWeierstrassInfinityEquation W).contDiffAt.hasStrictFDerivAt
      (by simp)).implicitFunctionDataOfProdDomain hinv
  apply e.contDiffAt_symm hz
  · change HasFDerivAt
      (fun q : ℂ × ℂ => (complexWeierstrassInfinityEquation W q, q.1)) _ q
    have hφ := φ.hasStrictFDerivAt.hasFDerivAt
    change HasFDerivAt
      (fun q : ℂ × ℂ => (complexWeierstrassInfinityEquation W q, q.1)) _ q at hφ
    exact hφ
  · exact (contDiff_complexWeierstrassInfinityEquation W).contDiffAt.prodMk
      contDiffAt_fst

private def complexWeierstrassInfinityChartInv
    (W : WeierstrassCurve ℂ) (u : ℂ) :
    ComplexWeierstrassInfinityBranch W := by
  classical
  let e := complexWeierstrassInfinityAmbientHomeomorph W
  exact if hu : (0, u) ∈ e.target then
    ⟨e.symm (0, u), by
      have hright := e.right_inv hu
      exact congrArg Prod.fst hright⟩
  else complexWeierstrassInfinityBranchOrigin W

private theorem complexWeierstrassInfinityChartInv_coe_of_mem
    (W : WeierstrassCurve ℂ) (u : ℂ)
    (hu : (0, u) ∈
      (complexWeierstrassInfinityAmbientHomeomorph W).target) :
    (complexWeierstrassInfinityChartInv W u : ℂ × ℂ) =
      (complexWeierstrassInfinityAmbientHomeomorph W).symm (0, u) := by
  classical
  simp [complexWeierstrassInfinityChartInv, hu]

/-- The zero-fiber restriction of the ambient inverse-function neighborhood.
This is an open partial homeomorphism from the projective equation branch to
`ℂ`, with forward coordinate `u = X/Y`. -/
def complexWeierstrassInfinityBranchChart (W : WeierstrassCurve ℂ) :
    OpenPartialHomeomorph (ComplexWeierstrassInfinityBranch W) ℂ := by
  let e := complexWeierstrassInfinityAmbientHomeomorph W
  let inv := complexWeierstrassInfinityChartInv W
  refine
    { toFun := fun Q => Q.1.1
      invFun := inv
      source := {Q | Q.1 ∈ e.source}
      target := {u | (0, u) ∈ e.target}
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
      continuousOn_toFun := continuous_subtype_val.fst.continuousOn
      continuousOn_invFun := ?_ }
  · intro Q hQ
    have hm := e.map_source hQ
    simpa [e, Q.2] using hm
  · intro u hu
    change (inv u).1 ∈ e.source
    rw [complexWeierstrassInfinityChartInv_coe_of_mem W u hu]
    exact e.map_target hu
  · intro Q hQ
    apply Subtype.ext
    change (inv Q.1.1).1 = Q.1
    have ht : (0, Q.1.1) ∈ e.target := by
      have hm := e.map_source hQ
      simpa [e, Q.2] using hm
    rw [complexWeierstrassInfinityChartInv_coe_of_mem W _ ht]
    simpa [e, Q.2] using e.left_inv hQ
  · intro u hu
    rw [complexWeierstrassInfinityChartInv_coe_of_mem W u hu]
    exact congrArg Prod.snd (e.right_inv hu)
  · rw [continuousOn_iff_continuous_restrict]
    let inc : {u : ℂ | (0, u) ∈ e.target} → ℂ × ℂ := fun u => (0, u.1)
    have hinc : Continuous inc := continuous_const.prodMk continuous_subtype_val
    have hamb : Continuous (fun u => e.symm (inc u)) :=
      e.continuousOn_symm.comp_continuous hinc (fun u => u.2)
    let g : {u : ℂ | (0, u) ∈ e.target} →
        ComplexWeierstrassInfinityBranch W := fun u =>
      ⟨e.symm (inc u), by
        exact congrArg Prod.fst (e.right_inv u.2)⟩
    have hg : Continuous g := Continuous.subtype_mk hamb _
    have heq : {u : ℂ | (0, u) ∈ e.target}.restrict inv = g := by
      funext u
      apply Subtype.ext
      exact complexWeierstrassInfinityChartInv_coe_of_mem W u.1 u.2
    rw [heq]
    exact hg

@[simp] theorem complexWeierstrassInfinityBranchChart_apply
    (W : WeierstrassCurve ℂ) (Q : ComplexWeierstrassInfinityBranch W) :
    complexWeierstrassInfinityBranchChart W Q = Q.1.1 :=
  rfl

theorem complexWeierstrassInfinityBranchOrigin_mem_chart_source
    (W : WeierstrassCurve ℂ) :
    complexWeierstrassInfinityBranchOrigin W ∈
      (complexWeierstrassInfinityBranchChart W).source :=
  complexWeierstrassInfinityAmbientHomeomorph_origin_mem_source W

/-- On the chart target, the inverse branch is the graph of the implicit
holomorphic function constructed at the origin. -/
theorem complexWeierstrassInfinityBranchChart_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) (u : ℂ)
    (hu : u ∈ (complexWeierstrassInfinityBranchChart W).target) :
    ((complexWeierstrassInfinityBranchChart W).symm u : ℂ × ℂ) =
      (u, complexWeierstrassInfinityImplicitV W u) := by
  let e := complexWeierstrassInfinityAmbientHomeomorph W
  change (complexWeierstrassInfinityChartInv W u : ℂ × ℂ) = _
  rw [complexWeierstrassInfinityChartInv_coe_of_mem W u hu]
  apply Prod.ext_iff.mpr
  constructor
  · exact congrArg Prod.snd (e.right_inv hu)
  · change (e.symm (0, u)).2 =
      (e.symm (complexWeierstrassInfinityEquation W (0, 0), u)).2
    simp

/-- Every inverse chart branch is holomorphic in ambient projective
coordinates. -/
theorem contDiffAt_complexWeierstrassInfinityBranchChart_symm_coe_of_mem
    (W : WeierstrassCurve ℂ) (u : ℂ)
    (hu : u ∈ (complexWeierstrassInfinityBranchChart W).target) :
    ContDiffAt ℂ ω (fun u =>
      ((complexWeierstrassInfinityBranchChart W).symm u : ℂ × ℂ)) u := by
  let e := complexWeierstrassInfinityAmbientHomeomorph W
  have hamb : ContDiffAt ℂ ω e.symm (0, u) :=
    contDiffAt_complexWeierstrassInfinityAmbientHomeomorph_symm W _ hu
  have hcomp : ContDiffAt ℂ ω (fun u => e.symm (0, u)) u :=
    hamb.comp u (contDiffAt_const.prodMk contDiffAt_id)
  have ht := (complexWeierstrassInfinityBranchChart W).open_target.mem_nhds hu
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [ht] with w hw
  simpa [complexWeierstrassInfinityBranchChart, e] using
    (complexWeierstrassInfinityChartInv_coe_of_mem W w hw)

/-- The origin is the only point of the projective branch with `v = 0`.
Thus deleting the point at infinity is exactly the locus on which the affine
overlap formulas are defined. -/
theorem complexWeierstrassInfinityBranch_snd_eq_zero_iff
    (W : WeierstrassCurve ℂ) (Q : ComplexWeierstrassInfinityBranch W) :
    Q.1.2 = 0 ↔ Q = complexWeierstrassInfinityBranchOrigin W := by
  constructor
  · intro hv
    apply Subtype.ext
    apply Prod.ext
    · have h := Q.2
      have hu3 : Q.1.1 ^ 3 = 0 := by
        simpa [complexWeierstrassInfinityEquation, hv] using h
      exact eq_zero_of_pow_eq_zero hu3
    · exact hv
  · rintro rfl
    rfl

/-- A nonzero local parameter has nonzero projective `v`-coordinate on the
inverse infinity chart. -/
theorem complexWeierstrassInfinityBranchChart_symm_snd_ne_zero
    (W : WeierstrassCurve ℂ) (u : ℂ)
    (hu : u ∈ (complexWeierstrassInfinityBranchChart W).target)
    (hu0 : u ≠ 0) :
    (((complexWeierstrassInfinityBranchChart W).symm u :
      ComplexWeierstrassInfinityBranch W) : ℂ × ℂ).2 ≠ 0 := by
  intro hv
  have hQ := (complexWeierstrassInfinityBranch_snd_eq_zero_iff W _).1 hv
  have hfirst := congrArg
    (fun Q : ComplexWeierstrassInfinityBranch W => Q.1.1) hQ
  have hright := (complexWeierstrassInfinityBranchChart W).right_inv hu
  apply hu0
  simpa [complexWeierstrassInfinityBranchOrigin] using
    hright.symm.trans hfirst

/-- The punctured projective branch, where passage to affine coordinates is
valid. -/
abbrev ComplexWeierstrassInfinityBranchPunctured (W : WeierstrassCurve ℂ) :=
  {uv : ComplexWeierstrassInfinityBranch W // uv.1.2 ≠ 0}

/-- The part of the affine curve on which the projective `Y ≠ 0` coordinates
are defined. -/
abbrev ComplexWeierstrassAffineYNeZero (W : WeierstrassCurve ℂ) :=
  {P : ComplexWeierstrassAffine W // P.1.2 ≠ 0}

private theorem infinityEquation_of_affine (W : WeierstrassCurve ℂ)
    (x y : ℂ) (h : W.toAffine.Equation x y) (hy : y ≠ 0) :
    complexWeierstrassInfinityEquation W (x / y, 1 / y) = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff'] at h
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 at h
  simp only [complexWeierstrassInfinityEquation]
  field_simp [hy]
  linear_combination h

private theorem affineEquation_of_infinity (W : WeierstrassCurve ℂ)
    (u v : ℂ) (h : complexWeierstrassInfinityEquation W (u, v) = 0)
    (hv : v ≠ 0) :
    W.toAffine.Equation (u / v) (1 / v) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change (1 / v) ^ 2 + W.a₁ * (u / v) * (1 / v) + W.a₃ * (1 / v) -
      ((u / v) ^ 3 + W.a₂ * (u / v) ^ 2 + W.a₄ * (u / v) + W.a₆) = 0
  simp only [complexWeierstrassInfinityEquation] at h
  field_simp [hv]
  linear_combination h

/-- On the punctured projective branch, `(u,v) ↦ (u/v,1/v)` is a
homeomorphism to the `y ≠ 0` part of the affine curve. -/
noncomputable def complexWeierstrassInfinityPuncturedHomeomorph
    (W : WeierstrassCurve ℂ) :
    ComplexWeierstrassInfinityBranchPunctured W ≃ₜ
      ComplexWeierstrassAffineYNeZero W where
  toFun uv :=
    ⟨⟨(uv.1.1.1 / uv.1.1.2, 1 / uv.1.1.2),
      affineEquation_of_infinity W _ _ uv.1.2 uv.2⟩, by
        exact one_div_ne_zero uv.2⟩
  invFun P :=
    ⟨⟨(P.1.1.1 / P.1.1.2, 1 / P.1.1.2),
      infinityEquation_of_affine W _ _ P.1.2 P.2⟩, by
        exact one_div_ne_zero P.2⟩
  left_inv uv := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> simp [uv.2]
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> simp [P.2]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have h : Continuous (fun uv : ComplexWeierstrassInfinityBranchPunctured W =>
        ((uv.1.1 : ℂ × ℂ))) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.fst.div₀ h.snd (fun uv => uv.2)).prodMk
      (continuous_const.div₀ h.snd (fun uv => uv.2))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have h : Continuous (fun P : ComplexWeierstrassAffineYNeZero W =>
        ((P.1.1 : ℂ × ℂ))) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.fst.div₀ h.snd (fun P => P.2)).prodMk
      (continuous_const.div₀ h.snd (fun P => P.2))

/-- The projective branch maps to the one-point compactification of the
affine curve: its origin goes to infinity and its punctured part uses the
rational overlap homeomorphism. -/
noncomputable def complexWeierstrassInfinityBranchToOnePoint
    (W : WeierstrassCurve ℂ) (Q : ComplexWeierstrassInfinityBranch W) :
    OnePoint (ComplexWeierstrassAffine W) := by
  classical
  exact if hv : Q.1.2 = 0 then ∞ else
    ((complexWeierstrassInfinityPuncturedHomeomorph W ⟨Q, hv⟩).1 :
      ComplexWeierstrassAffine W)

@[simp] theorem complexWeierstrassInfinityBranchToOnePoint_origin
    (W : WeierstrassCurve ℂ) :
    complexWeierstrassInfinityBranchToOnePoint W
      (complexWeierstrassInfinityBranchOrigin W) =
        (∞ : OnePoint (ComplexWeierstrassAffine W)) := by
  simp [complexWeierstrassInfinityBranchToOnePoint,
    complexWeierstrassInfinityBranchOrigin]

/-- The projective-to-one-point map is continuous at the branch origin.
Compact subsets of the affine curve have bounded `y`-coordinate, whereas
`y=1/v` diverges as the projective coordinate `v` tends to zero. -/
theorem continuousAt_complexWeierstrassInfinityBranchToOnePoint_origin
    (W : WeierstrassCurve ℂ) :
    ContinuousAt (complexWeierstrassInfinityBranchToOnePoint W)
      (complexWeierstrassInfinityBranchOrigin W) := by
  rw [ContinuousAt]
  rw [complexWeierstrassInfinityBranchToOnePoint_origin]
  rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
  intro K hK
  rcases hK with ⟨hKclosed, hKcompact⟩
  have hycont : Continuous
      (fun P : ComplexWeierstrassAffine W => P.1.2) :=
    continuous_subtype_val.snd
  have hycompact : IsCompact
      ((fun P : ComplexWeierstrassAffine W => P.1.2) '' K) :=
    hKcompact.image hycont
  rcases (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1
      hycompact.isBounded with ⟨r, hr⟩
  let R : ℝ := max r 0 + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [le_max_right r 0]
  have hc : ContinuousAt
      (fun Q : ComplexWeierstrassInfinityBranch W => Q.1.2)
      (complexWeierstrassInfinityBranchOrigin W) :=
    continuous_subtype_val.snd.continuousAt
  have hvlim : Tendsto
      (fun Q : ComplexWeierstrassInfinityBranch W => Q.1.2)
      (𝓝 (complexWeierstrassInfinityBranchOrigin W)) (𝓝 0) := by
    change Tendsto (fun Q : ComplexWeierstrassInfinityBranch W => Q.1.2)
      (𝓝 (complexWeierstrassInfinityBranchOrigin W))
      (𝓝 ((complexWeierstrassInfinityBranchOrigin W).1.2)) at hc
    simpa [complexWeierstrassInfinityBranchOrigin] using hc
  have hball : Metric.ball (0 : ℂ) R⁻¹ ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (inv_pos.mpr hR)
  filter_upwards [hvlim hball] with Q hQ
  by_cases hv : Q.1.2 = 0
  · right
    simp [complexWeierstrassInfinityBranchToOnePoint, hv]
  · left
    let P : ComplexWeierstrassAffine W :=
      (complexWeierstrassInfinityPuncturedHomeomorph W ⟨Q, hv⟩).1
    refine ⟨P, ?_, ?_⟩
    · intro hPK
      have hy_mem : P.1.2 ∈
          (fun T : ComplexWeierstrassAffine W => T.1.2) '' K :=
        ⟨P, hPK, rfl⟩
      have hyr : ‖P.1.2‖ ≤ r := by
        have := hr hy_mem
        simpa [Metric.mem_closedBall, dist_zero_right] using this
      have hrR : r < R := by
        dsimp [R]
        linarith [le_max_left r 0]
      have hvpos : 0 < ‖Q.1.2‖ := norm_pos_iff.mpr hv
      have hvsmall : ‖Q.1.2‖ < R⁻¹ := by
        simpa [Metric.mem_ball, dist_zero_right] using hQ
      have hlarge : R < ‖Q.1.2‖⁻¹ :=
        (lt_inv_comm₀ hvpos hR).mp hvsmall
      have hyformula : ‖P.1.2‖ = ‖Q.1.2‖⁻¹ := by
        simp [P, complexWeierstrassInfinityPuncturedHomeomorph, norm_inv]
      rw [hyformula] at hyr
      linarith
    · simp [complexWeierstrassInfinityBranchToOnePoint, hv, P]

private def complexWeierstrassCurveNormBound (W : WeierstrassCurve ℂ) (B : ℝ) : ℝ :=
  max 1 (B ^ 2 + ‖W.a₁‖ * B + ‖W.a₃‖ * B + ‖W.a₂‖ + ‖W.a₄‖ + ‖W.a₆‖)

private theorem norm_fst_le_complexWeierstrassCurveNormBound (W : WeierstrassCurve ℂ)
    (x y : ℂ) (hEq : W.toAffine.Equation x y) (B : ℝ) (hB : 0 ≤ B)
    (hy : ‖y‖ ≤ B * max 1 ‖x‖) :
    ‖x‖ ≤ complexWeierstrassCurveNormBound W B := by
  rw [WeierstrassCurve.Affine.equation_iff'] at hEq
  let C : ℝ := B ^ 2 + ‖W.a₁‖ * B + ‖W.a₃‖ * B +
    ‖W.a₂‖ + ‖W.a₄‖ + ‖W.a₆‖
  by_cases hx : ‖x‖ ≤ 1
  · exact hx.trans (le_max_left _ _)
  · have hx1 : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hy' : ‖y‖ ≤ B * ‖x‖ := by simpa [max_eq_right hx1] using hy
    have hnorm : ‖x‖ ^ 3 ≤ ‖y‖ ^ 2 + ‖W.a₁‖ * ‖x‖ * ‖y‖ +
        ‖W.a₃‖ * ‖y‖ + ‖W.a₂‖ * ‖x‖ ^ 2 +
        ‖W.a₄‖ * ‖x‖ + ‖W.a₆‖ := by
      have heq : x ^ 3 = y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          W.a₂ * x ^ 2 - W.a₄ * x - W.a₆ := by
        linear_combination -hEq
      rw [← norm_pow, heq]
      calc
        ‖y ^ 2 + W.a₁ * x * y + W.a₃ * y - W.a₂ * x ^ 2 - W.a₄ * x - W.a₆‖
            ≤ ‖y ^ 2‖ + ‖W.a₁ * x * y‖ + ‖W.a₃ * y‖ +
                ‖W.a₂ * x ^ 2‖ + ‖W.a₄ * x‖ + ‖W.a₆‖ := by
              calc
                _ ≤ ‖y ^ 2 + W.a₁ * x * y + W.a₃ * y - W.a₂ * x ^ 2 - W.a₄ * x‖ + ‖W.a₆‖ := norm_sub_le _ _
                _ ≤ (‖y ^ 2 + W.a₁ * x * y + W.a₃ * y - W.a₂ * x ^ 2‖ + ‖W.a₄ * x‖) + ‖W.a₆‖ := by gcongr; exact norm_sub_le _ _
                _ ≤ ((‖y ^ 2 + W.a₁ * x * y + W.a₃ * y‖ + ‖W.a₂ * x ^ 2‖) + ‖W.a₄ * x‖) + ‖W.a₆‖ := by gcongr; exact norm_sub_le _ _
                _ ≤ (((‖y ^ 2 + W.a₁ * x * y‖ + ‖W.a₃ * y‖) + ‖W.a₂ * x ^ 2‖) + ‖W.a₄ * x‖) + ‖W.a₆‖ := by gcongr; exact norm_add_le _ _
                _ ≤ ((((‖y ^ 2‖ + ‖W.a₁ * x * y‖) + ‖W.a₃ * y‖) + ‖W.a₂ * x ^ 2‖) + ‖W.a₄ * x‖) + ‖W.a₆‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by simp only [norm_pow, norm_mul]
    have hx_sq : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    have hyy : ‖y‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := by
      simpa [mul_pow] using
        (sq_le_sq₀ (norm_nonneg y) (mul_nonneg hB hx0)).2 hy'
    have ha1 : ‖W.a₁‖ * ‖x‖ * ‖y‖ ≤
        (‖W.a₁‖ * B) * ‖x‖ ^ 2 := by
      calc
        _ ≤ ‖W.a₁‖ * ‖x‖ * (B * ‖x‖) :=
          mul_le_mul_of_nonneg_left hy' (mul_nonneg (norm_nonneg _) hx0)
        _ = _ := by ring
    have ha3 : ‖W.a₃‖ * ‖y‖ ≤
        (‖W.a₃‖ * B) * ‖x‖ ^ 2 := by
      calc
        _ ≤ ‖W.a₃‖ * (B * ‖x‖) :=
          mul_le_mul_of_nonneg_left hy' (norm_nonneg _)
        _ ≤ ‖W.a₃‖ * (B * ‖x‖ ^ 2) := by
          gcongr
        _ = _ := by ring
    have ha4 : ‖W.a₄‖ * ‖x‖ ≤ ‖W.a₄‖ * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hx_sq (norm_nonneg _)
    have ha6 : ‖W.a₆‖ ≤ ‖W.a₆‖ * ‖x‖ ^ 2 := by
      calc
        _ = ‖W.a₆‖ * 1 := by ring
        _ ≤ ‖W.a₆‖ * ‖x‖ := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hx_sq (norm_nonneg _)
    have hXC : ‖x‖ ^ 3 ≤ C * ‖x‖ ^ 2 := by
      dsimp [C]
      nlinarith
    have hleC : ‖x‖ ≤ C := by
      nlinarith [sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hx1)]
    exact hleC.trans (le_max_right _ _)

private theorem isCompact_complexWeierstrassInfinityControlSet (W : WeierstrassCurve ℂ)
    (δ : ℝ) (hδ : 0 < δ) :
    IsCompact {P : ComplexWeierstrassAffine W |
      δ * ‖P.1.2‖ ≤ 1 ∨ δ * ‖P.1.2‖ ≤ ‖P.1.1‖} := by
  let B : ℝ := δ⁻¹
  let R : ℝ := complexWeierstrassCurveNormBound W B
  let S : Set (ℂ × ℂ) := {p |
    W.toAffine.Equation p.1 p.2 ∧
      (δ * ‖p.2‖ ≤ 1 ∨ δ * ‖p.2‖ ≤ ‖p.1‖)}
  have hB : 0 ≤ B := (inv_nonneg.mpr hδ.le)
  have hSclosed : IsClosed S := by
    apply (isClosed_complexWeierstrassAffine W).inter
    exact (isClosed_le (continuous_const.mul continuous_snd.norm) continuous_const).union
      (isClosed_le (continuous_const.mul continuous_snd.norm) continuous_fst.norm)
  have hxR : ∀ p ∈ S, ‖p.1‖ ≤ R := by
    intro p hp
    apply norm_fst_le_complexWeierstrassCurveNormBound W p.1 p.2 hp.1 B hB
    rcases hp.2 with hv | hu
    · have hyB : ‖p.2‖ ≤ B := by
        simpa [B] using (le_inv_mul_iff₀ hδ).2 hv
      exact hyB.trans (le_mul_of_one_le_right hB (le_max_left _ _))
    · have hyBX : ‖p.2‖ ≤ B * ‖p.1‖ := by
        exact (le_inv_mul_iff₀ hδ).2 hu
      exact hyBX.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hB)
  have hyBound : ∀ p ∈ S, ‖p.2‖ ≤ B * max 1 R := by
    intro p hp
    rcases hp.2 with hv | hu
    · have hyB : ‖p.2‖ ≤ B :=
        by simpa [B] using (le_inv_mul_iff₀ hδ).2 hv
      exact hyB.trans (le_mul_of_one_le_right hB (le_max_left _ _))
    · have hyBX : ‖p.2‖ ≤ B * ‖p.1‖ :=
        (le_inv_mul_iff₀ hδ).2 hu
      exact hyBX.trans (mul_le_mul_of_nonneg_left
        ((hxR p hp).trans (le_max_right _ _)) hB)
  have hSbounded : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ × ℂ)]
    refine ⟨max R (B * max 1 R), ?_⟩
    intro p hp
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [Prod.norm_def]
    exact max_le ((hxR p hp).trans (le_max_left _ _))
      ((hyBound p hp).trans (le_max_right _ _))
  have hScompact : IsCompact S :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hSclosed, hSbounded⟩
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert hScompact using 1
  ext p
  simp [S, and_comm]

/-- The inverse rational coordinate map on the `y ≠ 0` affine locus, extended
by the branch origin both at one-point infinity and on the omitted `y = 0`
locus.  Its continuity is only asserted on the open target below. -/
noncomputable def complexWeierstrassOnePointToInfinityBranch (W : WeierstrassCurve ℂ)
    (P : OnePoint (ComplexWeierstrassAffine W)) :
    ComplexWeierstrassInfinityBranch W := by
  classical
  induction P using OnePoint.rec with
  | infty => exact complexWeierstrassInfinityBranchOrigin W
  | coe P =>
      exact if hy : P.1.2 = 0 then
        complexWeierstrassInfinityBranchOrigin W
      else (complexWeierstrassInfinityPuncturedHomeomorph W).symm ⟨P, hy⟩ |>.1

@[simp] theorem complexWeierstrassOnePointToInfinityBranch_infty (W : WeierstrassCurve ℂ) :
    complexWeierstrassOnePointToInfinityBranch W ∞ = complexWeierstrassInfinityBranchOrigin W := rfl

@[simp] theorem complexWeierstrassOnePointToInfinityBranch_coe_of_ne (W : WeierstrassCurve ℂ)
    (P : ComplexWeierstrassAffine W) (hy : P.1.2 ≠ 0) :
    complexWeierstrassOnePointToInfinityBranch W (P : OnePoint _) =
      ((complexWeierstrassInfinityPuncturedHomeomorph W).symm ⟨P, hy⟩).1 := by
  change (if h : P.1.2 = 0 then
      complexWeierstrassInfinityBranchOrigin W
    else ((complexWeierstrassInfinityPuncturedHomeomorph W).symm ⟨P, h⟩).1) = _
  rw [dif_neg hy]

@[simp] theorem complexWeierstrassInfinityBranchToOnePoint_of_snd_ne_zero
    (W : WeierstrassCurve ℂ) (Q : ComplexWeierstrassInfinityBranch W)
    (hv : Q.1.2 ≠ 0) :
    complexWeierstrassInfinityBranchToOnePoint W Q =
      (((complexWeierstrassInfinityPuncturedHomeomorph W ⟨Q, hv⟩).1 :
        ComplexWeierstrassAffine W) : OnePoint _) := by
  simp [complexWeierstrassInfinityBranchToOnePoint, hv]

/-- The projective branch map is continuous everywhere, not only at its
origin.  Away from the origin this follows from the punctured overlap
homeomorphism. -/
theorem continuous_complexWeierstrassInfinityBranchToOnePoint
    (W : WeierstrassCurve ℂ) :
    Continuous (complexWeierstrassInfinityBranchToOnePoint W) := by
  rw [continuous_iff_continuousAt]
  intro Q
  by_cases hv : Q.1.2 = 0
  · have hQ := (complexWeierstrassInfinityBranch_snd_eq_zero_iff W Q).1 hv
    simpa [hQ] using
      continuousAt_complexWeierstrassInfinityBranchToOnePoint_origin W
  · let U : Set (ComplexWeierstrassInfinityBranch W) := {R | R.1.2 ≠ 0}
    have hU : IsOpen U := isOpen_ne.preimage continuous_subtype_val.snd
    let qU : U := ⟨Q, hv⟩
    let g : U → OnePoint (ComplexWeierstrassAffine W) := fun R =>
      (((complexWeierstrassInfinityPuncturedHomeomorph W R).1 :
        ComplexWeierstrassAffine W) : OnePoint _)
    have hg : Continuous g := OnePoint.continuous_coe.comp
      (continuous_subtype_val.comp
        (complexWeierstrassInfinityPuncturedHomeomorph W).continuous)
    have heq :
        complexWeierstrassInfinityBranchToOnePoint W ∘
          ((↑) : U → ComplexWeierstrassInfinityBranch W) = g := by
      funext R
      exact complexWeierstrassInfinityBranchToOnePoint_of_snd_ne_zero W R.1 R.2
    have hc : ContinuousAt
        (complexWeierstrassInfinityBranchToOnePoint W ∘
          ((↑) : U → ComplexWeierstrassInfinityBranch W)) qU := by
      rw [heq]
      exact hg.continuousAt
    exact (hU.isOpenEmbedding_subtypeVal.continuousAt_iff).1 hc

private theorem continuousAt_complexWeierstrassOnePointToInfinityBranch_infty
    (W : WeierstrassCurve ℂ) :
    ContinuousAt (complexWeierstrassOnePointToInfinityBranch W) ∞ := by
  rw [OnePoint.continuousAt_infty]
  intro s hs
  rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := div_pos hε (by norm_num)
  let K : Set (ComplexWeierstrassAffine W) := {P |
    δ * ‖P.1.2‖ ≤ 1 ∨ δ * ‖P.1.2‖ ≤ ‖P.1.1‖}
  refine ⟨K, ?_, isCompact_complexWeierstrassInfinityControlSet W δ hδ, ?_⟩
  · exact (isCompact_complexWeierstrassInfinityControlSet W δ hδ).isClosed
  · intro P hP
    have hnot : ¬ (δ * ‖P.1.2‖ ≤ 1 ∨
        δ * ‖P.1.2‖ ≤ ‖P.1.1‖) := hP
    push Not at hnot
    have hy : P.1.2 ≠ 0 := by
      intro hy
      have : ‖P.1.1‖ < 0 := by simpa [hy] using hnot.2
      exact (not_lt_of_ge (norm_nonneg _)) this
    rw [Function.comp_apply, complexWeierstrassOnePointToInfinityBranch_coe_of_ne W P hy]
    apply hball
    rw [Metric.mem_ball]
    change dist
      (((complexWeierstrassInfinityPuncturedHomeomorph W).symm ⟨P, hy⟩).1 :
        ℂ × ℂ) (0, 0) < ε
    rw [Prod.dist_eq, max_lt_iff]
    have hcoe :
        ((((complexWeierstrassInfinityPuncturedHomeomorph W).symm
          ⟨P, hy⟩).1 : ComplexWeierstrassInfinityBranch W) : ℂ × ℂ) =
          (P.1.1 / P.1.2, 1 / P.1.2) := rfl
    rw [hcoe]
    constructor
    · rw [dist_zero_right, norm_div]
      have hratio : ‖P.1.1‖ / ‖P.1.2‖ < δ := by
        rw [div_lt_iff₀ (norm_pos_iff.mpr hy)]
        simpa [mul_comm] using hnot.2
      exact hratio.trans (by dsimp [δ]; linarith)
    · rw [dist_zero_right, norm_div, norm_one, one_div]
      have hinv : ‖P.1.2‖⁻¹ < δ := by
        rw [inv_lt_iff_one_lt_mul₀' (norm_pos_iff.mpr hy)]
        simpa [mul_comm] using hnot.1
      exact hinv.trans (by dsimp [δ]; linarith)

private theorem continuousAt_complexWeierstrassOnePointToInfinityBranch_coe_of_ne
    (W : WeierstrassCurve ℂ) (P : ComplexWeierstrassAffine W)
    (hy : P.1.2 ≠ 0) :
    ContinuousAt (complexWeierstrassOnePointToInfinityBranch W) (P : OnePoint _) := by
  let U : Set (ComplexWeierstrassAffine W) := {R | R.1.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage continuous_subtype_val.snd
  let j : U → OnePoint (ComplexWeierstrassAffine W) := fun R => (R.1 : OnePoint _)
  have hj : Topology.IsOpenEmbedding j :=
    OnePoint.isOpenEmbedding_coe.comp hU.isOpenEmbedding_subtypeVal
  let g : U → ComplexWeierstrassInfinityBranch W := fun R =>
    ((complexWeierstrassInfinityPuncturedHomeomorph W).symm R).1
  have hg : Continuous g := continuous_subtype_val.comp
    (complexWeierstrassInfinityPuncturedHomeomorph W).symm.continuous
  let pU : U := ⟨P, hy⟩
  have heq : complexWeierstrassOnePointToInfinityBranch W ∘ j = g := by
    funext R
    exact complexWeierstrassOnePointToInfinityBranch_coe_of_ne W R.1 R.2
  have hc : ContinuousAt (complexWeierstrassOnePointToInfinityBranch W ∘ j) pU := by
    rw [heq]
    exact hg.continuousAt
  exact hj.continuousAt_iff.mp hc

/-- The affine points with `y = 0` form a compact locus.  The proof uses the
same explicit cubic root bound as reverse continuity at infinity. -/
theorem isCompact_complexWeierstrassAffine_snd_eq_zero
    (W : WeierstrassCurve ℂ) :
    IsCompact {P : ComplexWeierstrassAffine W | P.1.2 = 0} := by
  let K : Set (ComplexWeierstrassAffine W) := {P |
    (1 : ℝ) * ‖P.1.2‖ ≤ 1 ∨ (1 : ℝ) * ‖P.1.2‖ ≤ ‖P.1.1‖}
  apply (isCompact_complexWeierstrassInfinityControlSet W 1 zero_lt_one).of_isClosed_subset
  · exact isClosed_eq continuous_subtype_val.snd continuous_const
  · intro P hP
    left
    change P.1.2 = 0 at hP
    simp [hP]

private theorem isOpen_infinityBranchTarget (W : WeierstrassCurve ℂ) :
    IsOpen (((↑) '' {P : ComplexWeierstrassAffine W | P.1.2 = 0})ᶜ :
      Set (OnePoint (ComplexWeierstrassAffine W))) := by
  rw [OnePoint.isOpen_compl_image_coe]
  exact ⟨isClosed_eq continuous_subtype_val.snd continuous_const,
    isCompact_complexWeierstrassAffine_snd_eq_zero W⟩

private theorem complexWeierstrassInfinityBranchToOnePoint_mem_target (W : WeierstrassCurve ℂ)
    (Q : ComplexWeierstrassInfinityBranch W) :
    complexWeierstrassInfinityBranchToOnePoint W Q ∈
      (((↑) '' {P : ComplexWeierstrassAffine W | P.1.2 = 0})ᶜ :
        Set (OnePoint (ComplexWeierstrassAffine W))) := by
  by_cases hv : Q.1.2 = 0
  · have hQ := (complexWeierstrassInfinityBranch_snd_eq_zero_iff W Q).1 hv
    simp [hQ]
  · rw [complexWeierstrassInfinityBranchToOnePoint_of_snd_ne_zero W Q hv]
    intro hmem
    rcases hmem with ⟨P, hPy, hP⟩
    have hPeq : P =
        (complexWeierstrassInfinityPuncturedHomeomorph W ⟨Q, hv⟩).1 :=
      OnePoint.coe_injective hP
    exact (complexWeierstrassInfinityPuncturedHomeomorph W ⟨Q, hv⟩).2
      (by simpa [hPeq] using hPy)

private theorem complexWeierstrassInfinityBranchToOnePoint_left_inv (W : WeierstrassCurve ℂ)
    (Q : ComplexWeierstrassInfinityBranch W) :
    complexWeierstrassOnePointToInfinityBranch W
      (complexWeierstrassInfinityBranchToOnePoint W Q) = Q := by
  by_cases hv : Q.1.2 = 0
  · have hQ := (complexWeierstrassInfinityBranch_snd_eq_zero_iff W Q).1 hv
    simp [hQ]
  · rw [complexWeierstrassInfinityBranchToOnePoint_of_snd_ne_zero W Q hv]
    let q : ComplexWeierstrassInfinityBranchPunctured W := ⟨Q, hv⟩
    let P : ComplexWeierstrassAffineYNeZero W :=
      complexWeierstrassInfinityPuncturedHomeomorph W q
    rw [complexWeierstrassOnePointToInfinityBranch_coe_of_ne W P.1 P.2]
    exact congrArg Subtype.val
      ((complexWeierstrassInfinityPuncturedHomeomorph W).symm_apply_apply q)

private theorem complexWeierstrassInfinityBranchToOnePoint_right_inv (W : WeierstrassCurve ℂ)
    (P : OnePoint (ComplexWeierstrassAffine W))
    (hP : P ∈ (((↑) '' {Q : ComplexWeierstrassAffine W | Q.1.2 = 0})ᶜ :
      Set (OnePoint (ComplexWeierstrassAffine W)))) :
    complexWeierstrassInfinityBranchToOnePoint W
      (complexWeierstrassOnePointToInfinityBranch W P) = P := by
  induction P using OnePoint.rec with
  | infty => simp
  | coe P =>
      have hy : P.1.2 ≠ 0 := by
        intro hy
        apply hP
        exact ⟨P, hy, rfl⟩
      rw [complexWeierstrassOnePointToInfinityBranch_coe_of_ne W P hy]
      let q : ComplexWeierstrassInfinityBranchPunctured W :=
        (complexWeierstrassInfinityPuncturedHomeomorph W).symm ⟨P, hy⟩
      rw [complexWeierstrassInfinityBranchToOnePoint_of_snd_ne_zero W q.1 q.2]
      exact congrArg (fun R : ComplexWeierstrassAffineYNeZero W =>
        (R.1 : OnePoint (ComplexWeierstrassAffine W)))
          ((complexWeierstrassInfinityPuncturedHomeomorph W).apply_symm_apply ⟨P, hy⟩)

/-- The complete projective `Y ≠ 0` branch is homeomorphic to the open
neighborhood of one-point infinity obtained by deleting the compact affine
locus `y = 0`.  Its source is all of the equation-defined branch. -/
noncomputable def complexWeierstrassInfinityBranchOpenPartialHomeomorph
    (W : WeierstrassCurve ℂ) :
    OpenPartialHomeomorph (ComplexWeierstrassInfinityBranch W)
      (OnePoint (ComplexWeierstrassAffine W)) where
  toFun := complexWeierstrassInfinityBranchToOnePoint W
  invFun := complexWeierstrassOnePointToInfinityBranch W
  source := Set.univ
  target := ((↑) '' {P : ComplexWeierstrassAffine W | P.1.2 = 0})ᶜ
  map_source' := fun Q _ => complexWeierstrassInfinityBranchToOnePoint_mem_target W Q
  map_target' := fun _ _ => Set.mem_univ _
  left_inv' := fun Q _ => complexWeierstrassInfinityBranchToOnePoint_left_inv W Q
  right_inv' := complexWeierstrassInfinityBranchToOnePoint_right_inv W
  open_source := isOpen_univ
  open_target := isOpen_infinityBranchTarget W
  continuousOn_toFun :=
    (continuous_complexWeierstrassInfinityBranchToOnePoint W).continuousOn
  continuousOn_invFun := by
    intro P hP
    induction P using OnePoint.rec with
    | infty => exact
        (continuousAt_complexWeierstrassOnePointToInfinityBranch_infty W).continuousWithinAt
    | coe P =>
        have hy : P.1.2 ≠ 0 := by
          intro hy
          apply hP
          exact ⟨P, hy, rfl⟩
        exact (continuousAt_complexWeierstrassOnePointToInfinityBranch_coe_of_ne W P hy).continuousWithinAt

/-- The projective branch embedded into the independently topologized compact
Weierstrass point space. -/
noncomputable def complexWeierstrassInfinityBranchToPoint
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ComplexWeierstrassInfinityBranch W → ComplexWeierstrassPoint W :=
  (complexWeierstrassPointHomeomorph W).symm ∘
    complexWeierstrassInfinityBranchToOnePoint W

@[simp] theorem complexWeierstrassInfinityBranchToPoint_origin
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    complexWeierstrassInfinityBranchToPoint W
        (complexWeierstrassInfinityBranchOrigin W) =
      complexWeierstrassPointInfinity W := by
  simp [complexWeierstrassInfinityBranchToPoint]

/-- The projective branch is an open subspace of the compact curve topology.
Its image is exactly the neighborhood obtained by deleting the affine points
with `y = 0`. -/
theorem isOpenEmbedding_complexWeierstrassInfinityBranchToPoint
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    Topology.IsOpenEmbedding (complexWeierstrassInfinityBranchToPoint W) := by
  exact (complexWeierstrassPointHomeomorph W).symm.isOpenEmbedding.comp
    ((complexWeierstrassInfinityBranchOpenPartialHomeomorph W).to_isOpenEmbedding rfl)

/-- The intrinsic infinity chart on the compact Weierstrass point space.  It
is obtained by extending the branch's `u`-coordinate chart along the proved
open embedding into the one-point compactification. -/
noncomputable def complexWeierstrassInfinityPointChart
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    OpenPartialHomeomorph (ComplexWeierstrassPoint W) ℂ :=
  (complexWeierstrassInfinityBranchChart W).lift_openEmbedding
    (isOpenEmbedding_complexWeierstrassInfinityBranchToPoint W)

/-- The compact point at infinity belongs to the source of the intrinsic
infinity chart. -/
theorem complexWeierstrassPointInfinity_mem_infinityPointChart_source
    (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    complexWeierstrassPointInfinity W ∈
      (complexWeierstrassInfinityPointChart W).source := by
  rw [complexWeierstrassInfinityPointChart,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨complexWeierstrassInfinityBranchOrigin W,
    complexWeierstrassInfinityBranchOrigin_mem_chart_source W, ?_⟩
  exact complexWeierstrassInfinityBranchToPoint_origin W

/-- On the embedded projective branch, the compact infinity chart is the
projective coordinate `u`. -/
@[simp] theorem complexWeierstrassInfinityPointChart_apply_branch
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (Q : ComplexWeierstrassInfinityBranch W) :
    complexWeierstrassInfinityPointChart W
        (complexWeierstrassInfinityBranchToPoint W Q) = Q.1.1 := by
  rw [complexWeierstrassInfinityPointChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

/-- The rational projective-to-affine overlap formula is holomorphic wherever
`v ≠ 0`. -/
theorem contDiffOn_complexWeierstrassInfinity_toAffine :
    ContDiffOn ℂ ω (fun uv : ℂ × ℂ => (uv.1 / uv.2, 1 / uv.2))
      {uv | uv.2 ≠ 0} := by
  exact (contDiff_fst.contDiffOn.div contDiff_snd.contDiffOn
      (fun uv huv => huv)).prodMk
    (contDiff_const.contDiffOn.div contDiff_snd.contDiffOn
      (fun uv huv => huv))

/-- The affine-to-projective overlap uses the same rational formula and is
holomorphic wherever `y ≠ 0`. -/
theorem contDiffOn_complexWeierstrassInfinity_toProjective :
    ContDiffOn ℂ ω (fun xy : ℂ × ℂ => (xy.1 / xy.2, 1 / xy.2))
      {xy | xy.2 ≠ 0} :=
  contDiffOn_complexWeierstrassInfinity_toAffine

end Heights
