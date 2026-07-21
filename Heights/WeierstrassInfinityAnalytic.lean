import Heights.WeierstrassFiniteManifold
import Mathlib.Analysis.Calculus.ImplicitContDiff

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

This is the analytic projective germ needed by an infinity chart.  It does not
yet prove that adjoining its origin induces the one-point-compactification
topology on `ComplexWeierstrassPoint W`; that properness/topology comparison is
kept as an explicit remaining step.
-/

open Filter
open scoped ContDiff Topology

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
