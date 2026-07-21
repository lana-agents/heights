import Heights.WeierstrassPrincipalPart
import Heights.WeierstrassDifferential

set_option linter.style.header false

/-!
# Differential identities for the Weierstrass secant law

For a point `(a,b/2)` on the short Weierstrass curve associated to a period
pair, this file studies the usual secant-law candidates obtained by adding
`(℘(z),℘′(z)/2)` to `(a,b/2)`.  Away from poles and a vertical secant, the
candidate coordinates satisfy

`X′ = 2Y` and `Y′ = 3X² - g₂/4`.

Thus `(X,2Y)` satisfies the same first-order polynomial ODE as `(℘,℘′)`.
Together with the removable limits at zero proved in
`Heights.WeierstrassPrincipalPart`, these identities are local analytic input
for the Weierstrass addition theorem.  No global addition identity or group
homomorphism is claimed here.
-/

open Set Filter Topology
open scoped Topology

noncomputable section
namespace Heights

/-- The slope of the secant from `(℘(z),℘′(z)/2)` to `(a,b/2)`. -/
def weierstrassSecantSlope (L : PeriodPair) (a b : ℂ) (z : ℂ) : ℂ :=
  (L.derivWeierstrassP z - b) / (2 * (L.weierstrassP z - a))

/-- The candidate `x`-coordinate supplied by the short-Weierstrass secant
law. -/
def weierstrassSecantAddX (L : PeriodPair) (a b : ℂ) (z : ℂ) : ℂ :=
  weierstrassSecantSlope L a b z ^ 2 - L.weierstrassP z - a

/-- The candidate `y`-coordinate supplied by the short-Weierstrass secant
law.  Here the curve point attached to `z` has second coordinate `℘′(z)/2`. -/
def weierstrassSecantAddY (L : PeriodPair) (a b : ℂ) (z : ℂ) : ℂ :=
  weierstrassSecantSlope L a b z *
      (L.weierstrassP z - weierstrassSecantAddX L a b z) -
    L.derivWeierstrassP z / 2

/-- The secant slope has derivative `℘ - X`.  The hypothesis on `(a,b)` says
that `(a,b/2)` lies on `y² = x³ - g₂x/4 - g₃/4`.

The explicit `HasDerivAt` parameters select the canonical complex normed-space
module, avoiding the two definitionally different `Module ℂ ℂ` instance paths
available in mathlib. -/
theorem hasDerivAt_weierstrassSecantSlope (L : PeriodPair) (a b z : ℂ)
    (hz : z ∉ L.lattice) (hpa : L.weierstrassP z ≠ a)
    (hab : b ^ 2 = 4 * a ^ 3 - L.g₂ * a - L.g₃) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _
      (weierstrassSecantSlope L a b)
      (L.weierstrassP z - weierstrassSecantAddX L a b z) z := by
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    rw [← L.deriv_weierstrassP]
    exact (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hpp : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
    rw [← deriv_derivWeierstrassP L z hz]
    exact (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hden : 2 * (L.weierstrassP z - a) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hpa)
  have hm : HasDerivAt (fun u : ℂ ↦
      (L.derivWeierstrassP u - b) / (2 * (L.weierstrassP u - a)))
      (((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) *
          (2 * (L.weierstrassP z - a)) -
        (L.derivWeierstrassP z - b) * (2 * L.derivWeierstrassP z)) /
        (2 * (L.weierstrassP z - a)) ^ 2) z :=
    (hpp.sub_const b).div ((hp.sub_const a).const_mul 2) hden
  have hcoeff :
      (((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) *
          (2 * (L.weierstrassP z - a)) -
        (L.derivWeierstrassP z - b) * (2 * L.derivWeierstrassP z)) /
        (2 * (L.weierstrassP z - a)) ^ 2) =
      L.weierstrassP z - weierstrassSecantAddX L a b z := by
    dsimp [weierstrassSecantAddX, weierstrassSecantSlope]
    have hpRel := L.derivWeierstrassP_sq z hz
    field_simp [hpa]
    linear_combination -hpRel + hab
  rw [hcoeff] at hm
  change @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
    RCLike.innerProductSpace.toModule _ _
    (fun u : ℂ ↦ (L.derivWeierstrassP u - b) /
      (2 * (L.weierstrassP u - a)))
    (L.weierstrassP z - weierstrassSecantAddX L a b z) z
  exact hm

/-- The secant candidate satisfies `X′ = 2Y` away from its poles and vertical
secants. -/
theorem hasDerivAt_weierstrassSecantAddX (L : PeriodPair) (a b z : ℂ)
    (hz : z ∉ L.lattice) (hpa : L.weierstrassP z ≠ a)
    (hab : b ^ 2 = 4 * a ^ 3 - L.g₂ * a - L.g₃) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _
      (weierstrassSecantAddX L a b)
      (2 * weierstrassSecantAddY L a b z) z := by
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    rw [← L.deriv_weierstrassP]
    exact (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hm := hasDerivAt_weierstrassSecantSlope L a b z hz hpa hab
  have hx := (hm.pow 2).sub hp |>.sub_const a
  change @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
    RCLike.innerProductSpace.toModule _ _
    (fun u : ℂ ↦ ((L.derivWeierstrassP u - b) /
      (2 * (L.weierstrassP u - a))) ^ 2 - L.weierstrassP u - a)
    (2 * weierstrassSecantAddY L a b z) z
  convert hx using 1
  · rfl
  · dsimp [weierstrassSecantAddY, weierstrassSecantAddX,
      weierstrassSecantSlope]
    ring

/-- The secant candidate satisfies `Y′ = 3X² - g₂/4` away from its poles and
vertical secants.  Consequently `(X,2Y)` obeys the same polynomial first-order
system as `(℘,℘′)`. -/
theorem hasDerivAt_weierstrassSecantAddY (L : PeriodPair) (a b z : ℂ)
    (hz : z ∉ L.lattice) (hpa : L.weierstrassP z ≠ a)
    (hab : b ^ 2 = 4 * a ^ 3 - L.g₂ * a - L.g₃) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _
      (weierstrassSecantAddY L a b)
      (3 * weierstrassSecantAddX L a b z ^ 2 - L.g₂ / 4) z := by
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    rw [← L.deriv_weierstrassP]
    exact (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hpp : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
    rw [← deriv_derivWeierstrassP L z hz]
    exact (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hm := hasDerivAt_weierstrassSecantSlope L a b z hz hpa hab
  have hx := hasDerivAt_weierstrassSecantAddX L a b z hz hpa hab
  have hy := (hm.mul (hp.sub hx)).sub (hpp.div_const 2)
  change @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
    RCLike.innerProductSpace.toModule _ _
    (fun u : ℂ ↦ ((L.derivWeierstrassP u - b) /
      (2 * (L.weierstrassP u - a))) *
      (L.weierstrassP u - (((L.derivWeierstrassP u - b) /
        (2 * (L.weierstrassP u - a))) ^ 2 - L.weierstrassP u - a)) -
      L.derivWeierstrassP u / 2)
    (3 * weierstrassSecantAddX L a b z ^ 2 - L.g₂ / 4) z
  convert hy using 1
  · funext u
    rfl
  · dsimp [weierstrassSecantAddY, weierstrassSecantAddX,
      weierstrassSecantSlope]
    have hpRel := L.derivWeierstrassP_sq z hz
    field_simp [hpa]
    linear_combination
      (-32 * (L.weierstrassP z - a) ^ 3) * hpRel +
      (32 * (L.weierstrassP z - a) ^ 3) * hab

/-- The previously proved removable limit for the secant `x`-candidate,
rephrased using the named definition in this file. -/
theorem tendsto_weierstrassSecantAddX_zero (L : PeriodPair) (a b : ℂ) :
    Tendsto (weierstrassSecantAddX L a b) (𝓝[≠] 0) (𝓝 a) := by
  change Tendsto (fun z : ℂ ↦
    ((L.derivWeierstrassP z - b) /
      (2 * (L.weierstrassP z - a))) ^ 2 - L.weierstrassP z - a)
    (𝓝[≠] 0) (𝓝 a)
  exact tendsto_weierstrass_secant_addX_zero L a b

/-- The previously proved removable limit for the secant `y`-candidate,
rephrased using the named definition in this file. -/
theorem tendsto_weierstrassSecantAddY_zero (L : PeriodPair) (a b : ℂ) :
    Tendsto (weierstrassSecantAddY L a b) (𝓝[≠] 0) (𝓝 (b / 2)) := by
  change Tendsto (fun z : ℂ ↦
    let s := (L.derivWeierstrassP z - b) /
      (2 * (L.weierstrassP z - a))
    let x := s ^ 2 - L.weierstrassP z - a
    s * (L.weierstrassP z - x) - L.derivWeierstrassP z / 2)
    (𝓝[≠] 0) (𝓝 (b / 2))
  exact tendsto_weierstrass_secant_addY_zero L a b

end Heights
