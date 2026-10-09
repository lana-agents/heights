/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Heights.LatticeQuotientTopology
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option linter.style.header false

/-!
# Complex-manifold structure on the lattice quotient

The quotient covering `ℂ → ℂ/L` supplies local inverse charts. Their transition
maps are locally translations by lattice elements, hence complex analytic. This
file uses that fact to equip `ℂ/L` with a one-dimensional complex-manifold
structure and proves that the quotient projection is locally biholomorphic.

This construction is intrinsic to the lattice quotient. It does not transport
an atlas from a Weierstrass curve, define a differential form on the quotient,
or prove that the Weierstrass point map is analytic.
-/

open Topology Set Filter
open scoped UpperHalfPlane Manifold
noncomputable section
namespace Heights

noncomputable instance latticeQuotientChartedSpace (τ : ℍ) :
    ChartedSpace ℂ (LatticeQuotient τ) :=
  (isCoveringMap_latticeQuotientMk τ).isLocalHomeomorph.chartedSpace
    (isAddQuotientCoveringMap_latticeQuotientMk τ).surjective

private theorem contDiffOn_latticeQuotient_localInverse_transition (τ : ℍ)
    (a b : ℂ) :
    let hf := (isCoveringMap_latticeQuotientMk τ).isLocalHomeomorph
    ContDiffOn ℂ ω ((hf.localInverseAt a).symm.trans (hf.localInverseAt b))
      ((hf.localInverseAt a).symm.trans (hf.localInverseAt b)).source := by
  dsimp only
  let hf := (isCoveringMap_latticeQuotientMk τ).isLocalHomeomorph
  let A := hf.localInverseAt a
  let B := hf.localInverseAt b
  intro z hz
  have hzsource := hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  have hBsource : latticeQuotientMk τ z ∈ B.source := by
    change z ∈ latticeQuotientMk τ ⁻¹' B.source
    simpa only [A, hf, IsLocalHomeomorph.localInverseAt_symm] using hz.2
  let y : ℂ := B (latticeQuotientMk τ z)
  let c : ℂ := y - z
  have hyB : y ∈ B.target := B.map_source hBsource
  have hmk_y : latticeQuotientMk τ y = latticeQuotientMk τ z := by
    exact hf.apply_localInverseAt_of_mem hBsource
  have hc : c ∈ (periodPairOfUpperHalfPlane τ).lattice.toAddSubgroup := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp hmk_y
  have heq : (fun w : ℂ ↦ ((A.symm.trans B) w)) =ᶠ[
      𝓝[(A.symm.trans B).source] z] (fun w ↦ w + c) := by
    have hV : {w : ℂ | w + c ∈ B.target} ∈ 𝓝 z := by
      apply (B.open_target.preimage (continuous_id.add continuous_const)).mem_nhds
      change z + c ∈ B.target
      simpa [c, y] using hyB
    filter_upwards [Filter.Eventually.filter_mono inf_le_left hV,
      self_mem_nhdsWithin] with w hwV hwsource
    rw [OpenPartialHomeomorph.trans_source] at hwsource
    have hwBsource : latticeQuotientMk τ w ∈ B.source := by
      change w ∈ latticeQuotientMk τ ⁻¹' B.source
      simpa only [A, hf, IsLocalHomeomorph.localInverseAt_symm] using hwsource.2
    rw [OpenPartialHomeomorph.trans_apply]
    rw [show (A.symm : ℂ → LatticeQuotient τ) = latticeQuotientMk τ by
      exact hf.localInverseAt_symm a]
    change B (latticeQuotientMk τ w) = w + c
    apply hf.injOn_localInverseAt_target
    · exact B.map_source hwBsource
    · exact hwV
    · rw [hf.apply_localInverseAt_of_mem hwBsource]
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hc)
  apply ((contDiffAt_id.add contDiffAt_const).contDiffWithinAt).congr_of_eventuallyEq heq
  simpa only [id_eq] using heq.self_of_nhdsWithin hzsource

noncomputable instance latticeQuotientComplexManifold (τ : ℍ) :
    IsManifold 𝓘(ℂ) ω (LatticeQuotient τ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ @ChartedSpace.atlas ℂ _ (LatticeQuotient τ) _
    (latticeQuotientChartedSpace τ) at he
  change ∃ q : LatticeQuotient τ, _ = e at he
  rcases he with ⟨q, rfl⟩
  change e' ∈ @ChartedSpace.atlas ℂ _ (LatticeQuotient τ) _
    (latticeQuotientChartedSpace τ) at he'
  change ∃ q : LatticeQuotient τ, _ = e' at he'
  rcases he' with ⟨q', rfl⟩
  simp only [chartAt_self_eq]
  simpa using contDiffOn_latticeQuotient_localInverse_transition τ
    ((isAddQuotientCoveringMap_latticeQuotientMk τ).surjective.hasRightInverse.choose q)
    ((isAddQuotientCoveringMap_latticeQuotientMk τ).surjective.hasRightInverse.choose q')

/-- Every covering-space local inverse is a holomorphic chart, even though
the chosen charted-space atlas contains only one selected lift over each
quotient point. -/
theorem latticeQuotientLocalInverse_mem_maximalAtlas (τ : ℍ) (a : ℂ) :
    let hf := (isCoveringMap_latticeQuotientMk τ).isLocalHomeomorph
    hf.localInverseAt a ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (LatticeQuotient τ) := by
  dsimp only
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e he
  change e ∈ @ChartedSpace.atlas ℂ _ (LatticeQuotient τ) _
    (latticeQuotientChartedSpace τ) at he
  change ∃ q : LatticeQuotient τ, _ = e at he
  rcases he with ⟨q, rfl⟩
  simp only [chartAt_self_eq]
  constructor
  · rw [contDiffGroupoid]
    constructor <;> simp only [contDiffPregroupoid,
      ModelWithCorners.range_eq_univ, inter_univ]
    · simpa using contDiffOn_latticeQuotient_localInverse_transition τ a _
    · simpa using contDiffOn_latticeQuotient_localInverse_transition τ _ a
  · rw [contDiffGroupoid]
    constructor <;> simp only [contDiffPregroupoid,
      ModelWithCorners.range_eq_univ, inter_univ]
    · simpa using contDiffOn_latticeQuotient_localInverse_transition τ _ a
    · simpa using contDiffOn_latticeQuotient_localInverse_transition τ a _

/-- The quotient projection is locally biholomorphic for the independently
constructed complex-manifold structure on the lattice quotient. -/
theorem isLocalDiffeomorph_latticeQuotientMk (τ : ℍ) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (latticeQuotientMk τ) := by
  intro z
  let hf := (isCoveringMap_latticeQuotientMk τ).isLocalHomeomorph
  let B := hf.localInverseAt z
  have hB : B ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (LatticeQuotient τ) :=
    latticeQuotientLocalInverse_mem_maximalAtlas τ z
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ (LatticeQuotient τ) ω := {
    toPartialEquiv := B.symm.toPartialEquiv
    open_source := B.symm.open_source
    open_target := B.symm.open_target
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hB
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hB }
  refine ⟨Φ, ?_, ?_⟩
  · exact hf.self_mem_localInverseAt_target
  · intro w hw
    change latticeQuotientMk τ w = B.symm w
    exact congrFun (hf.localInverseAt_symm z).symm w

/-- The quotient projection is holomorphic. The stronger local-biholomorphism
theorem above also records holomorphicity of its local inverses. -/
theorem contMDiff_latticeQuotientMk (τ : ℍ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (latticeQuotientMk τ) :=
  (isLocalDiffeomorph_latticeQuotientMk τ).contMDiff

end Heights
