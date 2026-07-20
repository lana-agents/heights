import Heights

/-!
# Heights comparator solution

This module re-exports only challenge targets for which a project proof exists.
`Comparator/config.json` lists the same proved targets.
-/

open scoped NumberField UpperHalfPlane nonZeroDivisors
open NumberField IsDedekindDomain

namespace Heights

/-- Comparator export of the proved rational-height scaling identity. -/
theorem rat_height_scaled_denominator (q : ℚ) (n : ℕ) (hn : 0 < n) :
    Height.logHeight₁ q + Real.log (n : ℝ) =
      Real.log ((max (q.num.natAbs * n) (q.den * n) : ℕ) : ℝ) :=
  ratHeight_scaled_denominator q n hn

/-- Comparator export of the proved weighted Jensen inequality. -/
theorem weighted_log_one_add_average
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) (d : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hd : ∑ i, w i = d) (hd_pos : 0 < d) :
    ∑ i, w i * Real.log (1 + x i) ≤
      d * Real.log (1 + (∑ i, w i * x i) / d) :=
  weightedLogOneAdd_le w x d hw hx hd hd_pos

/-- Comparator export of the fundamental-domain modular estimate. -/
theorem modular_delta_j_fd_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      |(-Real.log ‖silvermanModularDiscriminant τ‖) -
          Real.log (max ‖modularJ τ‖ 1)| ≤ C :=
  modularDeltaJ_fd_comparison

/-- Comparator export of the expanded certified Proposition 2.1 target. -/
theorem silverman_proposition_2_1_certified :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type*) [Field K] [NumberField K]
        (W : WeierstrassCurve K) [W.IsElliptic]
        (Δmin A D : Ideal (𝓞 K))
        (_hΔmin_ne : Δmin ≠ ⊥) (_hD_ne : D ≠ ⊥)
        (_hA_ne : W.j ≠ 0 → A ≠ ⊥)
        (_hzero : W.j = 0 → A = ⊥ ∧ D = ⊤)
        (_hcoprime : IsCoprime A D)
        (_hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ W.j =
          FractionalIdeal.coeIdeal A / FractionalIdeal.coeIdeal D)
        (_hminimal : ∀ v : HeightOneSpectrum (𝓞 K),
          ∃ change : WeierstrassCurve.VariableChange K,
            (v.valuation K (change • W).a₁ ≤ 1 ∧
              v.valuation K (change • W).a₂ ≤ 1 ∧
              v.valuation K (change • W).a₃ ≤ 1 ∧
              v.valuation K (change • W).a₄ ≤ 1 ∧
              v.valuation K (change • W).a₆ ≤ 1) ∧
            v.valuation K (change • W).Δ =
              WithZero.exp (-(multiplicity v.asIdeal Δmin : ℤ)) ∧
            ∀ other : WeierstrassCurve.VariableChange K,
              (v.valuation K (other • W).a₁ ≤ 1 ∧
                v.valuation K (other • W).a₂ ≤ 1 ∧
                v.valuation K (other • W).a₃ ≤ 1 ∧
                v.valuation K (other • W).a₄ ≤ 1 ∧
                v.valuation K (other • W).a₆ ≤ 1) →
              v.valuation K (other • W).Δ ≤
                WithZero.exp (-(multiplicity v.asIdeal Δmin : ℤ)))
        (τ : InfinitePlace K → ℍ)
        (_hfd : ∀ v, τ v ∈ ModularGroup.fd)
        (_hj : ∀ v, v.embedding W.j = modularJ (τ v)),
        ∃ hDvd : D ∣ Δmin,
        let hj := Height.logHeight₁ W.j / (Module.finrank ℚ K : ℝ);
        let γ := Classical.choose hDvd;
        let hF :=
          (Real.log (Ideal.absNorm Δmin) -
              ∑ v : InfinitePlace K,
                (v.mult : ℝ) * Real.log
                  (‖silvermanModularDiscriminant (τ v)‖ * (τ v).im ^ 6)) /
            (12 * (Module.finrank ℚ K : ℝ));
        -C ≤ hj + Real.log (Ideal.absNorm γ) / (Module.finrank ℚ K : ℝ) - 12 * hF ∧
          hj + Real.log (Ideal.absNorm γ) / (Module.finrank ℚ K : ℝ) - 12 * hF ≤
            6 * Real.log (1 + hj) + C := by
  rcases proposition_2_1_certified with ⟨C, hC, hall⟩
  refine ⟨C, hC, ?_⟩
  intro K _ _ W _ Δmin A D hΔmin hD hA hzero hcoprime hspan hminimal τ hfd hj
  let r : ReducedPrincipalIdealData K W.j :=
    { numerator := A
      denominator := D
      denominator_ne_bot := hD
      numerator_ne_bot := hA
      zero_normalization := hzero
      coprime := hcoprime
      span_eq := hspan }
  let m : GlobalMinimalDiscriminantData K W :=
    { ideal := Δmin
      ideal_ne_bot := hΔmin
      realizes := fun v => by
        let change := Classical.choose (hminimal v)
        have hs := Classical.choose_spec (hminimal v)
        exact
          { change := change
            integral := ⟨hs.1.1, hs.1.2.1, hs.1.2.2.1, hs.1.2.2.2.1,
              hs.1.2.2.2.2⟩
            exponent := hs.2.1
            maximal := fun other hother => hs.2.2 other
              ⟨hother.a₁, hother.a₂, hother.a₃, hother.a₄, hother.a₆⟩ } }
  let p : ArchimedeanPeriodData K W :=
    { τ := τ
      mem_fd := hfd
      j_eq := hj }
  have hdenominator : D = (reducedPrincipalIdealData K W.j).denominator :=
    r.denominator_eq (reducedPrincipalIdealData K W.j)
  have hDvd : D ∣ Δmin := by
    rw [hdenominator]
    exact denominator_dvd_minimalDiscriminant m
  refine ⟨hDvd, ?_⟩
  have hγ : Classical.choose hDvd = unstableMinimalDiscriminant m := by
    apply unstableMinimalDiscriminant_unique m
    rw [← hdenominator]
    exact (Classical.choose_spec hDvd).symm
  simpa [normalizedLogHeight, silvermanHeight, logIdealNorm, m, p, hγ] using
    hall K W m p

end Heights
