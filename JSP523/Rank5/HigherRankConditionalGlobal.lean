import JSP523.Rank5.HigherRankConditionalGlobalScalar
import JSP523.Rank5.UniformDegreeGap

/-! # Conditional extraction and uniform high-rank closing

The endpoint interface concerns the actual regularized parent family.
All extraction parameters, positive mass, and the uniformization step
are supplied here by previously proved concrete theorems.
-/

namespace JSP523.Rank5

open Filter

/-- The concrete higher-rank mass endpoint closes the conditional
extraction at every large ambient size. -/
theorem higher_rank_conditional_exclusion_of_structural_endpoint
    (r : ℕ) (δ : ℝ) (hr : 6 ≤ r) (hδ : 0 < δ)
    (hEndpoint : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ K : Family (Fin n),
        Admissible K → Uniform r K →
        (∀ j, 2 ≤ j → j ≤ r - 1 → ∀ S : Edge (Fin n), S.card = j →
          (K.filter fun E => S ⊆ E).card ≤
            discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (r - j - 1)) →
        (K.card : ℝ) ≤ ε * ((n : ℝ) ^ (r - 1) + K.card))
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform r (H n))
    (hMax : ∀ n z, ((H n).filter fun E => z ∈ E).card ≤ M n) :
    ∀ᶠ n : ℕ in atTop,
      ¬ ((M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ) ∧
        (n - 1).choose (r - 1) ≤ (H n).card) := by
  obtain ⟨a, b, m, ha, hb, hm, hExtract⟩ :=
    eventually_conditional_initial_polynomial_extraction r 9 δ (by omega) hδ
      H M hAdm hUniform hMax
  let D := 2 ^ (r - 1) * (r - 1).factorial
  have hD : 0 < D := Nat.mul_pos (pow_pos (by decide) _) (Nat.factorial_pos _)
  let ε : ℝ := 1 / (16 * (b : ℝ) * D)
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [hExtract, hEndpoint ε hε,
    eventually_ge_atTop (2 * (r - 1) + 1)] with n hExtractN hEndpointN hn
  rintro ⟨hGapN, hMassN⟩
  obtain ⟨K₀, K, _hKK₀, _hK₀Out, _hK₀H, hAdmK, hUniformK,
    hCapsK, hMassK, _hDiscard, _hRoundDiscard, _hLedger⟩ := hExtractN hGapN hMassN
  have hMass : a * (n - 1).choose (r - 1) ≤ 4 * b * K.card := by
    have hScaled : m * (a * (n - 1).choose (r - 1)) ≤ m * (4 * b * K.card) := by
      calc
        m * (a * (n - 1).choose (r - 1)) = m * a * (n - 1).choose (r - 1) := by ring
        _ ≤ 4 * m * b * K.card := hMassK
        _ = m * (4 * b * K.card) := by ring
    exact Nat.le_of_mul_le_mul_left hScaled hm
  have hPower : n ^ (r - 1) ≤ D * (n - 1).choose (r - 1) :=
    far_star_power_le_choose_multiple n (r - 1) hn
  have hB : 0 < (n - 1).choose (r - 1) := Nat.choose_pos (by omega)
  have hEndpointK := hEndpointN K hAdmK hUniformK
    (fun j hj hjr S hS => hCapsK j (by omega) hjr S hS)
  exact positive_mass_excludes_higher_rank_scaled_endpoint a b D
    ((n - 1).choose (r - 1)) (n ^ (r - 1)) K.card ha hb hD hB hMass hPower
    (by simpa only [ε, Nat.cast_pow] using hEndpointK)

/-- Uniform degree concentration follows from the actual parent-family
structural endpoint, without assumptions on the spacing of counterexamples. -/
theorem higher_rank_uniform_concentration_of_structural_endpoint
    (r : ℕ) (δ : ℝ) (hr : 6 ≤ r) (hδ : 0 < δ)
    (hEndpoint : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ K : Family (Fin n),
        Admissible K → Uniform r K →
        (∀ j, 2 ≤ j → j ≤ r - 1 → ∀ S : Edge (Fin n), S.card = j →
          (K.filter fun E => S ⊆ E).card ≤
            discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (r - j - 1)) →
        (K.card : ℝ) ≤ ε * ((n : ℝ) ^ (r - 1) + K.card)) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin n),
      Admissible F → Uniform r F → (n - 1).choose (r - 1) ≤ F.card →
      ∃ z : Fin n, (1 - δ) * ((n - 1).choose (r - 1) : ℝ) <
        ((F.filter fun E => z ∈ E).card : ℝ) := by
  exact eventually_uniform_degree_concentration_of_conditional_exclusion r δ
    (higher_rank_conditional_exclusion_of_structural_endpoint r δ hr hδ hEndpoint)

end JSP523.Rank5
