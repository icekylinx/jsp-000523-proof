import JSP523.Rank5.ConditionalExtraction

/-! # Scalar contradiction for the higher-rank positive-mass extraction

The higher-rank endpoint concerns mass directly, so no shadow ledger
or extraction-loss estimate enters this closing step.
-/

namespace JSP523.Rank5

/-- A sufficiently small direct mass endpoint contradicts any fixed
positive extracted mass. -/
theorem positive_mass_excludes_higher_rank_real_endpoint
    (a b B K endpointConstant endpointMass : ℝ)
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hMass : a * B ≤ b * K)
    (hEndpoint : K ≤ endpointConstant + endpointMass * K)
    (hMassError : endpointMass ≤ 1 / 2)
    (hSmall : 2 * b * endpointConstant < a * B) : False := by
  have hMassTerm : endpointMass * K ≤ K / 2 := by
    have h := mul_le_mul_of_nonneg_right hMassError hK
    nlinarith
  have hKBound : K ≤ 2 * endpointConstant := by linarith
  have hScaled := mul_le_mul_of_nonneg_left hKBound hb
  nlinarith

/-- The explicit choice `ε=1/(16βD)` pays both the ambient-power error
and the parent-mass error in a higher-rank structural endpoint. -/
theorem positive_mass_excludes_higher_rank_scaled_endpoint
    (a b D B N K : ℕ) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hB : 0 < B) (hMass : a * B ≤ 4 * b * K) (hPower : N ≤ D * B)
    (hEndpoint : (K : ℝ) ≤
      (1 / (16 * (b : ℝ) * D)) * ((N : ℝ) + K)) : False := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hden : (0 : ℝ) < 16 * (b : ℝ) * D := by positivity
  have hε : (1 / (16 * (b : ℝ) * D)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hDR (show 0 ≤ (b : ℝ) by positivity)]
  have hPowerR : (N : ℝ) ≤ (D : ℝ) * B := by exact_mod_cast hPower
  have hSmall : 2 * (4 * (b : ℝ)) *
      ((1 / (16 * (b : ℝ) * D)) * N) < (a : ℝ) * B := by
    have hId : 2 * (4 * (b : ℝ)) *
        ((1 / (16 * (b : ℝ) * D)) * N) = (N : ℝ) / (2 * D) := by
      field_simp
      ring
    rw [hId]
    have hBound : (N : ℝ) / (2 * D) ≤ (B : ℝ) / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D)).2
      nlinarith only [hPowerR]
    have hAB := mul_le_mul_of_nonneg_right haR hBR.le
    linarith
  exact positive_mass_excludes_higher_rank_real_endpoint
    a (4 * (b : ℝ)) B K
    ((1 / (16 * (b : ℝ) * D)) * N) (1 / (16 * (b : ℝ) * D))
    (by positivity) (Nat.cast_nonneg K) (by exact_mod_cast hMass)
    (by nlinarith only [hEndpoint]) hε hSmall

end JSP523.Rank5
