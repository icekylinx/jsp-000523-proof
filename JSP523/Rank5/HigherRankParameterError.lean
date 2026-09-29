import JSP523.Rank5.HigherRankRepairedLoss
import JSP523.Rank5.FinalParameterRoot
import JSP523.Rank5.HigherRankParameterFeasibility

/-! # Higher-rank inheritance errors at the common integer-root scale

Use rho=U⁻³, t_s=N^(r-s-2)/U⁹ and q_s=N^(s-1)/U⁶.
The s=3 error is U²⁷ N^(r-2), compatible with U³²≤N even at r=6.
-/
namespace JSP523.Rank5

/-- A spare factor of the ambient size absorbs each fixed root-scale
    monomial whose exponent is below 32. -/
theorem higher_scale_monomial_bound
    (N U : ℝ) (hU : 1 ≤ U) (hN : U ^ 32 ≤ N)
    (a d : ℕ) (ha : a + 1 ≤ 32) :
    U ^ a * N ^ d ≤ N ^ (d + 1) / U := by
  have hUp : 0 < U := by linarith
  have hPow : U ^ (a + 1) ≤ N := (pow_le_pow_right₀ hU ha).trans hN
  have hN0 : 0 ≤ N := (by positivity : 0 ≤ U ^ 32).trans hN
  apply (le_div_iff₀ hUp).2
  calc
    U ^ a * N ^ d * U = U ^ (a + 1) * N ^ d := by rw [pow_succ]; ring
    _ ≤ N * N ^ d := mul_le_mul_of_nonneg_right hPow (by positivity)
    _ = N ^ (d + 1) := by rw [pow_succ]; ring

/-- The s=2 inherited-facet witness error, with r=k+6. -/
theorem higher_facet_inheritance_scale_envelope
    (N U tPair qPair : ℝ) (k : ℕ)
    (hU : 1 ≤ U) (hN : U ^ 32 ≤ N)
    (ht : N ^ (k + 2) / (2 * U ^ 9) ≤ tPair)
    (hq : N / (2 * U ^ 6) ≤ qPair) :
    512 * U ^ 6 * N ^ (2 * k + 7) / (8 * tPair * qPair) ≤
      256 * (N ^ (k + 5) / U) := by
  have hUp : 0 < U := by linarith
  have hNp : 0 < N := lt_of_lt_of_le (by positivity) hN
  have htLo : 0 < N ^ (k + 2) / (2 * U ^ 9) := by positivity
  have hqLo : 0 < N / (2 * U ^ 6) := by positivity
  have htPos := lt_of_lt_of_le htLo ht
  have hqPos := lt_of_lt_of_le hqLo hq
  have hBound : 512 * U ^ 6 * N ^ (2 * k + 7) / (8 * tPair * qPair) ≤
      512 * U ^ 6 * N ^ (2 * k + 7) /
        (8 * (N ^ (k + 2) / (2 * U ^ 9)) * (N / (2 * U ^ 6))) := by
    gcongr
  have hId : 512 * U ^ 6 * N ^ (2 * k + 7) /
      (8 * (N ^ (k + 2) / (2 * U ^ 9)) * (N / (2 * U ^ 6))) =
      256 * (U ^ 21 * N ^ (k + 4)) := by
    field_simp
    simp only [show 2 * k + 7 = k + k + 7 by omega, pow_add]
    ring
  rw [hId] at hBound
  have hMono := higher_scale_monomial_bound N U hU hN 21 (k + 4) (by omega)
  have hScaled := mul_le_mul_of_nonneg_left hMono (by norm_num : (0 : ℝ) ≤ 256)
  exact hBound.trans (by simpa only [show k + 4 + 1 = k + 5 by omega] using hScaled)

/-- The s=3 lower-deletion witness error, retaining the pinned D₅ cap. -/
theorem higher_lower_inheritance_scale_envelope
    (N U tTriple qPair qTriple : ℝ) (k : ℕ)
    (hU : 1 ≤ U) (hN : U ^ 32 ≤ N)
    (ht : N ^ (k + 1) / (2 * U ^ 9) ≤ tTriple)
    (hqPair : N / (2 * U ^ 6) ≤ qPair)
    (hqTriple : N ^ 2 / (2 * U ^ 6) ≤ qTriple) :
    768 * U ^ 6 * N ^ (2 * k + 8) / (16 * tTriple * qPair * qTriple) ≤
      384 * (N ^ (k + 5) / U) := by
  have hUp : 0 < U := by linarith
  have hNp : 0 < N := lt_of_lt_of_le (by positivity) hN
  have htLo : 0 < N ^ (k + 1) / (2 * U ^ 9) := by positivity
  have hqPairLo : 0 < N / (2 * U ^ 6) := by positivity
  have hqTripleLo : 0 < N ^ 2 / (2 * U ^ 6) := by positivity
  have htPos := lt_of_lt_of_le htLo ht
  have hqPairPos := lt_of_lt_of_le hqPairLo hqPair
  have hqTriplePos := lt_of_lt_of_le hqTripleLo hqTriple
  have hBound : 768 * U ^ 6 * N ^ (2 * k + 8) / (16 * tTriple * qPair * qTriple) ≤
      768 * U ^ 6 * N ^ (2 * k + 8) /
        (16 * (N ^ (k + 1) / (2 * U ^ 9)) *
          (N / (2 * U ^ 6)) * (N ^ 2 / (2 * U ^ 6))) := by
    gcongr
  have hId : 768 * U ^ 6 * N ^ (2 * k + 8) /
      (16 * (N ^ (k + 1) / (2 * U ^ 9)) *
        (N / (2 * U ^ 6)) * (N ^ 2 / (2 * U ^ 6))) =
      384 * (U ^ 27 * N ^ (k + 4)) := by
    field_simp
    simp only [show 2 * k + 8 = k + k + 8 by omega, pow_add]
    ring
  rw [hId] at hBound
  have hMono := higher_scale_monomial_bound N U hU hN 27 (k + 4) (by omega)
  have hScaled := mul_le_mul_of_nonneg_left hMono (by norm_num : (0 : ℝ) ≤ 384)
  exact hBound.trans (by simpa only [show k + 4 + 1 = k + 5 by omega] using hScaled)

/-- Both actual repairs cost a vanishing fraction of parent mass plus
    O_r(N^(r-1)/U). The constants are uniform in the ambient size. -/
theorem higher_inheritance_scale_envelope
    (N U m C tPair tTriple qPair qTriple : ℝ) (k : ℕ)
    (hU : 1 ≤ U) (hN : U ^ 32 ≤ N) (hm : 0 ≤ m) (hC : 0 ≤ C)
    (htPair : N ^ (k + 2) / (2 * U ^ 9) ≤ tPair)
    (htTriple : N ^ (k + 1) / (2 * U ^ 9) ≤ tTriple)
    (hqPair : N / (2 * U ^ 6) ≤ qPair)
    (hqTriple : N ^ 2 / (2 * U ^ 6) ≤ qTriple) :
    16 * C * m / U ^ 3 +
      512 * U ^ 6 * N ^ (2 * k + 7) / (8 * tPair * qPair) +
      768 * U ^ 6 * N ^ (2 * k + 8) / (16 * tTriple * qPair * qTriple) ≤
      16 * C * (m / U) + 640 * (N ^ (k + 5) / U) := by
  have hUp : 0 < U := by linarith
  have hLow : m / U ^ 3 ≤ m / U := by
    apply div_le_div_of_nonneg_left hm hUp
    simpa only [pow_one] using pow_le_pow_right₀ hU (by omega : 1 ≤ 3)
  have hLowScaled := mul_le_mul_of_nonneg_left hLow (by positivity : 0 ≤ 16 * C)
  have hLowScaled' : 16 * C * m / U ^ 3 ≤ 16 * C * (m / U) := by
    calc
      16 * C * m / U ^ 3 = 16 * C * (m / U ^ 3) := by ring
      _ ≤ _ := hLowScaled
  have hFacet := higher_facet_inheritance_scale_envelope N U tPair qPair k hU hN htPair hqPair
  have hLower := higher_lower_inheritance_scale_envelope N U tTriple qPair qTriple k
    hU hN htTriple hqPair hqTriple
  linarith only [hLowScaled', hFacet, hLower]

/-- The scaled finite repair inequality gives its two separate error terms. -/
theorem higher_scaled_repair_budget_divide
    (Q M₂ M₃ loss mass W₂ W₃ : ℝ)
    (hQ : 0 < Q) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hBudget : Q * M₂ * M₃ * loss ≤
      M₂ * M₃ * mass + Q * (M₂ * W₃ + M₃ * W₂)) :
    loss ≤ mass / Q + W₂ / M₂ + W₃ / M₃ := by
  apply (mul_le_mul_iff_left₀ (show 0 < Q * M₂ * M₃ by positivity)).mp
  calc
    loss * (Q * M₂ * M₃) = Q * M₂ * M₃ * loss := by ring
    _ ≤ _ := hBudget
    _ = (mass / Q + W₂ / M₂ + W₃ / M₃) * (Q * M₂ * M₃) := by
      field_simp
      ring

/-- Cast the finite natural-number budget without losing its two denominators. -/
theorem higher_nat_scaled_repair_budget_divide
    (Q M₂ M₃ loss mass W₂ W₃ : ℕ)
    (hQ : 0 < Q) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hBudget : Q * M₂ * M₃ * loss ≤
      M₂ * M₃ * mass + Q * (M₂ * W₃ + M₃ * W₂)) :
    (loss : ℝ) ≤ (mass : ℝ) / Q + (W₂ : ℝ) / M₂ + (W₃ : ℝ) / M₃ := by
  apply higher_scaled_repair_budget_divide
  · exact_mod_cast hQ
  · exact_mod_cast hM₂
  · exact_mod_cast hM₃
  · exact_mod_cast hBudget

/-- The exact s=2 witness numerator under the extracted codegree caps. -/
theorem higher_facet_witness_numerator_bound
    (N U D₃ D₄ DFacet k : ℕ)
    (hD₃ : D₃ ≤ 4 * U ^ 2 * N ^ (k + 2))
    (hD₄ : D₄ ≤ 4 * U ^ 2 * N ^ (k + 1))
    (hDFacet : DFacet ≤ 4 * U ^ 2) :
    8 * (N.choose 2) ^ 2 * D₃ * DFacet * D₄ ≤
      512 * U ^ 6 * N ^ (2 * k + 7) := by
  calc
    _ ≤ 8 * (N ^ 2) ^ 2 * (4 * U ^ 2 * N ^ (k + 2)) *
        (4 * U ^ 2) * (4 * U ^ 2 * N ^ (k + 1)) := by
      gcongr
      exact Nat.choose_le_pow N 2
    _ = _ := by
      simp only [show 2 * k + 7 = k + k + 7 by omega, pow_add]
      ring

/-- The exact s=3 witness numerator keeps the separate fixed D₅ cap. -/
theorem higher_lower_witness_numerator_bound
    (N U D₄ D₅ DBase k : ℕ)
    (hD₄ : D₄ ≤ 4 * U ^ 2 * N ^ (k + 1))
    (hD₅ : D₅ ≤ 4 * U ^ 2 * N ^ k)
    (hDBase : DBase ≤ 4 * U ^ 2 * N) :
    12 * (N.choose 3) ^ 2 * D₄ * DBase * D₅ ≤
      768 * U ^ 6 * N ^ (2 * k + 8) := by
  calc
    _ ≤ 12 * (N ^ 3) ^ 2 * (4 * U ^ 2 * N ^ (k + 1)) *
        (4 * U ^ 2 * N) * (4 * U ^ 2 * N ^ k) := by
      gcongr
      exact Nat.choose_le_pow N 3
    _ = _ := by
      simp only [show 2 * k + 8 = k + k + 8 by omega, pow_add]
      ring

/-- The same error envelope for the actual integer-rounded thresholds. -/
theorem higher_rounded_inheritance_scale_envelope
    (N U : ℕ) (m C : ℝ) (k : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ N) (hm : 0 ≤ m) (hC : 0 ≤ C) :
    let tPair : ℝ := (N ^ (k + 2) / U ^ 9 : ℕ)
    let tTriple : ℝ := (N ^ (k + 1) / U ^ 9 : ℕ)
    let qPair : ℝ := (N / U ^ 6 : ℕ)
    let qTriple : ℝ := (N ^ 2 / U ^ 6 : ℕ)
    16 * C * m / (U : ℝ) ^ 3 +
      512 * (U : ℝ) ^ 6 * (N : ℝ) ^ (2 * k + 7) / (8 * tPair * qPair) +
      768 * (U : ℝ) ^ 6 * (N : ℝ) ^ (2 * k + 8) /
        (16 * tTriple * qPair * qTriple) ≤
      16 * C * (m / U) + 640 * ((N : ℝ) ^ (k + 5) / U) := by
  have hUOne : 1 ≤ U := by omega
  apply higher_inheritance_scale_envelope
  · exact_mod_cast hUOne
  · exact_mod_cast hN
  · exact hm
  · exact hC
  · exact (higher_power_quotient_real_bounds N U (k + 2) 9 hUOne hN
      (by omega) (by omega)).1
  · exact (higher_power_quotient_real_bounds N U (k + 1) 9 hUOne hN
      (by omega) (by omega)).1
  · simpa only [pow_one] using
      (higher_power_quotient_real_bounds N U 1 6 hUOne hN (by omega) (by omega)).1
  · exact (higher_power_quotient_real_bounds N U 2 6 hUOne hN
      (by omega) (by omega)).1

/-- Apply the error envelope directly to a finite two-repair budget. -/
theorem higher_repair_scale_bound_of_budget
    (N U k loss m C tPair tTriple qPair qTriple W₂ W₃ : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ N)
    (htPair : (N : ℝ) ^ (k + 2) / (2 * (U : ℝ) ^ 9) ≤ tPair)
    (htTriple : (N : ℝ) ^ (k + 1) / (2 * (U : ℝ) ^ 9) ≤ tTriple)
    (hqPair : (N : ℝ) / (2 * (U : ℝ) ^ 6) ≤ qPair)
    (hqTriple : (N : ℝ) ^ 2 / (2 * (U : ℝ) ^ 6) ≤ qTriple)
    (hW₂ : W₂ ≤ 512 * U ^ 6 * N ^ (2 * k + 7))
    (hW₃ : W₃ ≤ 768 * U ^ 6 * N ^ (2 * k + 8))
    (hBudget : U ^ 3 * (8 * tPair * qPair) * (16 * tTriple * qPair * qTriple) * loss ≤
      (8 * tPair * qPair) * (16 * tTriple * qPair * qTriple) * (16 * C * m) +
      U ^ 3 * ((8 * tPair * qPair) * W₃ + (16 * tTriple * qPair * qTriple) * W₂)) :
    (loss : ℝ) ≤ 16 * C * ((m : ℝ) / U) + 640 * ((N : ℝ) ^ (k + 5) / U) := by
  have hUp : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hNR : (U : ℝ) ^ 32 ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNR
  have htP : (0 : ℝ) < tPair := lt_of_lt_of_le (by positivity) htPair
  have htT : (0 : ℝ) < tTriple := lt_of_lt_of_le (by positivity) htTriple
  have hqP : (0 : ℝ) < qPair := lt_of_lt_of_le (by positivity) hqPair
  have hqT : (0 : ℝ) < qTriple := lt_of_lt_of_le (by positivity) hqTriple
  have hBudgetR : (U : ℝ) ^ 3 * (8 * tPair * qPair) *
      (16 * tTriple * qPair * qTriple) * loss ≤
      (8 * tPair * qPair) * (16 * tTriple * qPair * qTriple) * (16 * C * m) +
      (U : ℝ) ^ 3 * ((8 * tPair * qPair) * W₃ +
        (16 * tTriple * qPair * qTriple) * W₂) := by exact_mod_cast hBudget
  have hDiv := higher_scaled_repair_budget_divide
    ((U : ℝ) ^ 3) (8 * tPair * qPair) (16 * tTriple * qPair * qTriple)
    loss (16 * C * m) W₂ W₃ (by positivity) (by positivity) (by positivity) hBudgetR
  have hW₂R : (W₂ : ℝ) ≤ 512 * (U : ℝ) ^ 6 * (N : ℝ) ^ (2 * k + 7) := by
    exact_mod_cast hW₂
  have hW₃R : (W₃ : ℝ) ≤ 768 * (U : ℝ) ^ 6 * (N : ℝ) ^ (2 * k + 8) := by
    exact_mod_cast hW₃
  apply le_trans hDiv
  apply le_trans _ (higher_inheritance_scale_envelope N U m C tPair tTriple qPair
    qTriple k (by exact_mod_cast (by omega : 1 ≤ U)) hNR (by positivity)
    (by positivity) htPair htTriple hqPair hqTriple)
  gcongr

/-- The repaired-prefix quadratic error vanishes at rho=U⁻³. -/
theorem higher_prefix_scale_envelope
    (N U : ℝ) (k : ℕ) (hU : 1 ≤ U) (hN : U ^ 32 ≤ N) :
    (4 * (k : ℝ) + 13) * U ^ 2 * N ^ (k + 4) +
      Real.sqrt (N ^ (2 * k + 9) * max 7 (1 + 8 * N / U)) ≤
      (4 * (k : ℝ) + 13) * (N ^ (k + 5) / U) +
        3 * (N ^ (k + 5) / Real.sqrt U) := by
  have hUp : 0 < U := by linarith
  have hNp : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hUPower : U ≤ U ^ 32 := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by omega : 1 ≤ 32)
  have hUN : U ≤ N := hUPower.trans hN
  have hRatio : 1 ≤ N / U := (le_div_iff₀ hUp).2 (by simpa using hUN)
  have hMax : max 7 (1 + 8 * N / U) ≤ 9 * N / U := by
    simp only [mul_div_assoc]
    apply max_le <;> linarith
  have hSqrtPos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUp
  have hRad : N ^ (2 * k + 9) * max 7 (1 + 8 * N / U) ≤
      (3 * (N ^ (k + 5) / Real.sqrt U)) ^ 2 := by
    calc
      _ ≤ N ^ (2 * k + 9) * (9 * N / U) :=
        mul_le_mul_of_nonneg_left hMax (by positivity)
      _ = _ := by
        rw [mul_pow, div_pow, Real.sq_sqrt hUp.le]
        field_simp
        simp only [show 2 * k + 9 = k + k + 9 by omega, pow_add]
        ring
  have hSqrt : Real.sqrt (N ^ (2 * k + 9) * max 7 (1 + 8 * N / U)) ≤
      3 * (N ^ (k + 5) / Real.sqrt U) :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hRad⟩
  have hMono := higher_scale_monomial_bound N U hU hN 2 (k + 4) (by omega)
  have hScaled := mul_le_mul_of_nonneg_left hMono
    (by positivity : 0 ≤ 4 * (k : ℝ) + 13)
  simp only [show k + 4 + 1 = k + 5 by omega] at hScaled
  nlinarith only [hScaled, hSqrt]

end JSP523.Rank5
