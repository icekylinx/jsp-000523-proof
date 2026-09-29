import JSP523.Rank5.ConditionalExtraction
import JSP523.Rank5.FinalExtractionContradiction

namespace JSP523.Rank5

open Filter

theorem eventually_rank_five_degree_gap_excludes_star_mass
    (δ : ℝ) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform 5 (H n))
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    : ∀ᶠ n : ℕ in Filter.atTop,
      ¬ ((M n : ℝ) ≤ (1 - δ) * ((n - 1).choose 4 : ℝ) ∧
        (n - 1).choose 4 ≤ (H n).card) := by
  obtain ⟨α, β, m, hα, hβ, hm, hExtract⟩ :=
    eventually_conditional_initial_polynomial_extraction
      5 9 δ (by omega) hδ H M hAdm hUniform hMax
  let ε : ℝ := 1 / (100000 * (β : ℝ))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hEndpoint := eventually_rank_five_small_structural_error ε hε
  have hError := eventually_rank_five_extraction_error_factor_bound
    H hAdm hUniform (100000 * β) (by omega)
  filter_upwards [hExtract, hEndpoint, hError,
    Filter.eventually_ge_atTop 9]
    with n hExtractN hEndpointN hErrorN hn
  rintro ⟨hDegreeN, hMassN⟩
  obtain ⟨K₀, K, hKK₀, hK₀Out, _hK₀H, hAdmK, hUniformK,
    hCapsK, hMassK, hDiscard, hRoundDiscard, hLedger⟩ := hExtractN hDegreeN hMassN
  let X := initialPolynomialChosenCover 5 H hUniform n
  let W : Edge (Fin n) := Finset.univ \ X
  let B := (n - 1).choose 4
  have hKOut : K ⊆ outsideFamily (H n) W := hKK₀.trans hK₀Out
  have hSupport : ∀ E ∈ K, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp (hKOut hE)).2
  have hShadow : shadowOn K W 5 = fourShadow K :=
    shadow_on_eq_four_shadow_of_supported K W hSupport
  have hCapsK' : ∀ j, 2 ≤ j → j ≤ 4 →
      ∀ S : Edge (Fin n), S.card = j →
      (K.filter fun E => S ⊆ E).card ≤
        discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (4 - j) := by
    intro j hj hj4 S hS
    simpa only [show 5 - j - 1 = 4 - j by omega] using
      hCapsK j (by omega) (by omega) S hS
  have hEndpointK := hEndpointN K hAdmK hUniformK hCapsK'
  have hMassSimple : α * B ≤ (4 * β) * K.card := by
    have hScaled : m * (α * B) ≤ m * ((4 * β) * K.card) := by
      calc
        m * (α * B) = m * α * B := by ring
        _ ≤ 4 * m * β * K.card := by simpa only [B] using hMassK
        _ = m * ((4 * β) * K.card) := by ring
    exact Nat.le_of_mul_le_mul_left hScaled hm
  have hStarPower : n ^ 4 ≤ 384 * B := by
    have h := far_star_power_le_choose_multiple n 4 (by omega)
    norm_num at h
    simpa only [B] using h
  have hBpos : 0 < B := by
    simpa only [B] using Nat.choose_pos (show 4 ≤ n - 1 by omega)
  have hSmall := rank_five_scaled_errors_small α β n B
    (rankFiveExtractionError H hUniform n) hα hβ hBpos
    (by simpa only [B] using hErrorN) hStarPower
  have hLedgerI : ((H n).card : ℤ) - (B : ℤ) ≤
      (K.card : ℤ) - ((shadowOn K W 5).card : ℤ) +
        (((K₀ \ K).card + ((outsideFamily (H n) W \ K₀).card) +
          rankFiveCoverError n X) : ℤ) := by
    simpa only [B, W, X, rankFiveCoverError, Nat.cast_add,
      show 5 - 1 = 4 by omega, show 5 - 2 = 3 by omega,
      show 5 - 3 = 2 by omega, add_assoc] using hLedger
  have hActualError : (K₀ \ K).card +
      (outsideFamily (H n) W \ K₀).card + rankFiveCoverError n X ≤
        rankFiveExtractionError H hUniform n := by
    have hRoundN : (K₀ \ K).card ≤ rankFiveRoundLoss n := by
      simpa only [rankFiveRoundLoss] using hRoundDiscard
    have hCleanupN : (outsideFamily (H n) W \ K₀).card ≤
        rankFiveCleanupCharge H n := by
      simpa only [rankFiveCleanupCharge, W, X] using hDiscard
    dsimp only [rankFiveExtractionError]
    change (K₀ \ K).card +
      (outsideFamily (H n) W \ K₀).card + rankFiveCoverError n X ≤
        rankFiveRoundLoss n + rankFiveCleanupCharge H n + rankFiveCoverError n X
    omega
  have hLedgerR : ((H n).card : ℝ) - (B : ℝ) ≤
      (K.card : ℝ) - ((shadowOn K W 5).card : ℝ) +
        (rankFiveExtractionError H hUniform n : ℝ) := by
    have hCast : ((H n).card : ℝ) - (B : ℝ) ≤
        (K.card : ℝ) - ((shadowOn K W 5).card : ℝ) +
          (((K₀ \ K).card + (outsideFamily (H n) W \ K₀).card +
            rankFiveCoverError n X) : ℝ) := by
      exact_mod_cast hLedgerI
    have hErrorR : (((K₀ \ K).card + (outsideFamily (H n) W \ K₀).card +
        rankFiveCoverError n X) : ℝ) ≤
          (rankFiveExtractionError H hUniform n : ℝ) := by
      exact_mod_cast hActualError
    linarith
  have hMassR : (α : ℝ) * (B : ℝ) ≤
      (4 * (β : ℝ)) * (K.card : ℝ) := by exact_mod_cast hMassSimple
  have hBaselineR : (B : ℝ) ≤ ((H n).card : ℝ) := by
    exact_mod_cast hMassN
  have hEndpointR : 2 * (K.card : ℝ) -
      ((shadowOn K W 5).card : ℝ) ≤
        ε * (n : ℝ) ^ 4 + ε * (K.card : ℝ) := by
    rw [hShadow]
    nlinarith [hEndpointK]
  exact positive_mass_excludes_rank_five_real_endpoint
    (α : ℝ) (4 * (β : ℝ)) (B : ℝ) ((H n).card : ℝ)
    (K.card : ℝ) ((shadowOn K W 5).card : ℝ)
    (rankFiveExtractionError H hUniform n : ℝ)
    (ε * (n : ℝ) ^ 4) ε
    (by positivity) (by positivity) hBaselineR hMassR hLedgerR
    hEndpointR (by
      have hβr : (1 : ℝ) ≤ β := by exact_mod_cast hβ
      have hden : (0 : ℝ) < 100000 * β := by positivity
      dsimp [ε]
      apply (div_le_iff₀ hden).2
      nlinarith)
    (by simpa only [ε, B] using hSmall)

end JSP523.Rank5
