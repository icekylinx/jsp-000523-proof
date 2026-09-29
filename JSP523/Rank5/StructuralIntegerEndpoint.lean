import JSP523.Rank5.FinalParameterError
import JSP523.Rank5.FinalParameterFeasibility

set_option maxHeartbeats 800000

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- All finite parameters are chosen as integer quotients. -/
theorem rank_five_integer_structural_endpoint
    (H : Family α) (V : Edge α) (U : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) (hU : 2 ≤ U) (hn : U ^ 32 ≤ V.card)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ 2)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2) :
    (H.card : ℝ) - (fourShadow H).card ≤ -(H.card : ℝ) +
      3800000 * ((V.card : ℝ) ^ 4 / U) + 1026000 * ((H.card : ℝ) / U) := by
  have hU1 : 1 ≤ U := by omega
  have hUp : 0 < U := by omega
  obtain ⟨hu, ht, hT, hq, hRetention, hqu, hScale⟩ :=
    final_parameter_feasibility V.card U hU hn
  have hSmall (k : ℕ) (hk : k ≤ 32) : U ^ k ≤ V.card :=
    (pow_le_pow_right₀ hU1 hk).trans hn
  have hn1 : 1 ≤ V.card := (Nat.one_le_pow _ _ hU1).trans hn
  have hnSquare : V.card ≤ V.card ^ 2 := by nlinarith
  have htBounds := nat_quotient_real_bounds V.card (U ^ 12)
    (pow_pos hUp _) (hSmall 12 (by omega))
  have hTBounds := nat_quotient_real_bounds (V.card ^ 2) (U ^ 12)
    (pow_pos hUp _) ((hSmall 12 (by omega)).trans hnSquare)
  have huBounds := nat_quotient_real_bounds V.card (U ^ 4)
    (pow_pos hUp _) (hSmall 4 (by omega))
  have hqBounds := nat_quotient_real_bounds V.card (U ^ 8)
    (pow_pos hUp _) (hSmall 8 (by omega))
  push_cast at htBounds hTBounds huBounds hqBounds
  have hD4 : 1 ≤ 4 * U ^ 2 := by
    have := Nat.one_le_pow 2 U hU1
    omega
  have hFinite := rank_five_finite_structural_surplus_bound H V
    16 (U ^ 4) (4 * (V.card / U ^ 8)) (V.card / U ^ 12)
    (V.card ^ 2 / U ^ 12) (V.card / U ^ 4) (V.card / U ^ 8)
    (4 * U ^ 2 * V.card ^ 2) (4 * U ^ 2 * V.card) (4 * U ^ 2)
    (2 / (U : ℝ) ^ 4) hAdm hUniform hAmbient hu ht hT hq
    (pow_pos hUp _) (by omega) hRetention (le_refl _) hqu hScale
    (by positivity) hD4 hD₂ hD₃ hD₄
  have hError := rank_five_structural_error_scale_bound V.card H.card U
    (V.card / U ^ 12) (V.card ^ 2 / U ^ 12) (V.card / U ^ 4) (V.card / U ^ 8)
    hU1 hn (by omega) (by omega) hq htBounds.1 htBounds.2 hTBounds.1 hTBounds.2
    huBounds.1 huBounds.2 hqBounds.1
  linarith

open Filter

omit [DecidableEq α] [Nonempty α] in
/-- The actual nine-round regularization factor supplies all scales and
all ordinary codegree caps for the structural endpoint. -/
theorem eventually_rank_five_structural_endpoint :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform 5 H →
      (∀ j, 2 ≤ j → j ≤ 4 → ∀ S : Edge (Fin n), S.card = j →
        (H.filter fun E => S ⊆ E).card ≤
          discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (4 - j)) →
      (H.card : ℝ) - (fourShadow H).card ≤ -(H.card : ℝ) +
        3800000 * ((n : ℝ) ^ 4 / finalParameterRoot n) +
        1026000 * ((H.card : ℝ) / finalParameterRoot n) := by
  have hLarge := final_parameter_root_tendsto_at_top.eventually (eventually_ge_atTop 2)
  have hRound := (tendsto_discrete_round_iterate_at_top initialPolynomialScale
    initial_polynomial_scale_tendsto_at_top 9).eventually (eventually_ge_atTop 1)
  filter_upwards [hLarge, hRound, eventually_ge_atTop 1] with n hU hR hn
  intro H hAdm hUniform hCaps
  let : Nonempty (Fin n) := ⟨⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 1) hn⟩⟩
  obtain ⟨_, _, hFactor, hPower⟩ := final_parameter_root_bounds n hn hR
  generalize hRoot : finalParameterRoot n = U at hU hFactor hPower ⊢
  generalize hRound : discreteRoundIterate (initialPolynomialScale n) 9 = R at hCaps hFactor
  have hD₂ (S : Edge (Fin n)) (hS : S.card = 2) :
      (H.filter fun E => S ⊆ E).card ≤ 4 * (U) ^ 2 * n ^ 2 := by
    have h := hCaps 2 (by decide) (by decide) S hS
    exact h.trans (Nat.mul_le_mul_right (n ^ 2) hFactor)
  have hD₃ (S : Edge (Fin n)) (hS : S.card = 3) :
      (H.filter fun E => S ⊆ E).card ≤ 4 * (U) ^ 2 * n := by
    have h := hCaps 3 (by decide) (by decide) S hS
    simpa only [Nat.pow_one] using h.trans (Nat.mul_le_mul_right (n ^ 1) hFactor)
  have hD₄ (S : Edge (Fin n)) (hS : S.card = 4) :
      (H.filter fun E => S ⊆ E).card ≤ 4 * (U) ^ 2 := by
    have h := hCaps 4 (by decide) (by decide) S hS
    simpa only [Nat.pow_zero, Nat.mul_one] using h.trans (Nat.mul_le_mul_right (n ^ 0) hFactor)
  simpa only [Finset.card_univ, Fintype.card_fin] using rank_five_integer_structural_endpoint H Finset.univ (U)
    hAdm hUniform (fun E _ => Finset.subset_univ E) hU
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hPower)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hD₂)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hD₃) hD₄

omit [DecidableEq α] [Nonempty α] in
/-- The structural error is arbitrarily small simultaneously relative
to the ambient fourth power and the actual parent mass. -/
theorem eventually_rank_five_small_structural_error
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform 5 H →
      (∀ j, 2 ≤ j → j ≤ 4 → ∀ S : Edge (Fin n), S.card = j →
        (H.filter fun E => S ⊆ E).card ≤
          discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (4 - j)) →
      (H.card : ℝ) - (fourShadow H).card ≤ -(H.card : ℝ) +
        ε * ((n : ℝ) ^ 4 + H.card) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (3800000 / ε)
  have hLarge := final_parameter_root_tendsto_at_top.eventually (eventually_ge_atTop N)
  filter_upwards [eventually_rank_five_structural_endpoint, hLarge,
    final_parameter_root_tendsto_at_top.eventually (eventually_ge_atTop 1)] with n hEnd hU hU1
  intro H hAdm hUniform hCaps
  have h := hEnd H hAdm hUniform hCaps
  generalize hRoot : finalParameterRoot n = U at hU hU1 h
  have hUp : (0 : ℝ) < U := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hU1)
  have hUr : (N : ℝ) ≤ U := by exact_mod_cast hU
  have hCoeff : (3800000 : ℝ) / U ≤ ε := by
    apply (div_le_iff₀ hUp).2
    have hNε := (div_lt_iff₀ hε).1 hN
    nlinarith only [hNε, mul_le_mul_of_nonneg_left hUr (le_of_lt hε)]
  have hCoeff' : (1026000 : ℝ) / U ≤ ε := by
    exact (div_le_div_of_nonneg_right (by norm_num : (1026000 : ℝ) ≤ 3800000)
      (le_of_lt hUp)).trans hCoeff
  have hNterm := mul_le_mul_of_nonneg_right hCoeff (pow_nonneg (Nat.cast_nonneg n) 4)
  have hMterm := mul_le_mul_of_nonneg_right hCoeff' (Nat.cast_nonneg H.card)
  calc
    _ ≤ -(H.card : ℝ) + 3800000 * ((n : ℝ) ^ 4 / U) +
      1026000 * ((H.card : ℝ) / U) := h
    _ = -(H.card : ℝ) + (3800000 / U) * (n : ℝ) ^ 4 +
      (1026000 / U) * H.card := by ring
    _ ≤ _ := by linarith only [hNterm, hMterm]

end JSP523.Rank5
