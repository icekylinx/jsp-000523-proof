import JSP523.Rank5.HigherRankConditionalGlobal
import JSP523.Rank5.HigherRankConditionalGlobalScale
import JSP523.Rank5.HigherRankStructuralScale

/-! # Closed higher-rank structural endpoint and uniform concentration -/

namespace JSP523.Rank5

open Filter

/-- Every actual regularized parent at rank `k+6` has arbitrarily small
mass relative to the ambient scale and its own mass. -/
theorem eventually_higher_rank_small_structural_error_add_six
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform (k + 6) H →
      (∀ j, 2 ≤ j → j ≤ k + 6 - 1 → ∀ S : Edge (Fin n), S.card = j →
        (H.filter fun E => S ⊆ E).card ≤
          discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (k + 6 - j - 1)) →
      (H.card : ℝ) ≤ ε * ((n : ℝ) ^ (k + 6 - 1) + H.card) := by
  have hParams := eventually_higher_rank_scale_parameters
    (2 * fixedPaletteSampleSize (k + 4)) (2 * fixedPaletteSampleSize (k + 3))
  have hError := eventually_higher_rank_scalar_error_bound
    (higherStructuralAmbientConstant k) (higherStructuralMassConstant k) ε hε
  filter_upwards [hParams, hError, eventually_ge_atTop 1] with n hParamsN hErrorN hn
  intro H hAdm hUniform hCaps
  let : Nonempty (Fin n) := ⟨⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 1) hn⟩⟩
  generalize hRoot : finalParameterRoot n = U at hParamsN hErrorN
  obtain ⟨hU, hPower, hFactor, hSamplePair, hSampleTriple⟩ := hParamsN
  have hCap (S : Edge (Fin n)) (hS₂ : 2 ≤ S.card) (hSupper : S.card ≤ k + 5) :
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * n ^ (k + 5 - S.card) := by
    have h := hCaps S.card hS₂ (by omega) S rfl
    have hExp : k + 6 - S.card - 1 = k + 5 - S.card := by omega
    rw [hExp] at h
    exact h.trans (Nat.mul_le_mul_right _ hFactor)
  have hFinite := higher_actual_structural_scale_bound H Finset.univ U k hU
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hPower)
    hAdm hUniform (fun E _ => Finset.subset_univ E)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hSamplePair)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hSampleTriple)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hCap)
  simp only [Finset.card_univ, Fintype.card_fin] at hFinite
  have hSmall := hErrorN ((n : ℝ) ^ (k + 5)) H.card
    (pow_nonneg (Nat.cast_nonneg n) _) (Nat.cast_nonneg H.card)
  have hRewrite :
      (higherStructuralAmbientConstant k : ℝ) * ((n : ℝ) ^ (k + 5) / U) +
        3 * ((n : ℝ) ^ (k + 5) / Real.sqrt U) +
        (higherStructuralMassConstant k : ℝ) * ((H.card : ℝ) / U) =
      (higherStructuralAmbientConstant k : ℝ) * (n : ℝ) ^ (k + 5) / U +
        3 * (n : ℝ) ^ (k + 5) / Real.sqrt U +
        (higherStructuralMassConstant k : ℝ) * H.card / U := by ring
  rw [hRewrite] at hFinite
  simpa only [show k + 6 - 1 = k + 5 by omega] using hFinite.trans hSmall

/-- The actual higher-rank structural theorem with every finite label,
cleanup, repair, prefix, and numerical parameter discharged. -/
theorem eventually_higher_rank_small_structural_error
    (r : ℕ) (hr : 6 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform r H →
      (∀ j, 2 ≤ j → j ≤ r - 1 → ∀ S : Edge (Fin n), S.card = j →
        (H.filter fun E => S ⊆ E).card ≤
          discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (r - j - 1)) →
      (H.card : ℝ) ≤ ε * ((n : ℝ) ^ (r - 1) + H.card) := by
  have hRank : r = (r - 6) + 6 := by omega
  simpa only [← hRank] using
    eventually_higher_rank_small_structural_error_add_six (r - 6) ε hε

/-- Every sufficiently large star-sized admissible family at every
fixed rank at least six has a vertex carrying almost a full star. -/
theorem eventually_uniform_higher_rank_degree_concentration
    (r : ℕ) (hr : 6 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin n),
      Admissible F → Uniform r F → (n - 1).choose (r - 1) ≤ F.card →
      ∃ z : Fin n, (1 - δ) * ((n - 1).choose (r - 1) : ℝ) <
        ((F.filter fun E => z ∈ E).card : ℝ) := by
  exact higher_rank_uniform_concentration_of_structural_endpoint r δ hr hδ
    (eventually_higher_rank_small_structural_error r hr)

/-- Unified degree concentration at every fixed rank at least five. -/
theorem eventually_uniform_rank_at_least_five_degree_concentration
    (r : ℕ) (hr : 5 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin n),
      Admissible F → Uniform r F → (n - 1).choose (r - 1) ≤ F.card →
      ∃ z : Fin n, (1 - δ) * ((n - 1).choose (r - 1) : ℝ) <
        ((F.filter fun E => z ∈ E).card : ℝ) := by
  by_cases hFive : r = 5
  · subst r
    exact eventually_uniform_rank_five_degree_concentration δ hδ
  · exact eventually_uniform_higher_rank_degree_concentration r (by omega) δ hδ

end JSP523.Rank5
