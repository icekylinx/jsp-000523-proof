import JSP523.Rank4.GlobalActualEndToEndParameters

namespace JSP523.Rank4

theorem nonnegative_choose_error_cubic_ratio_tendsto_zero
    (f : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ f n)
    (hChoose : Filter.Tendsto (fun n => f n / (n.choose 3 : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => f n / (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => div_nonneg (hNonneg n) (by positivity))) ?_ hChoose
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with n hn
  have hPos : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
  have hLe : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast Nat.choose_le_pow n 3
  exact div_le_div_of_nonneg_left (hNonneg n) hPos hLe

/-- The actual small remainder: integer sampling, repeated-color deletion,
and actual reciprocal cleanup. -/
noncomputable def endToEndVanishingError
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n)) (level : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  2 * (((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) / (n : ℝ) ^ 3) +
    10 * ((((level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * n ^ 2 : ℕ) : ℝ) / (n : ℝ) ^ 3) +
    10 * (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) / (n : ℝ) ^ 3

theorem end_to_end_vanishing_error_tendsto_zero
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n)) (level : ℕ) (a : ℝ)
    (hCaps : ∀ᶠ n in Filter.atTop,
      (∀ E ∈ (D n).K, E ⊆ (D n).ground) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → ((D n).K.filter fun E => Q ⊆ E).card ≤ level ^ 8) ∧
      (∀ x y, (reciprocalUsedLabelFiber (D n) x y).card ≤ actualUsedCenterCap (level ^ 8) (level ^ 8) a)) :
    Filter.Tendsto (endToEndVanishingError D level a) Filter.atTop (nhds 0) := by
  have hStar := nonnegative_choose_error_cubic_ratio_tendsto_zero _ (fun _ => by positivity)
    star_sampling_error_choose_ratio_tendsto_zero
  have hColor := nonnegative_choose_error_cubic_ratio_tendsto_zero _ (fun _ => by positivity)
    (quadratic_error_choose_ratio_tendsto_zero ((level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2))
  have hRecip := actual_reciprocal_cleanup_ratio_tendsto_zero_of_eventual_caps D _ _ hCaps
  unfold endToEndVanishingError
  simpa only [mul_div_assoc, mul_zero, add_zero] using
    ((hStar.const_mul 2).add (hColor.const_mul 10)).add (hRecip.const_mul 10)

/-- Finite master-error bound with its full fixed-parameter coefficient. -/
theorem ActualEndToEndData.master_error_ratio_bound
    {n level overlap outerLoss : ℕ} {H : Family (Fin n)} {U : Edge (Fin n)} {a : ℝ}
    (A : ActualEndToEndData H U level a overlap outerLoss)
    (D : (m : ℕ) → FiniteCompletionCliqueData (Fin m)) (hD : D n = A.completion)
    (hn : 0 < n) (hLevel : 0 < level) (ha : 0 ≤ a) :
    (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤
      10 * (256 / (level : ℝ) + a) + 4 * (overlap : ℝ) / (n : ℝ) ^ 3 +
        10 * (outerLoss : ℝ) / (n : ℝ) ^ 3 + endToEndVanishingError D level a n := by
  have hN : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hN0 : (n : ℝ) ≠ 0 := by positivity
  have hCleanup := A.cleanup_budget_le_cubic_and_actual_errors hLevel ha
  have hU : U.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ U)
    simpa using h
  have hSampling : U.card ^ 2 * (Nat.sqrt U.card + 1) ≤ n ^ 2 * (Nat.sqrt n + 1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hU 2) (Nat.add_le_add_right (Nat.sqrt_le_sqrt hU) 1)
  have hSamplingReal : ((U.card ^ 2 * (Nat.sqrt U.card + 1) : ℕ) : ℝ) ≤
      ((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) := by exact_mod_cast hSampling
  apply (div_le_iff₀ hN).2
  unfold endToEndVanishingError
  rw [hD]
  have hRight : (10 * (256 / (level : ℝ) + a) + 4 * (overlap : ℝ) / (n : ℝ) ^ 3 +
        10 * (outerLoss : ℝ) / (n : ℝ) ^ 3 +
      (2 * (((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) / (n : ℝ) ^ 3) +
        10 * ((((level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * n ^ 2 : ℕ) : ℝ) / (n : ℝ) ^ 3) +
        10 * ((A.completion.K \ (clearUsedParentThenReciprocal A.completion).K).card : ℝ) / (n : ℝ) ^ 3)) * (n : ℝ) ^ 3 =
      10 * (256 / (level : ℝ) + a) * (n : ℝ) ^ 3 + 4 * overlap + 10 * outerLoss +
        2 * ((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) +
        10 * ((((level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * n ^ 2 : ℕ) : ℝ) +
          ((A.completion.K \ (clearUsedParentThenReciprocal A.completion).K).card : ℝ)) := by
    field_simp
    ring
  rw [hRight]
  unfold ActualEndToEndData.masterError
  push_cast
  push_cast at hCleanup hSamplingReal
  nlinarith

end JSP523.Rank4
