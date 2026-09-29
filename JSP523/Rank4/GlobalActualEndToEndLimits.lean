import JSP523.Rank4.GlobalActualErrorLimits

/-! # Actual cleanup limits with eventual, rather than all-size, caps -/

namespace JSP523.Rank4

/-- Canonical data for the finitely many sizes before preprocessing applies. -/
def emptyCompletionData (n : ℕ) : FiniteCompletionCliqueData (Fin n) where
  ground := ∅
  K := ∅
  uniform_four := by simp [Uniform]
  admissible := by simp [Admissible]
  label := min
  label_symm := min_comm
  label_center := by simp [commonTripleCell]
  no_bicolored_triangle := by simp [graphFacetCompletions]

/-- Caps hold for the harmless initial empty data at every size. -/
theorem empty_completion_data_caps (n d κ : ℕ) :
    (∀ E ∈ (emptyCompletionData n).K, E ⊆ (emptyCompletionData n).ground) ∧
    (∀ T : Edge (Fin n), T.card = 3 → ((emptyCompletionData n).K.filter fun E => T ⊆ E).card ≤ d) ∧
    (∀ x y, (reciprocalUsedLabelFiber (emptyCompletionData n) x y).card ≤ κ) := by
  refine ⟨by simp [emptyCompletionData], by simp [emptyCompletionData], ?_⟩
  intro x y
  unfold reciprocalUsedLabelFiber reciprocalLabelFiber
  exact (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans (by simp [emptyCompletionData]))

/-- Genuine eventual bounds suffice for the reciprocal cleanup limit;
there is no all-size preprocessing hypothesis. -/
theorem actual_reciprocal_cleanup_ratio_tendsto_zero_of_eventual_caps
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n)) (d κ : ℕ)
    (hCaps : ∀ᶠ n in Filter.atTop,
      (∀ E ∈ (D n).K, E ⊆ (D n).ground) ∧
      (∀ T : Edge (Fin n), T.card = 3 → ((D n).K.filter fun E => T ⊆ E).card ≤ d) ∧
      (∀ x y, (reciprocalUsedLabelFiber (D n) x y).card ≤ κ)) :
    Filter.Tendsto (fun n => (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) /
      (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  classical
  let P := fun n => (∀ E ∈ (D n).K, E ⊆ (D n).ground) ∧
    (∀ T : Edge (Fin n), T.card = 3 → ((D n).K.filter fun E => T ⊆ E).card ≤ d) ∧
    (∀ x y, (reciprocalUsedLabelFiber (D n) x y).card ≤ κ)
  let D' := fun n => if P n then D n else emptyCompletionData n
  have hAll : ∀ n, (∀ E ∈ (D' n).K, E ⊆ (D' n).ground) ∧
      (∀ T : Edge (Fin n), T.card = 3 → ((D' n).K.filter fun E => T ⊆ E).card ≤ d) ∧
      (∀ x y, (reciprocalUsedLabelFiber (D' n) x y).card ≤ κ) := by
    intro n
    by_cases hp : P n
    · simpa only [D', ite_eq_left hp] using hp
    · simpa only [D', ite_eq_right hp] using empty_completion_data_caps n d κ
  have hLimit := clear_used_parent_then_reciprocal_loss_ratio_tendsto_zero D' d κ
    (fun n => (hAll n).1) (fun n => (hAll n).2.1) (fun n => (hAll n).2.2)
  apply hLimit.congr'
  filter_upwards [hCaps] with n hn
  change P n at hn
  simp only [D', ite_eq_left hn]

/-- The reciprocal limit also holds in the exact binomial normalization. -/
theorem actual_reciprocal_cleanup_choose_ratio_tendsto_zero_of_eventual_caps
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n)) (d κ : ℕ)
    (hCaps : ∀ᶠ n in Filter.atTop,
      (∀ E ∈ (D n).K, E ⊆ (D n).ground) ∧
      (∀ T : Edge (Fin n), T.card = 3 → ((D n).K.filter fun E => T ⊆ E).card ≤ d) ∧
      (∀ x y, (reciprocalUsedLabelFiber (D n) x y).card ≤ κ)) :
    Filter.Tendsto (fun n => (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) /
      (n.choose 3 : ℝ)) Filter.atTop (nhds 0) :=
  nonnegative_cubic_error_choose_ratio_tendsto_zero _ (fun _ => by positivity)
    (actual_reciprocal_cleanup_ratio_tendsto_zero_of_eventual_caps D d κ hCaps)

end JSP523.Rank4
