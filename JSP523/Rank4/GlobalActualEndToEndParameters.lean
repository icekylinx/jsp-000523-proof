import JSP523.Rank4.GlobalActualEndToEndData

/-! # Fixed parameter choices and actual finite cleanup budgets -/

namespace JSP523.Rank4

noncomputable def endToEndLevel (ε : ℝ) : ℕ := max 256 ⌈10240 / ε⌉₊
noncomputable def endToEndWeakCoefficient (ε : ℝ) : ℝ := ε / 40

theorem end_to_end_parameter_bounds (ε : ℝ) (hε : 0 < ε) :
    256 ≤ endToEndLevel ε ∧ 0 < endToEndWeakCoefficient ε ∧
      256 / (endToEndLevel ε : ℝ) + endToEndWeakCoefficient ε ≤ ε / 20 := by
  have hL : 256 ≤ endToEndLevel ε := Nat.le_max_left _ _
  have hLPos : (0 : ℝ) < endToEndLevel ε := by exact_mod_cast (by omega : 0 < endToEndLevel ε)
  have hScale : 10240 ≤ ε * (endToEndLevel ε : ℝ) := by
    have h : 10240 / ε ≤ (endToEndLevel ε : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_max_right 256 ⌈10240 / ε⌉₊))
    have hh := (div_le_iff₀ hε).1 h
    linarith
  refine ⟨hL, by dsimp [endToEndWeakCoefficient]; positivity, ?_⟩
  have hReg : 256 / (endToEndLevel ε : ℝ) ≤ ε / 40 := by
    apply (div_le_iff₀ hLPos).2
    linarith
  dsimp [endToEndWeakCoefficient]
  linarith

namespace ActualEndToEndData

variable {n level overlap outerLoss : ℕ} {H : Family (Fin n)} {U : Edge (Fin n)} {a : ℝ}

/-- The exact scalar used by both the cleanup bound and the finite master. -/
noncomputable def cleanupBudget (A : ActualEndToEndData H U level a overlap outerLoss) : ℕ :=
  (fixedDecompositionCore H U \ A.regularized).card +
    (2 * (actualWeakCellThreshold a n - 1) * U.card.choose 2 +
      (level ^ 8) ^ 2 * U.card ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 +
      (A.completion.K \ (clearUsedParentThenReciprocal A.completion).K).card)

noncomputable def masterError (A : ActualEndToEndData H U level a overlap outerLoss) : ℕ :=
  2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) + 4 * overlap + 10 * (outerLoss + A.cleanupBudget)

/-- The recorded master uses exactly this error, with the actual final core. -/
theorem master_with_error (A : ActualEndToEndData H U level a overlap outerLoss) :
    10 * H.card + (rankFourNonprivateFacets (clearUsedParentThenReciprocal A.completion).K U).card +
      6 * (rankFourAllPrivateEdges (clearUsedParentThenReciprocal A.completion).K U).card ≤
    10 * U.card.choose 3 + A.masterError := by
  have h := A.master
  unfold masterError cleanupBudget
  omega

/-- The finite regularization and weak-cell losses contribute `256/level+a`;
all other terms are actual quadratic or reciprocal errors. -/
theorem cleanup_budget_le_cubic_and_actual_errors
    (A : ActualEndToEndData H U level a overlap outerLoss) (hLevel : 0 < level) (ha : 0 ≤ a) :
    (A.cleanupBudget : ℝ) ≤ (256 / (level : ℝ) + a) * (n : ℝ) ^ 3 +
      (((level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * n ^ 2 : ℕ) : ℝ) +
      ((A.completion.K \ (clearUsedParentThenReciprocal A.completion).K).card : ℝ) := by
  have hU : U.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ U)
    simpa using h
  have hLPos : (0 : ℝ) < level := by exact_mod_cast hLevel
  have hReg : ((fixedDecompositionCore H U \ A.regularized).card : ℝ) ≤
      (256 / (level : ℝ)) * (n : ℝ) ^ 3 := by
    have hReal : ((fixedDecompositionCore H U \ A.regularized).card : ℝ) * (level : ℝ) ≤
        256 * (n : ℝ) ^ 3 := by
      have h := A.regularized_loss
      rw [mul_comm] at h
      exact_mod_cast h
    convert (le_div_iff₀ hLPos).2 hReal using 1
    ring
  have hWeak := actual_weak_cell_loss_le_cubic a ha U.card n hU
  have hColor : (level ^ 8) ^ 2 * U.card ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 ≤
      (level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * n ^ 2 := by
    calc
      _ = (level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * U.card ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU 2)
  have hColorReal :
      (( (level ^ 8) ^ 2 * U.card ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 : ℕ) : ℝ) ≤
      (((level ^ 8) ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hColor
  unfold cleanupBudget
  push_cast
  push_cast at hWeak hColorReal
  nlinarith

/-- The same fixed parameters control the actual deletion from the original core. -/
theorem parent_cleanup_le_budget (A : ActualEndToEndData H U level a overlap outerLoss) :
    (fixedDecompositionCore H U \ (clearUsedParentThenReciprocal A.completion).K).card ≤ A.cleanupBudget :=
  A.cleanup_bound

/-- One error ledger controls the actual parent cleanup and the outer loss. -/
theorem parent_cleanup_and_outer_le_master_error
    (A : ActualEndToEndData H U level a overlap outerLoss) :
    10 * ((fixedDecompositionCore H U \ (clearUsedParentThenReciprocal A.completion).K).card + outerLoss) ≤
      A.masterError := by
  have h := A.parent_cleanup_le_budget
  unfold masterError
  omega

end ActualEndToEndData

end JSP523.Rank4
