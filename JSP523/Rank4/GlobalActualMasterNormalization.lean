import JSP523.Rank4.GlobalActualParameterChoice

/-! # Normalizing the actual master and its surplus -/

namespace JSP523.Rank4

/-- Both the leading estimate and the stability surplus survive exact
binomial normalization of the concrete finite master. -/
theorem actual_master_normalized
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (a : ℝ) (d κ n u h b m overlap outerLoss : ℕ)
    (hn : 3 ≤ n) (hu : u ≤ n)
    (hMaster : 10 * h + b + 6 * m ≤
      10 * u.choose 3 + 2 * (u ^ 2 * (Nat.sqrt u + 1)) + 4 * overlap +
        10 * (outerLoss + (2 * (actualWeakCellThreshold a n - 1) * u.choose 2 +
          d ^ 2 * u ^ 2 * κ ^ 2 +
          ((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card))) :
    (h : ℝ) / (n.choose 3 : ℝ) + ((b : ℝ) + 6 * m) / (10 * (n.choose 3 : ℝ)) ≤
      1 + (outerLoss : ℝ) / (n.choose 3 : ℝ) +
        2 * (overlap : ℝ) / (5 * (n.choose 3 : ℝ)) +
        ((2 * (actualWeakCellThreshold a n - 1) * u.choose 2 : ℕ) : ℝ) /
          (n.choose 3 : ℝ) + actualMasterVanishingRemainder D d κ n := by
  have hChoose : u.choose 3 ≤ n.choose 3 := Nat.choose_le_choose 3 hu
  have hSampling : u ^ 2 * (Nat.sqrt u + 1) ≤ n ^ 2 * (Nat.sqrt n + 1) := by
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hu 2) (Nat.add_le_add_right (Nat.sqrt_le_sqrt hu) 1)
  have hColor : d ^ 2 * u ^ 2 * κ ^ 2 ≤ d ^ 2 * κ ^ 2 * n ^ 2 := by
    calc
      _ = d ^ 2 * κ ^ 2 * u ^ 2 := by ring
      _ ≤ d ^ 2 * κ ^ 2 * n ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu 2)
  have hWhole : 10 * h + b + 6 * m ≤
      10 * n.choose 3 + 2 * (n ^ 2 * (Nat.sqrt n + 1)) + 4 * overlap +
        10 * (outerLoss + (2 * (actualWeakCellThreshold a n - 1) * u.choose 2 +
          d ^ 2 * κ ^ 2 * n ^ 2 +
          ((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card)) := by omega
  have hReal := (show (10 * (h : ℝ) + b + 6 * m) ≤
      10 * (n.choose 3 : ℝ) + 2 * ((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) + 4 * overlap +
        10 * (outerLoss + (((2 * (actualWeakCellThreshold a n - 1) * u.choose 2 : ℕ) : ℝ) +
          ((d ^ 2 * κ ^ 2 * n ^ 2 : ℕ) : ℝ) +
          (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ))) by exact_mod_cast hWhole)
  have hq : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
  have hDiv := div_le_div_of_nonneg_right hReal (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 10) hq))
  unfold actualMasterVanishingRemainder
  convert hDiv using 1 <;> field_simp <;> ring

/-- The concrete fixed-parameter error has coefficient `12 a`; its
remaining part is the actual vanishing remainder, with no chosen `o(1)` term. -/
theorem actual_master_normalized_eventually
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (a : ℝ) (ha : 0 ≤ a) (d κ : ℕ)
    (u h b m overlap outerLoss : ℕ → ℕ)
    (hu : ∀ n, u n ≤ n)
    (hMaster : ∀ᶠ n in Filter.atTop,
      10 * h n + b n + 6 * m n ≤
        10 * (u n).choose 3 + 2 * (u n ^ 2 * (Nat.sqrt (u n) + 1)) + 4 * overlap n +
          10 * (outerLoss n + (2 * (actualWeakCellThreshold a n - 1) * (u n).choose 2 +
            d ^ 2 * u n ^ 2 * κ ^ 2 +
            ((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card))) :
    ∀ᶠ n in Filter.atTop,
      (h n : ℝ) / (n.choose 3 : ℝ) + ((b n : ℝ) + 6 * m n) / (10 * (n.choose 3 : ℝ)) ≤
        1 + (outerLoss n : ℝ) / (n.choose 3 : ℝ) +
          2 * (overlap n : ℝ) / (5 * (n.choose 3 : ℝ)) +
          12 * a + actualMasterVanishingRemainder D d κ n := by
  filter_upwards [hMaster, actual_weak_cell_loss_choose_bound_eventually a ha,
    Filter.eventually_ge_atTop (3 : ℕ)] with n hM hWeak hn
  have hBound := actual_master_normalized D a d κ n (u n) (h n) (b n) (m n)
    (overlap n) (outerLoss n) hn (hu n) hM
  have hW := hWeak (u n) (hu n)
  linarith

end JSP523.Rank4
