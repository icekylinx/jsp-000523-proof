import JSP523.Rank4.GlobalActualErrorLimits

/-! # Explicit weak-cell threshold and center-degree parameters -/

namespace JSP523.Rank4

/-- A positive integer threshold with the same deletion bound as
ceiling `α n`, including integer boundary values. -/
noncomputable def actualWeakCellThreshold (a : ℝ) (n : ℕ) : ℕ :=
  ⌊a * n⌋₊ + 1

/-- A fixed center-graph cap for a linear original pair-degree bound. -/
noncomputable def actualUsedCenterCap (d L : ℕ) (a : ℝ) : ℕ :=
  ⌈(((d - 1) * L : ℕ) : ℝ) / a⌉₊

theorem actual_weak_cell_threshold_pos (a : ℝ) (n : ℕ) :
    0 < actualWeakCellThreshold a n := by
  unfold actualWeakCellThreshold
  omega

/-- The center-degree scale inequality follows from the explicit ceiling
choice, rather than being a separate asymptotic hypothesis. -/
theorem actual_used_center_cap_scale (d L n : ℕ) (a : ℝ) (ha : 0 < a) :
    (d - 1) * (L * n) ≤ actualWeakCellThreshold a n * actualUsedCenterCap d L a := by
  have hCeil := Nat.le_ceil ((((d - 1) * L : ℕ) : ℝ) / a)
  have hCap : (((d - 1) * L : ℕ) : ℝ) ≤ a * (actualUsedCenterCap d L a : ℝ) := by
    unfold actualUsedCenterCap
    exact (div_le_iff₀ ha).1 hCeil |>.trans_eq (mul_comm _ _)
  have hFloor := (Nat.lt_floor_add_one (a * (n : ℝ))).le
  have hThreshold : a * (n : ℝ) ≤ (actualWeakCellThreshold a n : ℝ) := by
    simpa [actualWeakCellThreshold] using hFloor
  have h1 := mul_le_mul_of_nonneg_right hCap (Nat.cast_nonneg n)
  have h2 := mul_le_mul_of_nonneg_right hThreshold (Nat.cast_nonneg (actualUsedCenterCap d L a))
  have hReal : (((d - 1) * (L * n) : ℕ) : ℝ) ≤
      ((actualWeakCellThreshold a n * actualUsedCenterCap d L a : ℕ) : ℝ) := by
    push_cast at h1 ⊢
    nlinarith
  exact_mod_cast hReal

/-- The threshold eventually exceeds the fixed large-cell constant. -/
theorem actual_weak_cell_threshold_eventually_large (d : ℕ) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop, 9 * d < actualWeakCellThreshold a n := by
  filter_upwards [Filter.eventually_ge_atTop (⌈(9 * (d : ℝ) + 1) / a⌉₊ : ℕ)] with n hn
  have hLower : (9 * (d : ℝ) + 1) / a ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hMul := (div_le_iff₀ ha).1 hLower
  have hFloor := Nat.lt_floor_add_one (a * (n : ℝ))
  have hReal : ((9 * d : ℕ) : ℝ) < (actualWeakCellThreshold a n : ℝ) := by
    simp only [actualWeakCellThreshold, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  exact_mod_cast hReal

/-- The exact weak-cell deletion cost has cubic coefficient at most a. -/
theorem actual_weak_cell_loss_le_cubic (a : ℝ) (ha : 0 ≤ a)
    (u n : ℕ) (hu : u ≤ n) :
    ((2 * (actualWeakCellThreshold a n - 1) * u.choose 2 : ℕ) : ℝ) ≤ a * (n : ℝ) ^ 3 := by
  have hFloor : ((actualWeakCellThreshold a n - 1 : ℕ) : ℝ) ≤ a * (n : ℝ) := by
    simpa [actualWeakCellThreshold] using (Nat.floor_le (by positivity : 0 ≤ a * (n : ℝ)))
  have hChoose : (u.choose 2 : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast Nat.choose_le_choose 2 hu
  have hTwo : 2 * (u.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hNC : 2 * (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [Nat.cast_choose_two]
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    linarith
  have hBound := mul_le_mul hFloor hTwo (by positivity) (by positivity : 0 ≤ a * (n : ℝ))
  push_cast
  nlinarith [hBound]

/-- The weak-cell cost is at most `12 a` in the exact binomial
normalization, uniformly for every smaller ground set. -/
theorem actual_weak_cell_loss_choose_bound_eventually (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ u ≤ n,
      ((2 * (actualWeakCellThreshold a n - 1) * u.choose 2 : ℕ) : ℝ) /
        (n.choose 3 : ℝ) ≤ 12 * a := by
  filter_upwards [cubic_le_twelve_choose_eventually, Filter.eventually_ge_atTop (3 : ℕ)] with n hCube hn u hu
  have hChoose : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
  apply (div_le_iff₀ hChoose).2
  have hWeak := actual_weak_cell_loss_le_cubic a ha u n hu
  have hScale := mul_le_mul_of_nonneg_left hCube ha
  nlinarith

end JSP523.Rank4
