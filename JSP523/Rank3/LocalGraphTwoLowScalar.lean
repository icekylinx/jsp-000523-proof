import JSP523.Rank3.LocalGraphScalar

/-!
# Scalar bounds behind the two-low-vertices lemma

§II.A.2 reduces the extremal bipartite graph with two prescribed
low-degree vertices to two explicit rational upper bounds.  This file
checks those upper bounds against the part budgets.  The graph reduction
from arbitrary edges to these expressions remains separate.
-/

namespace JSP523.Rank3

/-- Upper bound when two low-degree vertices lie in the same part. -/
def samePartTwoLowUpper (a b : ℕ) : ℚ :=
  ((a : ℚ) - 2) * localPhi b +
    (b : ℚ) * localPhi (a - 2) +
      6 / ((a : ℚ) * ((a : ℚ) - 1))

/-- The exact rational surplus in the same-part case of §II.A.2. -/
theorem same_part_two_low_surplus_eq
    {a b : ℕ} (ha : 4 ≤ a) (hb : 2 ≤ b) :
    localGraphBudget a + localGraphBudget b -
        samePartTwoLowUpper a b =
      3 * (((a : ℚ) - (b : ℚ) - 2) *
        ((a : ℚ) - (b : ℚ) - 1)) /
        (((a : ℚ) - 1) * ((b : ℚ) + 1)) +
      6 / ((a : ℚ) + 1) -
        6 / ((a : ℚ) * ((a : ℚ) - 1)) := by
  have haTwo : 2 ≤ a := by omega
  have haMinusTwo : 2 ≤ a - 2 := by omega
  rw [local_graph_budget_eq_formula haTwo,
    local_graph_budget_eq_formula hb]
  have hCast : ((a - 2 : ℕ) : ℚ) = (a : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ a)]
    norm_num
  unfold samePartTwoLowUpper
  rw [local_phi_eq_formula hb,
    local_phi_eq_formula haMinusTwo, hCast]
  rw [show (a : ℚ) - 2 + 1 = (a : ℚ) - 1 by ring]
  have haq : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have hbq : (2 : ℚ) ≤ b := by exact_mod_cast hb
  have h₁ : (a : ℚ) - 1 ≠ 0 := by linarith
  have h₂ : (a : ℚ) + 1 ≠ 0 := by linarith
  have h₃ : (a : ℚ) ≠ 0 := by linarith
  have h₄ : (b : ℚ) + 1 ≠ 0 := by linarith
  have hAlt : (-1 : ℚ) + a ≠ 0 := by linarith
  field_simp [h₁, h₂, h₃, h₄, hAlt]
  ring

/-- The consecutive-integer factor in the same-part surplus is
    nonnegative even when `a-b-2` is negative. -/
private theorem consecutive_difference_product_nonneg
    (a b : ℕ) :
    0 ≤ ((a : ℚ) - (b : ℚ) - 2) *
      ((a : ℚ) - (b : ℚ) - 1) := by
  by_cases h : b + 2 ≤ a
  · have haq : (b : ℚ) + 2 ≤ a := by exact_mod_cast h
    have hLeft : (0 : ℚ) ≤ (a : ℚ) - b - 2 := by linarith
    have hRight : (0 : ℚ) ≤ (a : ℚ) - b - 1 := by linarith
    exact mul_nonneg hLeft hRight
  · have hNat : a ≤ b + 1 := by omega
    have haq : (a : ℚ) ≤ b + 1 := by exact_mod_cast hNat
    have hLeft : (a : ℚ) - b - 2 ≤ 0 := by linarith
    have hRight : (a : ℚ) - b - 1 ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos hLeft hRight

/-- The same-part upper bound is within the combined part budgets. -/
theorem same_part_two_low_upper_le_budgets
    {a b : ℕ} (ha : 4 ≤ a) (hb : 2 ≤ b) :
    samePartTwoLowUpper a b ≤
      localGraphBudget a + localGraphBudget b := by
  rw [← sub_nonneg]
  rw [same_part_two_low_surplus_eq ha hb]
  have haq : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have hbq : (2 : ℚ) ≤ b := by exact_mod_cast hb
  have hProd := consecutive_difference_product_nonneg a b
  have hDen : 0 < ((a : ℚ) - 1) * ((b : ℚ) + 1) := by
    apply mul_pos <;> linarith
  have hFirst : 0 ≤
      3 * (((a : ℚ) - b - 2) * ((a : ℚ) - b - 1)) /
        (((a : ℚ) - 1) * ((b : ℚ) + 1)) :=
    div_nonneg (mul_nonneg (by norm_num) hProd) hDen.le
  have hDenA : 0 < (a : ℚ) * ((a : ℚ) - 1) := by
    apply mul_pos <;> linarith
  have hDenPlus : 0 < (a : ℚ) + 1 := by linarith
  have hDenCompare : (a : ℚ) + 1 ≤
      (a : ℚ) * ((a : ℚ) - 1) := by nlinarith
  have hSecond : 6 / ((a : ℚ) * ((a : ℚ) - 1)) ≤
      6 / ((a : ℚ) + 1) :=
    (div_le_div_iff₀ hDenA hDenPlus).mpr (by nlinarith)
  linarith

/-- Upper bound when one low-degree vertex lies in each part. -/
def oppositePartsTwoLowUpper (a b : ℕ) : ℚ :=
  ((a : ℚ) - 1) * localPhi (b - 1) +
    ((b : ℚ) - 1) * localPhi (a - 1) +
      3 / ((a : ℚ) * ((a : ℚ) + 1)) +
        3 / ((b : ℚ) * ((b : ℚ) + 1))

/-- The exact rational surplus in the opposite-parts case. -/
theorem opposite_parts_two_low_surplus_eq
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    localGraphBudget a + localGraphBudget b -
        oppositePartsTwoLowUpper a b =
      3 * (((a : ℚ) - (b : ℚ)) ^ 2 /
        ((a : ℚ) * (b : ℚ)) +
        ((a : ℚ) - 2) / ((a : ℚ) * ((a : ℚ) + 1)) +
        ((b : ℚ) - 2) / ((b : ℚ) * ((b : ℚ) + 1))) := by
  have haTwo : 2 ≤ a := by omega
  have hbTwo : 2 ≤ b := by omega
  have haMinusOne : 2 ≤ a - 1 := by omega
  have hbMinusOne : 2 ≤ b - 1 := by omega
  rw [local_graph_budget_eq_formula haTwo,
    local_graph_budget_eq_formula hbTwo]
  unfold oppositePartsTwoLowUpper
  rw [local_phi_eq_formula hbMinusOne,
    local_phi_eq_formula haMinusOne]
  have hCastA : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    norm_num
  have hCastB : ((b - 1 : ℕ) : ℚ) = (b : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]
    norm_num
  rw [hCastA, hCastB]
  have haq : (3 : ℚ) ≤ a := by exact_mod_cast ha
  have hbq : (3 : ℚ) ≤ b := by exact_mod_cast hb
  have h₁ : (a : ℚ) ≠ 0 := by linarith
  have h₂ : (b : ℚ) ≠ 0 := by linarith
  have h₃ : (a : ℚ) + 1 ≠ 0 := by linarith
  have h₄ : (b : ℚ) + 1 ≠ 0 := by linarith
  field_simp [h₁, h₂, h₃, h₄]
  ring

/-- The opposite-parts upper bound is within the combined part budgets. -/
theorem opposite_parts_two_low_upper_le_budgets
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    oppositePartsTwoLowUpper a b ≤
      localGraphBudget a + localGraphBudget b := by
  rw [← sub_nonneg]
  rw [opposite_parts_two_low_surplus_eq ha hb]
  have haq : (3 : ℚ) ≤ a := by exact_mod_cast ha
  have hbq : (3 : ℚ) ≤ b := by exact_mod_cast hb
  have hAB : 0 < (a : ℚ) * (b : ℚ) := by
    apply mul_pos <;> linarith
  have hA : 0 < (a : ℚ) * ((a : ℚ) + 1) := by
    apply mul_pos <;> linarith
  have hB : 0 < (b : ℚ) * ((b : ℚ) + 1) := by
    apply mul_pos <;> linarith
  have hSquare : 0 ≤ ((a : ℚ) - b) ^ 2 := sq_nonneg _
  have hOne : 0 ≤ ((a : ℚ) - b) ^ 2 /
      ((a : ℚ) * (b : ℚ)) := div_nonneg hSquare hAB.le
  have hTwo : 0 ≤ ((a : ℚ) - 2) /
      ((a : ℚ) * ((a : ℚ) + 1)) :=
    div_nonneg (by linarith) hA.le
  have hThree : 0 ≤ ((b : ℚ) - 2) /
      ((b : ℚ) * ((b : ℚ) + 1)) :=
    div_nonneg (by linarith) hB.le
  linarith

end JSP523.Rank3
