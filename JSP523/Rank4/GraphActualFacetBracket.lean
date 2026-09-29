import JSP523.Rank4.GraphPaymentScalar

/-!
# The exact facet-slot bracket in (III.B.9)

The zero-degree case of `slotSlack` contributes one unit.  Combining it
with the positive-slot indicator removes that case distinction, leaving
the polynomial bracket used for private, monochromatic, and colored facets.
-/

namespace JSP523.Rank4

/-- The manuscript's slot slack is nonnegative for every eligible
facet degree and every possible selected degree. -/
theorem slot_slack_nonneg_of_nonprivate
    (d k : ℕ) (hd : 2 ≤ d) (hk : k ≤ d) :
    0 ≤ slotSlack d k := by
  have hdq : (2 : ℚ) ≤ d := by exact_mod_cast hd
  by_cases hZero : k = 0
  · subst k
    unfold slotSlack
    simp only [↓reduceIte]
    apply mul_nonneg <;> linarith
  · have hkq : (k : ℚ) ≤ d := by exact_mod_cast hk
    have hkpos : (1 : ℚ) ≤ k := by
      exact_mod_cast (by omega : 1 ≤ k)
    unfold slotSlack
    simp only [hZero, ↓reduceIte]
    apply mul_nonneg <;> linarith

/-- One eligible slot's squared-degree and positive-slot terms are
exactly its slack plus a linear expression in the full and selected
degrees. -/
theorem slot_square_indicator_slack_identity (d k : ℕ) :
    (k : ℚ) ^ 2 + (if 0 < k then 1 else 0) + slotSlack d k =
      (d : ℚ) ^ 2 - (5 / 2) * d + (5 / 2) * k + 1 := by
  by_cases hk : k = 0
  · subst k
    norm_num [slotSlack]
    ring
  · have hkpos : 0 < k := by omega
    simp only [hkpos, ↓reduceIte, slotSlack, hk]
    ring

/-- Summed (III.B.9) facet bracket for any finite set of eligible
slots.  The chosen slot degrees need no further combinatorial premise. -/
theorem facet_slot_bracket_identity
    {ι : Type*} (S : Finset ι) (d : ℕ) (k : ι → ℕ) :
    2 * (d : ℚ) ^ 2 -
      ∑ x ∈ S, ((k x : ℚ) ^ 2 +
        (if 0 < k x then 1 else 0)) =
      (2 - (S.card : ℚ)) * (d : ℚ) ^ 2 +
        (5 / 2) * (S.card : ℚ) * d - (S.card : ℚ) -
        (5 / 2) * (∑ x ∈ S, (k x : ℚ)) +
        ∑ x ∈ S, slotSlack d (k x) := by
  classical
  have hPoint :
      (∑ x ∈ S, ((k x : ℚ) ^ 2 +
        (if 0 < k x then 1 else 0) + slotSlack d (k x))) =
      ∑ x ∈ S, ((d : ℚ) ^ 2 - (5 / 2) * d +
        (5 / 2) * k x + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    exact slot_square_indicator_slack_identity d (k x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at hPoint
  rw [Finset.sum_add_distrib]
  ring_nf at hPoint ⊢
  linarith

/-- A private degree-one facet has bracket two and no eligible slot. -/
theorem private_facet_slot_bracket_identity :
    2 * (1 : ℚ) ^ 2 = 2 := by norm_num

/-- A monochromatic facet has exactly two eligible slots. -/
theorem monochromatic_facet_slot_bracket_identity
    {ι : Type*} (S : Finset ι) (d : ℕ) (k : ι → ℕ)
    (hS : S.card = 2) :
    2 * (d : ℚ) ^ 2 -
      ∑ x ∈ S, ((k x : ℚ) ^ 2 +
        (if 0 < k x then 1 else 0)) =
      5 * (d : ℚ) - 2 -
        (5 / 2) * (∑ x ∈ S, (k x : ℚ)) +
        ∑ x ∈ S, slotSlack d (k x) := by
  rw [facet_slot_bracket_identity]
  simp [hS]

/-- A colored facet has exactly three eligible slots. -/
theorem colored_facet_slot_bracket_identity
    {ι : Type*} (S : Finset ι) (d : ℕ) (k : ι → ℕ)
    (hS : S.card = 3) :
    2 * (d : ℚ) ^ 2 -
      ∑ x ∈ S, ((k x : ℚ) ^ 2 +
        (if 0 < k x then 1 else 0)) =
      -(d : ℚ) ^ 2 + (15 / 2) * d - 3 -
        (5 / 2) * (∑ x ∈ S, (k x : ℚ)) +
        ∑ x ∈ S, slotSlack d (k x) := by
  rw [facet_slot_bracket_identity]
  simp [hS]
  ring

end JSP523.Rank4
