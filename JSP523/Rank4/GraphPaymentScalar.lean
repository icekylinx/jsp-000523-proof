import Mathlib.Tactic

/-!
# Scalar payments in the rank-four graph deficit lemma

The slot slack and record-loss functions are those of (III.B.9)–(III.B.11)
in the all-rank manuscript. These finite inequalities are summed
over selected pair-link slots; the graph and record-counting interfaces are
not assumed here.
-/

namespace JSP523.Rank4

/-- Nonnegative slack attached to an eligible slot of a facet of degree
`d`, with selected pair-link degree `k`. -/
def slotSlack (d k : ℕ) : ℚ :=
  if k = 0 then ((d : ℚ) - 1 / 2) * ((d : ℚ) - 2)
  else ((d : ℚ) - k) * ((d : ℚ) + k - 5 / 2)

/-- At most one rainbow record is lost if a degree-three colored slot is
not fully selected. -/
def rainbowRecordLoss (k : ℕ) : ℕ := if k < 3 then 1 else 0

/-- At most two disjoint proper-`K₄` records are lost at a degree-four
colored slot. -/
def properFourRecordLoss (k : ℕ) : ℕ := min 2 (4 - k)

theorem slotSlack_three_nonneg (k : ℕ) (hk : k ≤ 3) :
    0 ≤ slotSlack 3 k := by
  interval_cases k <;> norm_num [slotSlack] at *

theorem slotSlack_four_nonneg (k : ℕ) (hk : k ≤ 4) :
    0 ≤ slotSlack 4 k := by
  interval_cases k <;> norm_num [slotSlack] at *

/-- The degree-three colored-slot payment in equation (III.B.11). -/
theorem rainbow_slot_payment (k : ℕ) (hk : k ≤ 3) :
    (1 / 2 : ℚ) * slotSlack 3 k +
        (if k = 3 then 1 / 2 else 0) -
        (1 / 2) * rainbowRecordLoss k ≥ 1 / 2 := by
  interval_cases k <;> norm_num [slotSlack, rainbowRecordLoss] at *

/-- The degree-four colored-slot payment in equation (III.B.11). -/
theorem proper_four_slot_payment (k : ℕ) (hk : k ≤ 4) :
    (1 / 2 : ℚ) * slotSlack 4 k +
        (if k = 4 then 1 else 0) -
        (1 / 2) * properFourRecordLoss k ≥ 1 := by
  interval_cases k <;> norm_num [slotSlack, properFourRecordLoss] at *

/-- Simplified per-edge slack after the retained-link occurrence count is
substituted into §III.B.3's definition of `z_E`. -/
def edgeSlack (h c l : ℕ) : ℤ :=
  6 - h - (h.choose 2 : ℤ) + c + l

theorem edgeSlack_nonneg
    (h c l : ℕ) (hh : h ≤ 4)
    (hFull : h = 4 → c + l = 4) :
    0 ≤ edgeSlack h c l := by
  interval_cases h <;> norm_num [edgeSlack, Nat.choose] at * <;> omega

theorem edgeSlack_full (c l : ℕ) (hcl : c + l = 4) :
    edgeSlack 4 c l = 0 := by
  norm_num [edgeSlack, Nat.choose]
  omega

theorem edgeSlack_all_private : edgeSlack 0 0 0 = 6 := by
  norm_num [edgeSlack, Nat.choose]

/-- The manuscript's original `z_E` formula equals the simplified slack
whenever the private-row and selected-link occurrence counts hold. -/
theorem original_edge_slack_eq
    (h p c l t k : ℕ)
    (hp : h + p = 4)
    (hk : k + l = h.choose 2 + t) :
    (2 : ℤ) + c - k + p + t = edgeSlack h c l := by
  have hpz : (h : ℤ) + p = 4 := by exact_mod_cast hp
  have hkz : (k : ℤ) + l = (h.choose 2 : ℤ) + t := by
    exact_mod_cast hk
  unfold edgeSlack
  omega

/-- The degree-three marked-vertex contribution on a nonleaf edge. -/
theorem marked_three_nonleaf_payment (k : ℕ) (hk : 2 ≤ k) :
    (1 / 4 : ℚ) ≤ (k : ℚ) / 4 + 3 / (2 * k) - 1 := by
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℚ) < k := by linarith
  have hpoly : 0 ≤ ((k : ℚ) - 2) * ((k : ℚ) - 3) := by
    rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with h | h | h
    · subst k; norm_num
    · subst k; norm_num
    · have hk4 : (4 : ℚ) ≤ k := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hEq : (k : ℚ) / 4 + 3 / (2 * k) - 1 - 1 / 4 =
      (((k : ℚ) - 2) * ((k : ℚ) - 3)) / (4 * k) := by
    field_simp
    ring
  rw [← sub_nonneg, hEq]
  exact div_nonneg hpoly (by positivity)

/-- The degree-four marked-vertex contribution on a nonleaf edge. -/
theorem marked_four_nonleaf_payment (k : ℕ) (hk : 2 ≤ k) :
    (3 / 8 : ℚ) ≤ (k : ℚ) / 4 + 4 / (2 * k) - 1 := by
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℚ) < k := by linarith
  have hpoly : 0 ≤ 2 * ((k : ℚ) - 11 / 4) ^ 2 + 7 / 8 := by positivity
  have hEq : (k : ℚ) / 4 + 4 / (2 * k) - 1 - 3 / 8 =
      (2 * ((k : ℚ) - 11 / 4) ^ 2 + 7 / 8) / (8 * k) := by
    field_simp
    ring
  rw [← sub_nonneg, hEq]
  exact div_nonneg hpoly (by positivity)

/-- An edge's nonnegative degree-ratio term pays the correction at its
leaf endpoints.  This is the remaining scalar inequality in equation (III.B.6). -/
theorem edge_ratio_pays_leaf_correction
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (if d = 1 then (k : ℚ) - 1 else 0) +
      (if k = 1 then (d : ℚ) - 1 else 0) ≤
      2 * ((d : ℚ) / k + (k : ℚ) / d - 2) := by
  have hdpos : (0 : ℚ) < d := by
    have : (1 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  have hkpos : (0 : ℚ) < k := by
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  rcases (by omega : d = 1 ∨ 2 ≤ d) with hd1 | hd2 <;>
    rcases (by omega : k = 1 ∨ 2 ≤ k) with hk1 | hk2
  · subst d; subst k; norm_num
  · subst d
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk2
    have hpoly : 0 ≤ ((k : ℚ) - 1) * ((k : ℚ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    have hEq : 2 * ((k : ℚ)⁻¹ + k - 2) + 1 - k =
        (((k : ℚ) - 1) * ((k : ℚ) - 2)) / k := by
      field_simp
      ring
    simp [show k ≠ 1 by omega]
    rw [← sub_nonneg, hEq]
    exact div_nonneg hpoly hkpos.le
  · subst k
    have hdq : (2 : ℚ) ≤ d := by exact_mod_cast hd2
    have hpoly : 0 ≤ ((d : ℚ) - 1) * ((d : ℚ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    have hEq : 2 * ((d : ℚ) + (d : ℚ)⁻¹ - 2) + 1 - d =
        (((d : ℚ) - 1) * ((d : ℚ) - 2)) / d := by
      field_simp
      ring
    simp [show d ≠ 1 by omega]
    rw [← sub_nonneg, hEq]
    exact div_nonneg hpoly hdpos.le
  · have hsq : 0 ≤ ((d : ℚ) - k) ^ 2 := sq_nonneg _
    have hEq : (d : ℚ) / k + (k : ℚ) / d - 2 =
        ((d : ℚ) - k) ^ 2 / ((d : ℚ) * k) := by
      field_simp
      ring
    simp [show d ≠ 1 by omega, show k ≠ 1 by omega]
    rw [← sub_nonneg, hEq]
    exact div_nonneg hsq (mul_pos hdpos hkpos).le

/-- Degree-three marked vertices receive one quarter from a leaf edge
after the leaf correction is deducted. -/
theorem marked_three_leaf_payment :
    (1 / 4 : ℚ) =
      1 / 12 + (1 / 2) * (3 / 1 + 1 / 3 - 2) -
        (3 - 1) / 4 := by
  norm_num

/-- Degree-four marked vertices receive one half from a leaf edge. -/
theorem marked_four_leaf_payment :
    (1 / 2 : ℚ) =
      1 / 8 + (1 / 2) * (4 / 1 + 1 / 4 - 2) -
        (4 - 1) / 4 := by
  norm_num

/-- On an edge joining two marked vertices, each endpoint's own local
deficit contribution suffices; the ratio term can be discarded. -/
theorem marked_three_neighbor_payment
    (k : ℕ) (hk : 3 ≤ k) :
    (1 / 4 : ℚ) ≤ (k : ℚ) / 12 := by
  have hkq : (3 : ℚ) ≤ k := by exact_mod_cast hk
  linarith

theorem marked_four_neighbor_payment
    (k : ℕ) (hk : 3 ≤ k) :
    (3 / 8 : ℚ) ≤ (k : ℚ) / 8 := by
  have hkq : (3 : ℚ) ≤ k := by exact_mod_cast hk
  linarith

/-- Fourfold version of the per-edge allocation, in the normalization of
the exact graph identity.  A leaf correction is deducted when `k = 1`. -/
theorem marked_three_edge_charge
    (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) ≤ (k : ℚ) / 3 +
      2 * (3 / k + (k : ℚ) / 3 - 2) -
      (if k = 1 then 2 else 0) := by
  by_cases hk1 : k = 1
  · subst k; norm_num
  · have hk2 : 2 ≤ k := by omega
    have hBase := marked_three_nonleaf_payment k hk2
    have hEq : (k : ℚ) / 3 +
        2 * (3 / k + (k : ℚ) / 3 - 2) =
        4 * ((k : ℚ) / 4 + 3 / (2 * k) - 1) := by
      have hkq : (0 : ℚ) < k := by
        have : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
      field_simp
      ring
    simp [hk1, hEq]
    linarith

theorem marked_four_edge_charge
    (k : ℕ) (hk : 1 ≤ k) :
    (3 / 2 : ℚ) ≤ (k : ℚ) / 2 +
      2 * (4 / k + (k : ℚ) / 4 - 2) -
      (if k = 1 then 3 else 0) := by
  by_cases hk1 : k = 1
  · subst k; norm_num
  · have hk2 : 2 ≤ k := by omega
    have hBase := marked_four_nonleaf_payment k hk2
    have hEq : (k : ℚ) / 2 +
        2 * (4 / k + (k : ℚ) / 4 - 2) =
        4 * ((k : ℚ) / 4 + 4 / (2 * k) - 1) := by
      have hkq : (0 : ℚ) < k := by
        have : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
      field_simp
      ring
    simp [hk1, hEq]
    linarith

end JSP523.Rank4
