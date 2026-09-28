import JSP523.Rank3.ExactSupportLedger
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Scalar algebra for rank-three signed weights

The graph-dependent weight formula is built from one monotone fraction
`f(d) = (d-3)_+ / d` and a pair budget `b(d)/d`.  This file proves their
pointwise relation and the integer-degree base-weight bound used before
the nonnegative deficit is subtracted.
-/

namespace JSP523.Rank3

/-- The normalized excess of a common-neighbor count. -/
def weightFraction (d : ℕ) : ℚ :=
  if d ≤ 3 then 0 else ((d : ℚ) - 3) / (d : ℚ)

/-- The pair budget per incident rooted triple. -/
def weightPairBudget (d : ℕ) : ℚ :=
  if d = 0 then 0 else pairBudget d / (d : ℚ)

/-- The degree-only term in the deficit form of a signed edge weight. -/
def baseWeight (d e : ℕ) : ℚ :=
  weightFraction d + weightFraction e -
    ((d : ℚ) - (e : ℚ)) * (weightFraction d - weightFraction e)

theorem weight_fraction_nonneg (d : ℕ) : 0 ≤ weightFraction d := by
  by_cases hsmall : d ≤ 3
  · simp [weightFraction, hsmall]
  · have hd : 4 ≤ d := by omega
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnum : (0 : ℚ) ≤ (d : ℚ) - 3 := by
      have : (4 : ℚ) ≤ d := by exact_mod_cast hd
      linarith
    simp only [weightFraction, ite_eq_right hsmall]
    exact div_nonneg hnum hdpos.le

theorem weight_fraction_lt_one (d : ℕ) : weightFraction d < 1 := by
  by_cases hsmall : d ≤ 3
  · simp [weightFraction, hsmall]
  · have hd : 4 ≤ d := by omega
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    simp only [weightFraction, ite_eq_right hsmall]
    apply (div_lt_iff₀ hdpos).mpr
    linarith

theorem weight_fraction_eq_zero_of_le_three
    {d : ℕ} (hd : d ≤ 3) : weightFraction d = 0 := by
  simp [weightFraction, hd]

/-- Multiplying by the number of common neighbors removes the normalized
    fraction and gives the common-link surplus. -/
theorem card_mul_weight_fraction_eq_link_surplus (d : ℕ) :
    (d : ℚ) * weightFraction d = linkSurplus d := by
  by_cases hsmall : d ≤ 3
  · have hsurplus : ¬ 3 < d := by omega
    simp [weightFraction, linkSurplus, hsmall, hsurplus]
  · have hlarge : 3 < d := by omega
    have hdne : (d : ℚ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp only [weightFraction, ite_eq_right hsmall,
      linkSurplus, ite_eq_left hlarge]
    field_simp

/-- Larger integer degrees have no smaller normalized excess. -/
theorem weight_fraction_mono {d e : ℕ} (hde : d ≤ e) :
    weightFraction d ≤ weightFraction e := by
  by_cases hdsmall : d ≤ 3
  · rw [weight_fraction_eq_zero_of_le_three hdsmall]
    exact weight_fraction_nonneg e
  · have hesmall : ¬ e ≤ 3 := by omega
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    have hepos : (0 : ℚ) < e := by exact_mod_cast (by omega : 0 < e)
    have hcast : (d : ℚ) ≤ (e : ℚ) := by exact_mod_cast hde
    simp only [weightFraction, ite_eq_right hdsmall,
      ite_eq_right hesmall]
    apply (div_le_div_iff₀ hdpos hepos).mpr
    nlinarith

/-- The budget `b(d)/d` equals `(d-2)f(d)` for every positive degree,
    with the low-degree branches both zero. -/
theorem weight_pair_budget_eq (d : ℕ) :
    weightPairBudget d = ((d : ℚ) - 2) * weightFraction d := by
  by_cases hd0 : d = 0
  · subst d; norm_num [weightPairBudget, weightFraction]
  by_cases hsmall : d ≤ 3
  · have hcases : d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hcases with h | h | h
    · subst d; norm_num [weightPairBudget, pairBudget, weightFraction]
    · subst d; norm_num [weightPairBudget, pairBudget, weightFraction]
    · subst d; norm_num [weightPairBudget, pairBudget, weightFraction]
  · have hd : 4 ≤ d := by omega
    have hdq : (d : ℚ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp [weightPairBudget, pairBudget, weightFraction, hd, hsmall, hd0]
    rw [mul_div_assoc]

/-- Multiplying the per-triple pair budget by the completion degree gives
    the original pair budget. -/
theorem card_mul_weight_pair_budget_eq_pair_budget (d : ℕ) :
    (d : ℚ) * weightPairBudget d = pairBudget d := by
  by_cases hd0 : d = 0
  · subst d
    norm_num [weightPairBudget, pairBudget]
  · have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    simp only [weightPairBudget, ite_eq_right hd0]
    field_simp

theorem base_weight_comm (d e : ℕ) : baseWeight d e = baseWeight e d := by
  unfold baseWeight
  ring

private theorem base_weight_le_twice_left
    {d e : ℕ} (hde : d ≤ e) :
    baseWeight d e ≤ 2 * weightFraction d := by
  by_cases heq : d = e
  · subst e
    unfold baseWeight
    nlinarith
  · have hgapNat : d + 1 ≤ e := by omega
    have hgap : (0 : ℚ) ≤ (e : ℚ) - (d : ℚ) - 1 := by
      have hcast : (d : ℚ) + 1 ≤ (e : ℚ) := by
        exact_mod_cast hgapNat
      linarith
    have hfgap : (0 : ℚ) ≤ weightFraction e - weightFraction d := by
      have hf := weight_fraction_mono hde
      linarith
    have hprod := mul_nonneg hgap hfgap
    unfold baseWeight
    nlinarith

/-- The base of every signed edge weight is at most twice its smaller
    endpoint fraction.  Integer degree gaps are essential here. -/
theorem base_weight_le_twice_min (d e : ℕ) :
    baseWeight d e ≤ 2 * min (weightFraction d) (weightFraction e) := by
  by_cases hde : d ≤ e
  · have hf := weight_fraction_mono hde
    rw [min_eq_left hf]
    exact base_weight_le_twice_left hde
  · have hed : e ≤ d := by omega
    have hf := weight_fraction_mono hed
    rw [min_eq_right hf, base_weight_comm]
    exact base_weight_le_twice_left hed

end JSP523.Rank3
