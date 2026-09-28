import JSP523.Rank3.ChargeTransfer
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Scalar receiver capacities in the rank-three charging proof

These are the numerical steps of §§II.5–II.6 in
`jsp-000523-proof/paper/proof.md`.
They do not construct the reciprocal receiver grouping; each theorem states
its finite numerical hypotheses explicitly.
-/

namespace JSP523.Rank3

/-- The two reciprocal `c=2` receivers have total capacity at most four.
This is the `h₁,h₂ ∈ {0,1,2}` calculation in §II.5. -/
theorem reciprocal_pair_capacity_le_four
    (h₁ h₂ : ℕ) (hh₁ : h₁ ≤ 2) (hh₂ : h₂ ≤ 2) :
    (h₁ : ℚ) * (2 - 2 * (h₂ : ℚ) / 3) +
      (h₂ : ℚ) * (2 - 2 * (h₁ : ℚ) / 3) ≤ 4 := by
  interval_cases h₁ <;> interval_cases h₂ <;> norm_num

/-- If the two relevant source pairs each have degree at least three,
their four possible charges have total capacity at most two. -/
theorem star_reciprocal_capacity_le_two
    (d₁ d₂ : ℕ) (hd₁ : 3 ≤ d₁) (hd₂ : 3 ≤ d₂) :
    (2 : ℚ) / ((d₁ : ℚ) - 1) +
      2 / ((d₂ : ℚ) - 1) ≤ 2 := by
  have hD₁ : (3 : ℚ) ≤ (d₁ : ℚ) := by exact_mod_cast hd₁
  have hD₂ : (3 : ℚ) ≤ (d₂ : ℚ) := by exact_mod_cast hd₂
  have h₁ : (2 : ℚ) ≤ (d₁ : ℚ) - 1 := by linarith
  have h₂ : (2 : ℚ) ≤ (d₂ : ℚ) - 1 := by linarith
  have hp₁ : 0 < (d₁ : ℚ) - 1 := by linarith
  have hp₂ : 0 < (d₂ : ℚ) - 1 := by linarith
  have hb₁ : (2 : ℚ) / ((d₁ : ℚ) - 1) ≤ 1 := by
    apply (div_le_iff₀ hp₁).mpr
    linarith
  have hb₂ : (2 : ℚ) / ((d₂ : ℚ) - 1) ≤ 1 := by
    apply (div_le_iff₀ hp₂).mpr
    linarith
  linarith

/-- Numerical bridge-demand inequality (II.10): four unit-bounded
individual charges in two page groups can exceed the baseline two only
by the sum of the two page minima. -/
theorem bridge_excess_le_page_demands
    (a b c d : ℚ)
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) (hd₀ : 0 ≤ d)
    (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) (hc₁ : c ≤ 1) (hd₁ : d ≤ 1) :
    max (a + b + c + d - 2) 0 ≤ min a b + min c d := by
  have hAB : a + b - 1 ≤ min a b :=
    le_min (by linarith) (by linarith)
  have hCD : c + d - 1 ≤ min c d :=
    le_min (by linarith) (by linarith)
  have hNonneg : 0 ≤ min a b + min c d := by
    have hMinAB : 0 ≤ min a b := le_min ha₀ hb₀
    have hMinCD : 0 ≤ min c d := le_min hc₀ hd₀
    linarith
  exact max_le_iff.mpr ⟨by linarith, hNonneg⟩

end JSP523.Rank3
