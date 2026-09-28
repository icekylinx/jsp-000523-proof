import JSP523.Rank3.PartIICorollary
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Corollary II.2: asymptotic formulation

The finite rank-three bounds imply that the extremal size, normalized by
`choose n 2`, tends to one.
-/

namespace JSP523.Rank3

open Filter
open scoped Topology

/-- The extremal rank-three density on `Fin n`, with the finitely many
small values assigned zero so the quotient is defined everywhere. -/
noncomputable def rankThreeDensity (n : ℕ) : ℝ :=
  if 3 ≤ n then
    (maxAvoidingCard (Finset.univ : Finset (Fin n)) 3 : ℝ) /
      (Nat.choose n 2 : ℝ)
  else 0


/-- The ratio of the two binomial bounds is `1 - 2/n` for `n ≥ 3`. -/
private theorem lower_choose_ratio (n : ℕ) (hn : 3 ≤ n) :
    ((n - 1).choose 2 : ℝ) / (n.choose 2 : ℝ) = 1 - 2 / (n : ℝ) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hCast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [Nat.cast_choose_two, Nat.cast_choose_two, hCast]
  field_simp [hn0, hn1]
  ring

/-- The finite extremal sandwich, normalized by `choose n 2`. -/
theorem rankThreeDensity_bounds (n : ℕ) (hn : 3 ≤ n) :
    1 - 2 / (n : ℝ) ≤ rankThreeDensity n ∧ rankThreeDensity n ≤ 1 := by
  have hBounds := corollary_II_2_finite
    (Finset.univ : Finset (Fin n)) (by simpa using hn)
  have hLower : (n - 1).choose 2 ≤
      maxAvoidingCard (Finset.univ : Finset (Fin n)) 3 := by
    simpa using hBounds.1
  have hUpper : maxAvoidingCard (Finset.univ : Finset (Fin n)) 3 ≤
      n.choose 2 := by
    simpa using hBounds.2
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hDenPos : 0 < (n.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hnPos : (0 : ℝ) < n := by linarith
    have hnSubPos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    positivity
  rw [rankThreeDensity, ite_eq_left hn]
  constructor
  · rw [← lower_choose_ratio n hn]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hLower) hDenPos.le
  · have hCast : (maxAvoidingCard (Finset.univ : Finset (Fin n)) 3 : ℝ) ≤
        (n.choose 2 : ℝ) := by exact_mod_cast hUpper
    exact (div_le_iff₀ hDenPos).2 (by simpa using hCast)

/-- The asymptotic assertion of Corollary II.2: extremal density tends to one. -/
theorem corollary_II_2_asymptotic :
    Tendsto rankThreeDensity atTop (nhds 1) := by
  have hZero : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ))
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 2
  have hLowerLimit : Tendsto (fun n : ℕ => 1 - 2 / (n : ℝ))
      atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hZero using 1; simp
  have hLowerEvent : ∀ᶠ n : ℕ in atTop,
      1 - 2 / (n : ℝ) ≤ rankThreeDensity n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (rankThreeDensity_bounds n hn).1
  have hUpperEvent : ∀ᶠ n : ℕ in atTop, rankThreeDensity n ≤ 1 := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (rankThreeDensity_bounds n hn).2
  exact hLowerLimit.squeeze' tendsto_const_nhds hLowerEvent hUpperEvent

end JSP523.Rank3
