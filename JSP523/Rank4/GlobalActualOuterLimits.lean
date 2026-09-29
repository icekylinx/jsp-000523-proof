import JSP523.Rank4.GlobalActualOuterOverlap
import JSP523.Rank4.GlobalActualErrorLimits

/-! # Cubic normalization of the actual outer overlap -/

namespace JSP523.Rank4

/-- The finite overlap estimate is negligible whenever the product of the
number of outer centers and the fixed core facet cap is `o(n)`. -/
theorem outer_overlap_choose_ratio_tendsto_zero_of_product
    (centers cap overlap : ℕ → ℕ)
    (hProduct : Filter.Tendsto
      (fun n : ℕ => ((centers n * cap n : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0))
    (hBound : ∀ᶠ n in Filter.atTop,
      overlap n ≤ centers n * n * (n + 9) * cap n) :
    Filter.Tendsto (fun n : ℕ => (overlap n : ℝ) / (n.choose 3 : ℝ))
      Filter.atTop (nhds 0) := by
  apply nonnegative_cubic_error_choose_ratio_tendsto_zero
    (fun n => (overlap n : ℝ)) (fun _ => by positivity)
  have hUpper : Filter.Tendsto
      (fun n : ℕ => 2 * (((centers n * cap n : ℕ) : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hProduct.const_mul 2
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hUpper
  filter_upwards [hBound, Filter.eventually_ge_atTop (9 : ℕ)] with n hn hn9
  have hnPos : (0 : ℝ) < n := by
    have hnNatPos : 0 < n := by omega
    exact_mod_cast hnNatPos
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnPos
  have hLinear : n + 9 ≤ 2 * n := by omega
  have hNat : overlap n ≤ 2 * (centers n * cap n) * n ^ 2 := by
    calc
      overlap n ≤ centers n * n * (n + 9) * cap n := hn
      _ ≤ centers n * n * (2 * n) * cap n := by
        exact Nat.mul_le_mul_right (cap n)
          (Nat.mul_le_mul_left (centers n * n) hLinear)
      _ = 2 * (centers n * cap n) * n ^ 2 := by ring
  have hReal : (overlap n : ℝ) ≤
      2 * ((centers n * cap n : ℕ) : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast hNat
  have hDiv := div_le_div_of_nonneg_right hReal (by positivity : 0 ≤ (n : ℝ) ^ 3)
  have hEq : (2 * ((centers n * cap n : ℕ) : ℝ) * (n : ℝ) ^ 2) /
      (n : ℝ) ^ 3 =
      2 * (((centers n * cap n : ℕ) : ℝ) / (n : ℝ)) := by
    field_simp
  simpa only [hEq] using hDiv

end JSP523.Rank4
