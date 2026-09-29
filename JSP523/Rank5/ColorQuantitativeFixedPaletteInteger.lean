import JSP523.Rank5.ColorQuantitativeFixedPaletteScale
import JSP523.Rank5.FinalParameterFeasibility

namespace JSP523.Rank5

/-- Integer rounding preserves the complete cleanup error bound for all
core sizes at least three and root sizes at least two. -/
theorem fixed_palette_integer_cleanup_cost_bound
    (n m U r s k : ℕ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n)
    (hs : 2 ≤ s) (hk : 3 ≤ k) :
    fixedPaletteCleanupCost n m r s k
      (n ^ (k - 2) / U ^ 9) (n ^ (s - 1) / U ^ 3) (n ^ (s - 1) / U ^ 6)
      (4 * U ^ 2 * n ^ (k - 2)) (4 * U ^ 2 * n ^ (k - 3))
      (4 * U ^ 2 * n ^ (s - 1)) (4 * U ^ 2 * n ^ (s - 2)) ≤
      (fixedPaletteAmbientErrorConstant k : ℝ) * ((n : ℝ) ^ (k + s - 1) / U) +
        (fixedPaletteMassErrorConstant r s k : ℝ) * ((m : ℝ) / U) := by
  have hUp : 0 < U := by omega
  have hn1 : 1 ≤ n := (Nat.one_le_pow _ _ hU).trans hn
  have hnK : n ≤ n ^ (k - 2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (by omega : 1 ≤ k - 2)
  have hnS : n ≤ n ^ (s - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (by omega : 1 ≤ s - 1)
  have hU9 : U ^ 9 ≤ n ^ (k - 2) :=
    ((pow_le_pow_right₀ hU (by decide : 9 ≤ 32)).trans hn).trans hnK
  have hU3 : U ^ 3 ≤ n ^ (s - 1) :=
    ((pow_le_pow_right₀ hU (by decide : 3 ≤ 32)).trans hn).trans hnS
  have hU6 : U ^ 6 ≤ n ^ (s - 1) :=
    ((pow_le_pow_right₀ hU (by decide : 6 ≤ 32)).trans hn).trans hnS
  have ht := nat_quotient_real_bounds (n ^ (k - 2)) (U ^ 9) (pow_pos hUp _) hU9
  have hu := nat_quotient_real_bounds (n ^ (s - 1)) (U ^ 3) (pow_pos hUp _) hU3
  have hq := nat_quotient_real_bounds (n ^ (s - 1)) (U ^ 6) (pow_pos hUp _) hU6
  push_cast at ht hu hq
  exact fixed_palette_cleanup_cost_scale_bound n m U r s k _ _ _ hU hn hs hk
    (Nat.div_pos hU9 (pow_pos hUp _)) ht.1 ht.2 hu.1 hu.2 hq.1

end JSP523.Rank5
