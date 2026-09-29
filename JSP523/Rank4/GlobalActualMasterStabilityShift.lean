import JSP523.Rank4.GlobalActualMasterStabilityEndToEnd

namespace JSP523.Rank4

/-- Transfer an actual nonnegative error on `Fin n` to the `Fin (n+1)`
indexing used by the near-star endpoint. -/
theorem nonnegative_cubic_error_succ_ratio_tendsto_zero
    (f : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ f n)
    (hLimit : Filter.Tendsto (fun n => f n / (n : ℝ) ^ 3) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => f (n + 1) / (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  have hShift := hLimit.comp (Filter.tendsto_add_atTop_nat 1)
  have hBound : Filter.Tendsto
      (fun n => 8 * (f (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3)) Filter.atTop (nhds 0) := by
    simpa using hShift.const_mul 8
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => div_nonneg (hNonneg _) (by positivity))) ?_ hBound
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCube : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hNum := mul_le_mul_of_nonneg_left hCube (hNonneg (n + 1))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)).2
  have hDiv := (le_div_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3)).2 hNum
  convert hDiv using 1
  ring

end JSP523.Rank4
