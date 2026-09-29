import JSP523.Rank3.PartIIAsymptotic
import JSP523.Counting.BinomialThresholdBounds

/-! # Coefficient-one density for every fixed rank at least three

The rank-three case uses Corollary II.2. For higher ranks, the eventual
exact extremal formula implies the same limit by elementary binomial
estimates. The forcing threshold is one more than the avoiding maximum.
-/

namespace JSP523

open Filter

/-- The elementary ratio between a star and its ambient shadow layer. -/
theorem shifted_choose_ratio (n k : ℕ) (hn : k + 1 ≤ n) :
    ((n - 1).choose k : ℝ) / (n.choose k : ℝ) = 1 - (k : ℝ) / n := by
  have hn1 : 1 ≤ n := by omega
  have hPos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNat := Nat.choose_mul_succ_eq (n - 1) k
  rw [Nat.sub_add_cancel hn1] at hNat
  have hEqNat : ((n - 1).choose k : ℝ) * n = (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast hNat
  rw [Nat.cast_sub (show k ≤ n by omega)] at hEqNat
  have hEq := hEqNat
  apply (div_eq_iff hPos.ne').2
  field_simp [hnPos.ne']
  nlinarith only [hEq]

/-- A fixed binomial coefficient of order at least two dominates a
quadratic term, with an explicit constant. -/
theorem quadratic_le_factorial_choose (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 4 ≤ n) :
    n ^ 2 ≤ 4 * k.factorial * n.choose k := by
  let b := n + 1 - k
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hnb : n ≤ 2 * b := by dsimp [b]; omega
  have hp : b ^ 2 ≤ b ^ k := Nat.pow_le_pow_right hb hk
  have hChoose := Counting.pow_sub_le_factorial_mul_choose n k
  have hSq := Nat.pow_le_pow_left hnb 2
  change b ^ k ≤ k.factorial * n.choose k at hChoose
  nlinarith only [hSq, hp, hChoose]

/-- Every nonnegative linear-size error is negligible relative to a
fixed binomial coefficient of order at least two. -/
theorem linear_error_choose_ratio_tendsto_zero
    (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ᶠ n in atTop, f n ≤ n + 1) :
    Tendsto (fun n => (f n : ℝ) / (n.choose k : ℝ)) atTop (nhds 0) := by
  have hUpper := tendsto_const_div_atTop_nhds_zero_nat (8 * (k.factorial : ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hUpper
  filter_upwards [hf, eventually_ge_atTop (2 * k + 4)] with n hfn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnPos : (0 : ℝ) < n := by linarith
  have hChoosePos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hQuadratic : (n : ℝ) ^ 2 ≤ 4 * (k.factorial : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast quadratic_le_factorial_choose n k hk hn
  have hF : (f n : ℝ) ≤ 2 * n := by
    have h : (f n : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hfn
    linarith
  apply (div_le_div_iff₀ hChoosePos hnPos).2
  nlinarith only [mul_le_mul_of_nonneg_right hF hnPos.le, hQuadratic]

/-- Fixed-rank stars have coefficient one in the ambient binomial scale. -/
theorem shifted_choose_ratio_tendsto_one (k : ℕ) :
    Tendsto (fun n => ((n - 1).choose k : ℝ) / (n.choose k : ℝ)) atTop (nhds 1) := by
  have hLimit : Tendsto (fun n : ℕ => 1 - (k : ℝ) / n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  apply hLimit.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  exact (shifted_choose_ratio n k hn).symm

/-- The eventual exact formula supplies coefficient-one density at any
fixed rank at least four. -/
theorem exact_formula_density_tendsto_one
    (r : ℕ) (hr : 4 ≤ r)
    (hExact : ∀ᶠ n in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
        (n - 1).choose (r - 1) + (n - 1) / r) :
    Tendsto (fun n => (maxAvoidingCard (Finset.univ : Edge (Fin n)) r : ℝ) /
      (n.choose (r - 1) : ℝ)) atTop (nhds 1) := by
  have hError := linear_error_choose_ratio_tendsto_zero (r - 1) (by omega)
    (fun n => (n - 1) / r) (Eventually.of_forall (fun n =>
      (Nat.div_le_self (n - 1) r).trans (by omega)))
  have hLimit := (shifted_choose_ratio_tendsto_one (r - 1)).add hError
  simp only [add_zero] at hLimit
  apply hLimit.congr'
  filter_upwards [hExact] with n hn
  rw [hn, Nat.cast_add, add_div]

/-- Manuscript Theorem 1 for the avoiding maximum, from the eventual
higher-rank exact formula and the proved rank-three theorem. -/
theorem coefficient_one_avoiding_density_of_eventual_exact
    (hExact : ∀ r : ℕ, 4 ≤ r → ∀ᶠ n in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
        (n - 1).choose (r - 1) + (n - 1) / r)
    (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun n => (maxAvoidingCard (Finset.univ : Edge (Fin n)) r : ℝ) /
      (n.choose (r - 1) : ℝ)) atTop (nhds 1) := by
  by_cases h3 : r = 3
  · subst r
    apply Rank3.corollary_ii_2_asymptotic.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    simp only [Rank3.rankThreeDensity, ite_eq_left hn]
  · exact exact_formula_density_tendsto_one r (by omega) (hExact r (by omega))

/-- The least forcing threshold has coefficient one for every fixed
rank at least three. Its equality to `maxAvoidingCard + 1` is the finite
`forcing_threshold_exact` theorem. -/
theorem coefficient_one_forcing_density_of_eventual_exact
    (hExact : ∀ r : ℕ, 4 ≤ r → ∀ᶠ n in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
        (n - 1).choose (r - 1) + (n - 1) / r)
    (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun n => ((maxAvoidingCard (Finset.univ : Edge (Fin n)) r + 1 : ℕ) : ℝ) /
      (n.choose (r - 1) : ℝ)) atTop (nhds 1) := by
  have hMain := coefficient_one_avoiding_density_of_eventual_exact hExact r hr
  have hOne := linear_error_choose_ratio_tendsto_zero (r - 1) (by omega)
    (fun _ => 1) (Eventually.of_forall (fun _ => by omega))
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using hMain.add hOne

end JSP523
