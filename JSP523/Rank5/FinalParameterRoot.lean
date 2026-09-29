import JSP523.Rank5.InitialPolynomialScale

/-!
# Integer parameter root after nine regularization rounds

The finite Part IV scale can be expressed using the square root of the
nine-round factor. Its two-sided polynomial bounds avoid fractional
powers in the final error estimates.
-/

namespace JSP523.Rank5

open Filter

/-- The integer auxiliary scale built from the nine-round factor. -/
def finalParameterRoot (n : ℕ) : ℕ :=
  Nat.sqrt (discreteRoundIterate (initialPolynomialScale n) 9)

/-- Square-root bounds for any positive round factor below the initial
sixteenth-root scale. -/
theorem final_parameter_root_bounds_of_factor
    (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R)
    (hUpper : R ≤ initialPolynomialRoot n) :
    let U := Nat.sqrt R
    1 ≤ U ∧ U ^ 2 ≤ R ∧ R ≤ 4 * U ^ 2 ∧ U ^ 32 ≤ n := by
  let U := Nat.sqrt R
  have hU : 1 ≤ U := by
    change 1 ≤ Nat.sqrt R
    exact Nat.le_sqrt'.2 (by simpa using hR)
  have hSquare : U ^ 2 ≤ R := Nat.sqrt_le' R
  have hRupper : R ≤ 4 * U ^ 2 := by
    have hLt : R < (U + 1) ^ 2 := Nat.lt_succ_sqrt' R
    have hTwo : U + 1 ≤ 2 * U := by omega
    have hPow := Nat.pow_le_pow_left hTwo 2
    calc
      R ≤ (U + 1) ^ 2 := Nat.le_of_lt hLt
      _ ≤ (2 * U) ^ 2 := hPow
      _ = 4 * U ^ 2 := by ring
  have hRoot := (initial_polynomial_root_bounds n hn).2.1
  have hU32 : U ^ 32 ≤ n := by
    calc
      U ^ 32 = (U ^ 2) ^ 16 := by ring
      _ ≤ R ^ 16 := Nat.pow_le_pow_left hSquare 16
      _ ≤ (initialPolynomialRoot n) ^ 16 :=
        Nat.pow_le_pow_left hUpper 16
      _ ≤ n := hRoot
  exact ⟨hU, hSquare, hRupper, hU32⟩

/-- The actual nine-round factor yields the same four integer bounds. -/
theorem final_parameter_root_bounds
    (n : ℕ) (hn : 1 ≤ n)
    (hR : 1 ≤ discreteRoundIterate (initialPolynomialScale n) 9) :
    1 ≤ finalParameterRoot n ∧
      (finalParameterRoot n) ^ 2 ≤
        discreteRoundIterate (initialPolynomialScale n) 9 ∧
      discreteRoundIterate (initialPolynomialScale n) 9 ≤
        4 * (finalParameterRoot n) ^ 2 ∧
      (finalParameterRoot n) ^ 32 ≤ n := by
  exact final_parameter_root_bounds_of_factor n _ hn hR
    (initial_polynomial_nine_round_factor_bound n hn)

/-- The auxiliary scale diverges with the number of vertices. -/
theorem final_parameter_root_tendsto_at_top :
    Tendsto finalParameterRoot atTop atTop := by
  have hRound : Tendsto
      (fun n : ℕ => discreteRoundIterate (initialPolynomialScale n) 9)
      atTop atTop :=
    tendsto_discrete_round_iterate_at_top
      initialPolynomialScale initial_polynomial_scale_tendsto_at_top 9
  apply tendsto_atTop.2
  intro M
  have hLarge := hRound.eventually (eventually_ge_atTop (M ^ 2))
  filter_upwards [hLarge] with n hn
  exact Nat.le_sqrt'.2 hn

end JSP523.Rank5
