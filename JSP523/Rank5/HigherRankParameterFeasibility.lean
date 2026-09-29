import JSP523.Rank5.FinalParameterFeasibility

/-! # Rounded higher-rank thresholds with rho=U⁻³ -/
namespace JSP523.Rank5

/-- Integer division retains an exact nested-quotient comparison. -/
theorem higher_nested_quotient_bound
    (n U : ℕ) (hU : 0 < U) :
    U ^ 3 * (n / U ^ 6) ≤ n / U ^ 3 := by
  have hDen : 0 < U ^ 3 := pow_pos hU _
  apply (Nat.le_div_iff_mul_le hDen).2
  calc
    U ^ 3 * (n / U ^ 6) * U ^ 3 =
        (n / U ^ 6) * U ^ 6 := by ring
    _ ≤ n := Nat.div_mul_le_self n (U ^ 6)

/-- All basic integer thresholds and the retention fraction meet the
finite hypotheses used in the lower and upper cleanup lemmas. -/
theorem higher_parameter_feasibility
    (n U : ℕ) (hU : 2 ≤ U) (hN : U ^ 32 ≤ n) :
    let u := n / U ^ 3
    let q := n / U ^ 6
    let L3 := 4 * q
    let tLower := n / U ^ 9
    let tUpper := n ^ 2 / U ^ 9
    let Q := U ^ 3
    let ε : ℝ := 2 / (U ^ 3 : ℝ)
    8 ≤ u ∧ 1 ≤ tLower ∧ 1 ≤ tUpper ∧ 0 < q ∧
      Q * L3 ≤ 16 * u ∧ q < u ∧ (q : ℝ) ≤ ε * u := by
  let u := n / U ^ 3
  let q := n / U ^ 6
  let L3 := 4 * q
  let tLower := n / U ^ 9
  let tUpper := n ^ 2 / U ^ 9
  let Q := U ^ 3
  let ε : ℝ := 2 / (U ^ 3 : ℝ)
  have hUpos : 0 < U := by omega
  have hUone : 1 ≤ U := by omega
  have hDen3 : 0 < U ^ 3 := pow_pos hUpos _
  have hDen6 : 0 < U ^ 6 := pow_pos hUpos _
  have hDen9 : 0 < U ^ 9 := pow_pos hUpos _
  have hNpos : 1 ≤ n := by
    have hPow : 1 ≤ U ^ 32 := Nat.one_le_pow _ _ hUone
    omega
  have hU6 : U ^ 6 ≤ n :=
    (pow_le_pow_right₀ hUone (by omega : 6 ≤ 32)).trans hN
  have hU9 : U ^ 9 ≤ n :=
    (pow_le_pow_right₀ hUone (by omega : 9 ≤ 32)).trans hN
  have hEight : 8 * U ^ 3 ≤ n := by
    have hCube : 8 ≤ U ^ 3 := by
      have h := Nat.pow_le_pow_left hU 3
      norm_num at h ⊢
      exact h
    have hMul := Nat.mul_le_mul_right (U ^ 3) hCube
    have hPow : U ^ 6 ≤ U ^ 32 :=
      pow_le_pow_right₀ hUone (by omega)
    calc
      8 * U ^ 3 ≤ U ^ 3 * U ^ 3 := hMul
      _ = U ^ 6 := by ring
      _ ≤ U ^ 32 := hPow
      _ ≤ n := hN
  have hu : 8 ≤ u :=
    (Nat.le_div_iff_mul_le hDen3).2 (by simpa [u] using hEight)
  have htLower : 1 ≤ tLower :=
    (Nat.le_div_iff_mul_le hDen9).2 (by simpa [tLower] using hU9)
  have htUpper : 1 ≤ tUpper := by
    apply (Nat.le_div_iff_mul_le hDen9).2
    have hNN : n ≤ n ^ 2 := by nlinarith
    simpa [tUpper] using hU9.trans hNN
  have hq : 0 < q := by
    have hOne : 1 ≤ q :=
      (Nat.le_div_iff_mul_le hDen6).2 (by simpa [q] using hU6)
    omega
  have hNested : Q * q ≤ u := by
    simpa [Q, q, u] using higher_nested_quotient_bound n U hUpos
  have hQge : 8 ≤ Q := by
    have h := Nat.pow_le_pow_left hU 3
    norm_num at h ⊢
    exact h
  have hL3 : Q * L3 ≤ 16 * u := by
    have hFour := Nat.mul_le_mul_left 4 hNested
    dsimp [L3]
    nlinarith
  have hqLt : q < u := by
    have hStrict : q < Q * q := by
      nlinarith [hQge, hq]
    omega
  have hReal : (Q : ℝ) * q ≤ (u : ℝ) := by
    exact_mod_cast hNested
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hDen3
  have hε : (q : ℝ) ≤ ε * u := by
    dsimp [ε, Q] at hReal ⊢
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by exact_mod_cast hDen3 :
      (0 : ℝ) < (U ^ 3 : ℝ))).2
    have hRealPow : (U : ℝ) ^ 3 * (q : ℝ) ≤ (u : ℝ) := by
      simpa only [Nat.cast_pow] using hReal
    have hCharge : (q : ℝ) * (U : ℝ) ^ 3 ≤ (u : ℝ) := by
      calc
        (q : ℝ) * (U : ℝ) ^ 3 =
            (U : ℝ) ^ 3 * (q : ℝ) := by ring
        _ ≤ (u : ℝ) := hRealPow
    have huNonneg : (0 : ℝ) ≤ u := by positivity
    linarith
  exact ⟨hu, htLower, htUpper, hq, hL3, hqLt, hε⟩

/-- Every positive ambient power supports the rounded thresholds. -/
theorem higher_power_quotient_real_bounds
    (N U a b : ℕ) (hU : 1 ≤ U) (hN : U ^ 32 ≤ N)
    (ha : 1 ≤ a) (hb : b ≤ 32) :
    (N : ℝ) ^ a / (2 * (U : ℝ) ^ b) ≤ ((N ^ a / U ^ b : ℕ) : ℝ) ∧
      ((N ^ a / U ^ b : ℕ) : ℝ) ≤ (N : ℝ) ^ a / (U : ℝ) ^ b := by
  have hNOne : 1 ≤ N := (Nat.one_le_pow _ _ hU).trans hN
  have hPower : N ≤ N ^ a := by
    simpa only [pow_one] using pow_le_pow_right₀ hNOne ha
  have hDen : U ^ b ≤ N ^ a :=
    ((pow_le_pow_right₀ hU hb).trans hN).trans hPower
  simpa only [Nat.cast_pow] using
    nat_quotient_real_bounds (N ^ a) (U ^ b) (pow_pos (by omega) _) hDen

end JSP523.Rank5
