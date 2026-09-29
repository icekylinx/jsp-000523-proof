import JSP523.Rank5.FinalParameterRoot

/-!
# Feasibility of the integer Part IV parameters

The thresholds are integer quotients of powers of the auxiliary scale.
These inequalities keep every denominator positive and preserve the
needed separation after rounding down.
-/

namespace JSP523.Rank5

/-- A positive integer quotient is within a factor two of its real
ratio when the numerator is at least the denominator. -/
theorem nat_quotient_real_bounds
    (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    (a : ℝ) / (2 * b) ≤ (a / b : ℕ) ∧
      ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  have hq : 1 ≤ a / b :=
    (Nat.le_div_iff_mul_le hb).2 (by simpa using hba)
  have hLt : a < b * (a / b + 1) := Nat.lt_mul_div_succ a hb
  have hbq : b ≤ b * (a / b) := by
    simpa using Nat.mul_le_mul_left b hq
  have hDouble : a ≤ 2 * b * (a / b) := by
    calc
      a ≤ b * (a / b + 1) := Nat.le_of_lt hLt
      _ = b * (a / b) + b := by ring
      _ ≤ b * (a / b) + b * (a / b) :=
        Nat.add_le_add_left hbq _
      _ = 2 * b * (a / b) := by ring
  have hLowerCast : (a : ℝ) ≤
      2 * (b : ℝ) * ((a / b : ℕ) : ℝ) := by
    exact_mod_cast hDouble
  have hUpperCast : ((a / b : ℕ) : ℝ) * (b : ℝ) ≤ a := by
    exact_mod_cast Nat.div_mul_le_self a b
  have hbReal : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * b)).2
    nlinarith
  · exact (le_div_iff₀ hbReal).2 hUpperCast

/-- Integer division retains an exact nested-quotient comparison. -/
theorem final_nested_quotient_bound
    (n U : ℕ) (hU : 0 < U) :
    U ^ 4 * (n / U ^ 8) ≤ n / U ^ 4 := by
  have hDen : 0 < U ^ 4 := pow_pos hU _
  apply (Nat.le_div_iff_mul_le hDen).2
  calc
    U ^ 4 * (n / U ^ 8) * U ^ 4 =
        (n / U ^ 8) * U ^ 8 := by ring
    _ ≤ n := Nat.div_mul_le_self n (U ^ 8)

/-- All basic integer thresholds and the retention fraction meet the
finite hypotheses used in the lower and upper cleanup lemmas. -/
theorem final_parameter_feasibility
    (n U : ℕ) (hU : 2 ≤ U) (hN : U ^ 32 ≤ n) :
    let u := n / U ^ 4
    let q := n / U ^ 8
    let L3 := 4 * q
    let tLower := n / U ^ 12
    let tUpper := n ^ 2 / U ^ 12
    let Q := U ^ 4
    let ε : ℝ := 2 / (U ^ 4 : ℝ)
    8 ≤ u ∧ 1 ≤ tLower ∧ 1 ≤ tUpper ∧ 0 < q ∧
      Q * L3 ≤ 16 * u ∧ q < u ∧ (q : ℝ) ≤ ε * u := by
  let u := n / U ^ 4
  let q := n / U ^ 8
  let L3 := 4 * q
  let tLower := n / U ^ 12
  let tUpper := n ^ 2 / U ^ 12
  let Q := U ^ 4
  let ε : ℝ := 2 / (U ^ 4 : ℝ)
  have hUpos : 0 < U := by omega
  have hUone : 1 ≤ U := by omega
  have hDen4 : 0 < U ^ 4 := pow_pos hUpos _
  have hDen8 : 0 < U ^ 8 := pow_pos hUpos _
  have hDen12 : 0 < U ^ 12 := pow_pos hUpos _
  have hNpos : 1 ≤ n := by
    have hPow : 1 ≤ U ^ 32 := Nat.one_le_pow _ _ hUone
    omega
  have hU8 : U ^ 8 ≤ n :=
    (pow_le_pow_right₀ hUone (by omega : 8 ≤ 32)).trans hN
  have hU12 : U ^ 12 ≤ n :=
    (pow_le_pow_right₀ hUone (by omega : 12 ≤ 32)).trans hN
  have hEight : 8 * U ^ 4 ≤ n := by
    have hCube : 8 ≤ U ^ 3 := by
      have h := Nat.pow_le_pow_left hU 3
      norm_num at h ⊢
      exact h
    have hMul := Nat.mul_le_mul_right (U ^ 4) hCube
    have hPow : U ^ 7 ≤ U ^ 32 :=
      pow_le_pow_right₀ hUone (by omega)
    calc
      8 * U ^ 4 ≤ U ^ 3 * U ^ 4 := hMul
      _ = U ^ 7 := by ring
      _ ≤ U ^ 32 := hPow
      _ ≤ n := hN
  have hu : 8 ≤ u :=
    (Nat.le_div_iff_mul_le hDen4).2 (by simpa [u] using hEight)
  have htLower : 1 ≤ tLower :=
    (Nat.le_div_iff_mul_le hDen12).2 (by simpa [tLower] using hU12)
  have htUpper : 1 ≤ tUpper := by
    apply (Nat.le_div_iff_mul_le hDen12).2
    have hNN : n ≤ n ^ 2 := by nlinarith
    simpa [tUpper] using hU12.trans hNN
  have hq : 0 < q := by
    have hOne : 1 ≤ q :=
      (Nat.le_div_iff_mul_le hDen8).2 (by simpa [q] using hU8)
    omega
  have hNested : Q * q ≤ u := by
    simpa [Q, q, u] using final_nested_quotient_bound n U hUpos
  have hQge : 16 ≤ Q := by
    have h := Nat.pow_le_pow_left hU 4
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
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hDen4
  have hε : (q : ℝ) ≤ ε * u := by
    dsimp [ε, Q] at hReal ⊢
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by exact_mod_cast hDen4 :
      (0 : ℝ) < (U ^ 4 : ℝ))).2
    have hRealPow : (U : ℝ) ^ 4 * (q : ℝ) ≤ (u : ℝ) := by
      simpa only [Nat.cast_pow] using hReal
    have hCharge : (q : ℝ) * (U : ℝ) ^ 4 ≤ (u : ℝ) := by
      calc
        (q : ℝ) * (U : ℝ) ^ 4 =
            (U : ℝ) ^ 4 * (q : ℝ) := by ring
        _ ≤ (u : ℝ) := hRealPow
    have huNonneg : (0 : ℝ) ≤ u := by positivity
    linarith
  exact ⟨hu, htLower, htUpper, hq, hL3, hqLt, hε⟩

end JSP523.Rank5
