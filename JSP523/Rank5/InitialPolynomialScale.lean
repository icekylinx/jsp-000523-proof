import JSP523.Rank5.InitialCodegreeCleanup
import JSP523.Rank5.FarStarAsymptotic

open Filter Asymptotics

/-!
# Explicit polynomial alternative for the initial logarithmic scales

Writing `U = ⌊n^(1/16)⌋`, the choices `h₀ = U⁷` and `Scale = U¹⁰`
have exactly the separation properties used by the manuscript's
`√n/log n` and `√n log³ n` choices. They avoid transcendental rounding
inside the finite cleanup ledger.
-/

namespace JSP523.Rank5

def initialPolynomialRoot (n : ℕ) : ℕ := Nat.nthRoot 16 n

def initialPolynomialFarSize (n : ℕ) : ℕ :=
  (initialPolynomialRoot n) ^ 7

def initialPolynomialScale (n : ℕ) : ℕ :=
  (initialPolynomialRoot n) ^ 10

theorem initial_polynomial_root_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ initialPolynomialRoot n ∧
      (initialPolynomialRoot n) ^ 16 ≤ n ∧
      n ≤ 2 ^ 16 * (initialPolynomialRoot n) ^ 16 := by
  let U := initialPolynomialRoot n
  have hUpos : 1 ≤ U := by
    dsimp [U, initialPolynomialRoot]
    apply (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2
    simpa using hn
  have hLo : U ^ 16 ≤ n := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hHi : n < (U + 1) ^ 16 :=
    Nat.lt_pow_nthRoot_add_one (by norm_num : 16 ≠ 0) n
  have hDouble : U + 1 ≤ 2 * U := by omega
  refine ⟨hUpos, hLo, ?_⟩
  calc
    n ≤ (U + 1) ^ 16 := Nat.le_of_lt hHi
    _ ≤ (2 * U) ^ 16 := Nat.pow_le_pow_left hDouble _
    _ = 2 ^ 16 * U ^ 16 := by rw [mul_pow]

theorem initial_polynomial_far_square_bound
    (n q : ℕ) (hn : 1 ≤ n)
    (hq : q ≤ (initialPolynomialRoot n) ^ 2) :
    q * (initialPolynomialFarSize n) ^ 2 ≤ n := by
  let U := initialPolynomialRoot n
  have hLo := (initial_polynomial_root_bounds n hn).2.1
  calc
    q * (initialPolynomialFarSize n) ^ 2 = q * U ^ 14 := by
      dsimp [initialPolynomialFarSize, U]
      ring
    _ ≤ U ^ 2 * U ^ 14 := Nat.mul_le_mul_right _ hq
    _ = U ^ 16 := by ring
    _ ≤ n := hLo

theorem initial_polynomial_scale_bounds
    (n : ℕ) (hn : 1 ≤ n) :
    0 < initialPolynomialScale n ∧
      initialPolynomialScale n ≤ n ∧
      (initialPolynomialScale n) ^ 3 ≤ n ^ 2 := by
  let U := initialPolynomialRoot n
  obtain ⟨hUpos, hLo, _⟩ := initial_polynomial_root_bounds n hn
  have hPow10 : U ^ 10 ≤ U ^ 16 := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ U) (by omega : 10 ≤ 16)
  have hPow30 : U ^ 30 ≤ U ^ 32 := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ U) (by omega : 30 ≤ 32)
  refine ⟨?_, hPow10.trans hLo, ?_⟩
  · dsimp [initialPolynomialScale]
    exact pow_pos (by omega : 0 < U) _
  · calc
      (initialPolynomialScale n) ^ 3 = U ^ 30 := by
        dsimp [initialPolynomialScale, U]
        ring
      _ ≤ U ^ 32 := hPow30
      _ = (U ^ 16) ^ 2 := by ring
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hLo 2

/-- The rounded matching parameter is at most a fixed rank-independent
multiple of `U⁶`. -/
theorem initial_polynomial_multiplier_bound
    (n : ℕ) (hn : 1 ≤ n) :
    initialScaleMultiplier n (initialPolynomialScale n) ≤
      (3 * 2 ^ 16 + 1) * (initialPolynomialRoot n) ^ 6 := by
  let U := initialPolynomialRoot n
  have hUpos := (initial_polynomial_root_bounds n hn).1
  have hHi := (initial_polynomial_root_bounds n hn).2.2
  have hU10 : 0 < U ^ 10 := pow_pos (by omega : 0 < U) _
  have hProduct : 3 * n ≤ (3 * 2 ^ 16 * U ^ 6) * U ^ 10 := by
    calc
      3 * n ≤ 3 * (2 ^ 16 * U ^ 16) := Nat.mul_le_mul_left 3 hHi
      _ = (3 * 2 ^ 16 * U ^ 6) * U ^ 10 := by ring
  have hDiv : 3 * n / U ^ 10 ≤ 3 * 2 ^ 16 * U ^ 6 := by
    calc
      3 * n / U ^ 10 ≤
          ((3 * 2 ^ 16 * U ^ 6) * U ^ 10) / U ^ 10 :=
        Nat.div_le_div_right hProduct
      _ = 3 * 2 ^ 16 * U ^ 6 := by
        rw [Nat.mul_comm (3 * 2 ^ 16 * U ^ 6) (U ^ 10)]
        exact Nat.mul_div_cancel_left _ hU10
  have hOne : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ hUpos
  dsimp [initialScaleMultiplier, initialPolynomialScale, U]
  nlinarith [hDiv, hOne]

theorem initial_polynomial_cleanup_multiplier_gap
    (n r m : ℕ) (hn : 1 ≤ n)
    (hU : m * (r * r) * (3 * 2 ^ 16 + 1) ≤
      initialPolynomialRoot n) :
    m * (r * r * initialScaleMultiplier n
      (initialPolynomialScale n)) ≤
        initialPolynomialFarSize n + 1 := by
  let U := initialPolynomialRoot n
  have ha := initial_polynomial_multiplier_bound n hn
  have hProduct := Nat.mul_le_mul_left (m * (r * r)) ha
  have hRoot := Nat.mul_le_mul_right (U ^ 6) hU
  have hPow : U * U ^ 6 = U ^ 7 := by ring
  dsimp [initialPolynomialFarSize, U]
  nlinarith [hProduct, hRoot, hPow]

theorem initial_polynomial_scale_separation
    (n r : ℕ) (hn : 1 ≤ n)
    (hU : 16 * r * 2 ^ 16 < (initialPolynomialRoot n) ^ 4) :
    16 * r * n < (initialPolynomialScale n) ^ 2 := by
  let U := initialPolynomialRoot n
  have hUpos := (initial_polynomial_root_bounds n hn).1
  have hN := (initial_polynomial_root_bounds n hn).2.2
  have hUpow : 0 < U ^ 16 := pow_pos (by omega : 0 < U) _
  calc
    16 * r * n ≤ 16 * r * (2 ^ 16 * U ^ 16) :=
      Nat.mul_le_mul_left _ hN
    _ = (16 * r * 2 ^ 16) * U ^ 16 := by ring
    _ < U ^ 4 * U ^ 16 :=
      (Nat.mul_lt_mul_right hUpow).2 hU
    _ = (initialPolynomialScale n) ^ 2 := by
      dsimp [initialPolynomialScale, U]
      ring

theorem initial_polynomial_root_tendsto_at_top :
    Tendsto initialPolynomialRoot atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (m ^ 16)] with n hn
  exact (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2 hn

theorem eventually_initial_polynomial_far_small (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      q * (initialPolynomialFarSize n) ^ 2 ≤ n := by
  have hRoot := initial_polynomial_root_tendsto_at_top.eventually
    (eventually_ge_atTop (max 1 q))
  filter_upwards [eventually_ge_atTop 1, hRoot] with n hn hU
  have hUpos : 1 ≤ initialPolynomialRoot n := (le_max_left _ _).trans hU
  have hq : q ≤ initialPolynomialRoot n := (le_max_right _ _).trans hU
  have hqSq : q ≤ (initialPolynomialRoot n) ^ 2 :=
    hq.trans (le_self_pow hUpos (by norm_num : 2 ≠ 0))
  exact initial_polynomial_far_square_bound n q hn hqSq

theorem initial_polynomial_far_square_is_little_o :
    (fun n : ℕ => ((initialPolynomialFarSize n) ^ 2 : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨q, hqgt⟩ := exists_nat_gt ((1 : ℝ) / c)
  have hqpos : 0 < q := by
    have hNonneg : (0 : ℝ) ≤ 1 / c := by positivity
    exact_mod_cast (lt_of_le_of_lt hNonneg hqgt)
  have hCoeff : (1 : ℝ) / q ≤ c := by
    have h := (div_lt_iff₀ hc).mp hqgt
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
    apply (div_le_iff₀ hqreal).2
    nlinarith
  filter_upwards [eventually_initial_polynomial_far_small q]
    with n hn
  have hReal : (q : ℝ) * (initialPolynomialFarSize n : ℝ) ^ 2 ≤
      (n : ℝ) := by exact_mod_cast hn
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hDiv : (initialPolynomialFarSize n : ℝ) ^ 2 ≤
      (1 / (q : ℝ)) * n := by
    have hDiv' : (initialPolynomialFarSize n : ℝ) ^ 2 ≤
        (n : ℝ) / q := (le_div_iff₀ hqreal).2 (by nlinarith [hReal])
    simpa [div_eq_mul_inv, mul_comm] using hDiv'
  have hBound : (initialPolynomialFarSize n : ℝ) ^ 2 ≤ c * n :=
    hDiv.trans (mul_le_mul_of_nonneg_right hCoeff (by positivity))
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (initialPolynomialFarSize n : ℝ)),
    abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using hBound

end JSP523.Rank5
