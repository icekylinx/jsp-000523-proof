import JSP523.Rank4.GlobalActualErrorLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The explicit first outer decomposition loss is subcubic -/

namespace JSP523.Rank4

open Filter

/-- The integer budget supplied by the actual initial outer decomposition. -/
def initial_outer_polynomial_budget (n z x radius : ℕ) : ℕ :=
  ((z + x).choose 2 + x.choose 2) * n ^ 2 +
    2 * (z + x) * n ^ 2 * (Nat.sqrt n + 1) +
    (radius + 3) * n ^ 2

/-- The integer radius used for the exactly-once layer at cover vertices. -/
noncomputable def initial_outer_radius (n : ℕ) : ℕ :=
  Nat.ceil (2 * (n : ℝ) ^ (9 / 10 : ℝ))

theorem initial_outer_radius_upper (n : ℕ) :
    (initial_outer_radius n : ℝ) ≤
      2 * (n : ℝ) ^ (9 / 10 : ℝ) + 1 := by
  exact (Nat.ceil_lt_add_one (by positivity :
    0 ≤ 2 * (n : ℝ) ^ (9 / 10 : ℝ))).le

/-- The chosen radius covers six times the initial vertex-degree scale. -/
theorem initial_outer_radius_cube_lower (n : ℕ) :
    6 * (n : ℝ) ^ (27 / 10 : ℝ) ≤ (initial_outer_radius n : ℝ) ^ 3 := by
  have hCeil : 2 * (n : ℝ) ^ (9 / 10 : ℝ) ≤ initial_outer_radius n :=
    Nat.le_ceil _
  have hNonneg : 0 ≤ 2 * (n : ℝ) ^ (9 / 10 : ℝ) := by positivity
  have hPow : (2 * (n : ℝ) ^ (9 / 10 : ℝ)) ^ 3 =
      8 * (n : ℝ) ^ (27 / 10 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ))]
    norm_num
  calc
    6 * (n : ℝ) ^ (27 / 10 : ℝ) ≤
        (2 * (n : ℝ) ^ (9 / 10 : ℝ)) ^ 3 := by
      rw [hPow]
      have hp : 0 ≤ (n : ℝ) ^ (27 / 10 : ℝ) := by positivity
      linarith
    _ ≤ (initial_outer_radius n : ℝ) ^ 3 :=
      pow_le_pow_left₀ hNonneg hCeil 3

/-- The initial cover loses fewer than all but six vertices for large `n`. -/
theorem eventually_initial_outer_ground_at_least_six :
    ∀ᶠ n : ℕ in atTop, ∀ U : Edge (Fin n),
      (n : ℝ) - U.card ≤ 134 * (n : ℝ) ^ (2 / 5 : ℝ) →
      6 ≤ U.card := by
  have hGrow : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 5 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hGrow.eventually (eventually_ge_atTop 268),
    eventually_ge_atTop (12 : ℕ)] with n hPow hn12
  intro U hMissing
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (by omega : 0 < n)
  have hIdentity : (n : ℝ) ^ (2 / 5 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) = n := by
    rw [← Real.rpow_add hnPos]
    norm_num
  have hBound : 268 * (n : ℝ) ^ (2 / 5 : ℝ) ≤ n := by
    nlinarith only [mul_le_mul_of_nonneg_left hPow (by positivity :
      0 ≤ (n : ℝ) ^ (2 / 5 : ℝ)), hIdentity]
  have hn12R : (12 : ℝ) ≤ n := by exact_mod_cast hn12
  have hCard : ((U.card : ℕ) : ℝ) ≥ 6 := by
    linarith only [hMissing, hBound, hn12R]
  exact_mod_cast hCard

/-- Combine the high-vertex and heavy-triple cover bounds into the
single exponent used by the explicit outer-loss budget. -/
theorem initial_outer_cover_sum_bound
    (n z x : ℕ) (hn : 1 ≤ n)
    (hZ : (z : ℝ) ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ))
    (hX : (x : ℝ) ≤ 6 * (n : ℝ) ^ (2 / 5 : ℝ)) :
    ((z + x : ℕ) : ℝ) ≤ 134 * (n : ℝ) ^ (2 / 5 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPower : (n : ℝ) ^ (3 / 10 : ℝ) ≤
      (n : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  push_cast
  linarith

/-- The outer budget is `o(n³)` under the exact exponents of §III.A.3. -/
theorem initial_outer_polynomial_budget_choose_ratio_tendsto_zero
    (z x radius : ℕ → ℕ)
    (hCover : ∀ᶠ n : ℕ in atTop,
      ((z n + x n : ℕ) : ℝ) ≤ 134 * (n : ℝ) ^ (2 / 5 : ℝ))
    (hRadius : ∀ᶠ n : ℕ in atTop,
      (radius n : ℝ) ≤ 2 * (n : ℝ) ^ (9 / 10 : ℝ) + 1) :
    Filter.Tendsto
      (fun n : ℕ => (initial_outer_polynomial_budget n (z n) (x n) (radius n) : ℝ) /
        (n.choose 3 : ℝ)) atTop (nhds 0) := by
  apply nonnegative_cubic_error_choose_ratio_tendsto_zero _ (fun _ => by positivity)
  have hPower : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 10 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  have hUpper : Tendsto (fun n : ℕ => 36454 * (n : ℝ) ^ (-(1 / 10 : ℝ)))
      atTop (nhds 0) := by simpa using hPower.const_mul 36454
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hUpper
  filter_upwards [hCover, hRadius, eventually_ge_atTop (1 : ℕ)]
    with n hCoverN hRadiusN hn1
  let N : ℝ := n
  let s : ℕ := z n + x n
  have hNpos : 0 < N := by
    change (0 : ℝ) < n
    exact_mod_cast (by omega : 0 < n)
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast hn1
  have hNsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt N := by
    have hNat : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ N := by
      dsimp [N]
      exact_mod_cast Nat.sqrt_le' n
    have hReal := Real.sq_sqrt hNpos.le
    nlinarith [Real.sqrt_nonneg N]
  have hSqrtOne : 1 ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hN1
  have hSqrtBound : (Nat.sqrt n : ℝ) + 1 ≤ 2 * N ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    linarith
  have hP04nonneg : 0 ≤ N ^ (2 / 5 : ℝ) := by positivity
  have hP05nonneg : 0 ≤ N ^ (1 / 2 : ℝ) := by positivity
  have hP09one : 1 ≤ N ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hPowSquare : (N ^ (2 / 5 : ℝ)) ^ 2 = N ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast hNpos.le]
    norm_num
  have hPowProd : N ^ (2 / 5 : ℝ) * N ^ (1 / 2 : ℝ) =
      N ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hPowCompare : N ^ (4 / 5 : ℝ) ≤ N ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hsBound : (s : ℝ) ≤ 134 * N ^ (2 / 5 : ℝ) := hCoverN
  have hsSquare : (s : ℝ) ^ 2 ≤ 17956 * N ^ (9 / 10 : ℝ) := by
    have hSquare := pow_le_pow_left₀ (Nat.cast_nonneg s) hsBound 2
    rw [mul_pow, hPowSquare] at hSquare
    nlinarith only [hSquare, hPowCompare]
  have hsCross : (s : ℝ) * ((Nat.sqrt n : ℝ) + 1) ≤
      268 * N ^ (9 / 10 : ℝ) := by
    calc
      _ ≤ (134 * N ^ (2 / 5 : ℝ)) * (2 * N ^ (1 / 2 : ℝ)) :=
        mul_le_mul hsBound hSqrtBound (by positivity) (by positivity)
      _ = 268 * N ^ (9 / 10 : ℝ) := by rw [← hPowProd]; ring
  have hRadiusPlus : (radius n : ℝ) + 3 ≤ 6 * N ^ (9 / 10 : ℝ) := by
    dsimp [N] at hRadiusN ⊢
    linarith [hP09one]
  have hInside : 2 * (s : ℝ) ^ 2 +
      2 * (s : ℝ) * ((Nat.sqrt n : ℝ) + 1) + (radius n : ℝ) + 3 ≤
      36454 * N ^ (9 / 10 : ℝ) := by
    nlinarith only [hsSquare, hsCross, hRadiusPlus]
  have hChoose : s.choose 2 + (x n).choose 2 ≤ 2 * s ^ 2 := by
    have h1 := Nat.choose_le_pow s 2
    have h2 := Nat.choose_le_pow (x n) 2
    have h3 : (x n) ^ 2 ≤ s ^ 2 :=
      Nat.pow_le_pow_left (by dsimp [s]; omega) 2
    omega
  have hNat : initial_outer_polynomial_budget n (z n) (x n) (radius n) ≤
      (2 * s ^ 2 + 2 * s * (Nat.sqrt n + 1) + radius n + 3) * n ^ 2 := by
    have hAdd : s.choose 2 + (x n).choose 2 +
        (2 * s * (Nat.sqrt n + 1) + radius n + 3) ≤
        2 * s ^ 2 + (2 * s * (Nat.sqrt n + 1) + radius n + 3) :=
      Nat.add_le_add_right hChoose _
    calc
      initial_outer_polynomial_budget n (z n) (x n) (radius n) =
          (s.choose 2 + (x n).choose 2 +
            (2 * s * (Nat.sqrt n + 1) + radius n + 3)) * n ^ 2 := by
        dsimp [initial_outer_polynomial_budget, s]
        ring
      _ ≤ _ := by
        simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (n ^ 2) hAdd
  have hReal : (initial_outer_polynomial_budget n (z n) (x n) (radius n) : ℝ) ≤
      (2 * (s : ℝ) ^ 2 + 2 * (s : ℝ) * ((Nat.sqrt n : ℝ) + 1) +
        (radius n : ℝ) + 3) * N ^ 2 := by
    calc
      (initial_outer_polynomial_budget n (z n) (x n) (radius n) : ℝ) ≤
          (((2 * s ^ 2 + 2 * s * (Nat.sqrt n + 1) + radius n + 3) * n ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hNat
      _ = _ := by push_cast; ring
  have hNumerator :
      (initial_outer_polynomial_budget n (z n) (x n) (radius n) : ℝ) ≤
      36454 * N ^ (9 / 10 : ℝ) * N ^ 2 :=
    hReal.trans (mul_le_mul_of_nonneg_right hInside (by positivity))
  have hDiv := div_le_div_of_nonneg_right hNumerator (by positivity : 0 ≤ N ^ 3)
  have hPowerQuot : N ^ (9 / 10 : ℝ) / N = N ^ (-(1 / 10 : ℝ)) := by
    have h := Real.rpow_sub hNpos (9 / 10 : ℝ) (1 : ℝ)
    norm_num at h
    simpa only [Real.rpow_one] using h.symm
  have hEq : (36454 * N ^ (9 / 10 : ℝ) * N ^ 2) / N ^ 3 =
      36454 * N ^ (-(1 / 10 : ℝ)) := by
    rw [← hPowerQuot]
    field_simp
  simpa only [hEq] using hDiv

end JSP523.Rank4
