import JSP523.Rank5.StructuralFinite
import Mathlib.Data.Nat.Choose.Bounds

namespace JSP523.Rank5

private theorem scale_monomial_bound (n U : ℝ) (hU : 1 ≤ U)
    (hn : U ^ 32 ≤ n) (k : ℕ) (hk : k + 1 ≤ 32) :
    U ^ k * n ^ 3 ≤ n ^ 4 / U := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 ≤ n := (by positivity : 0 ≤ U ^ 32).trans hn
  apply (le_div_iff₀ hUp).2
  have hp : U ^ (k + 1) ≤ n := (pow_le_pow_right₀ hU hk).trans hn
  calc
    U ^ k * n ^ 3 * U = U ^ (k + 1) * n ^ 3 := by rw [pow_succ]; ring
    _ ≤ n * n ^ 3 := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = n ^ 4 := by ring

private theorem scale_fourth_div_bound (n U : ℝ) (hU : 1 ≤ U)
    (k : ℕ) (hk : 1 ≤ k) : n ^ 4 / U ^ k ≤ n ^ 4 / U := by
  apply div_le_div_of_nonneg_left (by positivity) (by linarith)
  simpa using pow_le_pow_right₀ hU hk

/-- Real-valued envelope for the lower cleanup at the integer scales. -/
theorem lower_cleanup_scale_envelope
    (n m U t u q : ℝ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n)
    (hm : 0 ≤ m) (ht0 : 0 < t) (_hu0 : 0 < u) (_hq0 : 0 < q)
    (ht : n / (2 * U ^ 12) ≤ t) (htu : t ≤ n / U ^ 12)
    (hu : n / (2 * U ^ 4) ≤ u) (huu : u ≤ n / U ^ 4)
    (hq : n / (2 * U ^ 8) ≤ q) :
    n ^ 3 * u +
      (10 * m + 3200 *
        (n ^ 4 * (t + 36 * U ^ 2) + 80 * U ^ 2 * m +
          64 * U ^ 6 * n ^ 6 / (t * u))) / q ≤
      1875201 * (n ^ 4 / U) + 512020 * (m / U) := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have htu0 : 0 < n / (2 * U ^ 12) := by positivity
  have huu0 : 0 < n / (2 * U ^ 4) := by positivity
  have hqu0 : 0 < n / (2 * U ^ 8) := by positivity
  have hBound :
      n ^ 3 * u +
        (10 * m + 3200 *
          (n ^ 4 * (t + 36 * U ^ 2) + 80 * U ^ 2 * m +
            64 * U ^ 6 * n ^ 6 / (t * u))) / q ≤
      n ^ 3 * (n / U ^ 4) +
        (10 * m + 3200 *
          (n ^ 4 * (n / U ^ 12 + 36 * U ^ 2) + 80 * U ^ 2 * m +
            64 * U ^ 6 * n ^ 6 /
              ((n / (2 * U ^ 12)) * (n / (2 * U ^ 4))))) /
          (n / (2 * U ^ 8)) := by
    gcongr
  have hId :
      n ^ 3 * (n / U ^ 4) +
        (10 * m + 3200 *
          (n ^ 4 * (n / U ^ 12 + 36 * U ^ 2) + 80 * U ^ 2 * m +
            64 * U ^ 6 * n ^ 6 /
              ((n / (2 * U ^ 12)) * (n / (2 * U ^ 4))))) /
          (n / (2 * U ^ 8)) =
      n ^ 4 / U ^ 4 + 6400 * (n ^ 4 / U ^ 4) +
        230400 * (U ^ 10 * n ^ 3) + 1638400 * (U ^ 30 * n ^ 3) +
        20 * (m * U ^ 8 / n) + 512000 * (m * U ^ 10 / n) := by
    field_simp
    ring
  rw [hId] at hBound
  have h4 := scale_fourth_div_bound n U hU 4 (by omega)
  have h10 := scale_monomial_bound n U hU hn 10 (by omega)
  have h30 := scale_monomial_bound n U hU hn 30 (by omega)
  have h8m : m * U ^ 8 / n ≤ m / U := by
    apply (div_le_div_iff₀ hn0 hUp).2
    have hp : U ^ 9 ≤ n := (pow_le_pow_right₀ hU (by omega : 9 ≤ 32)).trans hn
    nlinarith [mul_le_mul_of_nonneg_left hp hm]
  have h10m : m * U ^ 10 / n ≤ m / U := by
    apply (div_le_div_iff₀ hn0 hUp).2
    have hp : U ^ 11 ≤ n := (pow_le_pow_right₀ hU (by omega : 11 ≤ 32)).trans hn
    nlinarith [mul_le_mul_of_nonneg_left hp hm]
  linarith

theorem upper_cleanup_scale_envelope
    (n U t : ℝ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n)
    (ht : n ^ 2 / (2 * U ^ 12) ≤ t) (htu : t ≤ n ^ 2 / U ^ 12) :
    2 * n ^ 2 * (t + 64 * U ^ 2 * n) + 12 * U ^ 2 * n ^ 3 +
      576 * U ^ 6 * n ^ 5 / t ≤ 1294 * (n ^ 4 / U) := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have ht0 : 0 < n ^ 2 / (2 * U ^ 12) := by positivity
  have hBound :
      2 * n ^ 2 * (t + 64 * U ^ 2 * n) + 12 * U ^ 2 * n ^ 3 +
        576 * U ^ 6 * n ^ 5 / t ≤
      2 * n ^ 2 * (n ^ 2 / U ^ 12 + 64 * U ^ 2 * n) +
        12 * U ^ 2 * n ^ 3 +
        576 * U ^ 6 * n ^ 5 / (n ^ 2 / (2 * U ^ 12)) := by gcongr
  have hId :
      2 * n ^ 2 * (n ^ 2 / U ^ 12 + 64 * U ^ 2 * n) +
        12 * U ^ 2 * n ^ 3 +
        576 * U ^ 6 * n ^ 5 / (n ^ 2 / (2 * U ^ 12)) =
      2 * (n ^ 4 / U ^ 12) + 140 * (U ^ 2 * n ^ 3) +
        1152 * (U ^ 18 * n ^ 3) := by field_simp; ring
  rw [hId] at hBound
  have h12 := scale_fourth_div_bound n U hU 12 (by omega)
  have h2 := scale_monomial_bound n U hU hn 2 (by omega)
  have h18 := scale_monomial_bound n U hU hn 18 (by omega)
  linarith

theorem inheritance_scale_envelope
    (n m U t q : ℝ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n)
    (hm : 0 ≤ m) (ht0 : 0 < t)
    (ht : n / (2 * U ^ 12) ≤ t) (hq : n / (2 * U ^ 8) ≤ q) :
    640 * m / U ^ 4 + 64 * U ^ 6 * n ^ 5 / (t * q) ≤
      640 * (m / U) + 256 * (n ^ 4 / U) := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have htLo : 0 < n / (2 * U ^ 12) := by positivity
  have hqLo : 0 < n / (2 * U ^ 8) := by positivity
  have hBound : 64 * U ^ 6 * n ^ 5 / (t * q) ≤
      64 * U ^ 6 * n ^ 5 /
        ((n / (2 * U ^ 12)) * (n / (2 * U ^ 8))) := by gcongr
  have hId : 64 * U ^ 6 * n ^ 5 /
      ((n / (2 * U ^ 12)) * (n / (2 * U ^ 8))) =
        256 * (U ^ 26 * n ^ 3) := by field_simp; ring
  rw [hId] at hBound
  have h26 := scale_monomial_bound n U hU hn 26 (by omega)
  have h4 : m / U ^ 4 ≤ m / U := by
    apply div_le_div_of_nonneg_left hm hUp
    simpa using pow_le_pow_right₀ hU (by omega : 1 ≤ 4)
  simp only [mul_div_assoc] at hBound ⊢
  linarith

theorem prefix_scale_envelope
    (n U : ℝ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n) :
    8 * U ^ 2 * n ^ 3 + Real.sqrt (n ^ 7 * max 7 (1 + 8 * n / U ^ 2)) ≤
      11 * (n ^ 4 / U) := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have h2 : U ^ 2 ≤ n := (pow_le_pow_right₀ hU (by omega : 2 ≤ 32)).trans hn
  have hRatio : 1 ≤ n / U ^ 2 := (le_div_iff₀ (by positivity)).2 (by simpa using h2)
  have hMax : max 7 (1 + 8 * n / U ^ 2) ≤ 9 * n / U ^ 2 := by
    simp only [mul_div_assoc]
    apply max_le <;> linarith
  have hRad : n ^ 7 * max 7 (1 + 8 * n / U ^ 2) ≤ (3 * (n ^ 4 / U)) ^ 2 := by
    calc
      _ ≤ n ^ 7 * (9 * n / U ^ 2) := mul_le_mul_of_nonneg_left hMax (by positivity)
      _ = _ := by field_simp; ring
  have hSqrt : Real.sqrt (n ^ 7 * max 7 (1 + 8 * n / U ^ 2)) ≤ 3 * (n ^ 4 / U) := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity, hRad⟩
  have hMono := scale_monomial_bound n U hU hn 2 (by omega)
  linarith

/-- The entire structural error vanishes at the common integer scale.
The parent mass is retained explicitly, so no upper bound on it is needed. -/
theorem rank_five_structural_error_scale_bound
    (n m U tLower tUpper u q : ℕ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n)
    (ht0 : 0 < tLower) (hu0 : 0 < u) (hq0 : 0 < q)
    (ht : (n : ℝ) / (2 * (U : ℝ) ^ 12) ≤ tLower)
    (htu : (tLower : ℝ) ≤ n / (U : ℝ) ^ 12)
    (hT : (n : ℝ) ^ 2 / (2 * (U : ℝ) ^ 12) ≤ tUpper)
    (hTu : (tUpper : ℝ) ≤ (n : ℝ) ^ 2 / (U : ℝ) ^ 12)
    (hu : (n : ℝ) / (2 * (U : ℝ) ^ 4) ≤ u)
    (huu : (u : ℝ) ≤ n / (U : ℝ) ^ 4)
    (hq : (n : ℝ) / (2 * (U : ℝ) ^ 8) ≤ q) :
    rankFiveStructuralError n m 16 (U ^ 4) (4 * q) tLower tUpper u q
      (4 * U ^ 2 * n ^ 2) (4 * U ^ 2 * n) (4 * U ^ 2) (2 / (U : ℝ) ^ 4) ≤
      1900000 * ((n : ℝ) ^ 4 / U) + 513000 * ((m : ℝ) / U) := by
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hnr : (U : ℝ) ^ 32 ≤ n := by exact_mod_cast hn
  have hUp : (0 : ℝ) < U := by linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnr
  have ht0r : (0 : ℝ) < tLower := by exact_mod_cast ht0
  have hu0r : (0 : ℝ) < u := by exact_mod_cast hu0
  have hq0r : (0 : ℝ) < q := by exact_mod_cast hq0
  have hC2 : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow n 2
  have hC3 : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast Nat.choose_le_pow n 3
  have hCN : ((n - 2).choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (Nat.choose_le_pow (n - 2) 2).trans (Nat.pow_le_pow_left (Nat.sub_le n 2) 2)
  have hLower : rankFiveLowerCleanupCost n m tLower u q (4 * U ^ 2 * n) (4 * U ^ 2) ≤
      1875201 * ((n : ℝ) ^ 4 / U) + 512020 * ((m : ℝ) / U) := by
    have h := lower_cleanup_scale_envelope n m U tLower u q hUr hnr
      (by positivity) ht0r hu0r hq0r ht htu hu huu hq
    refine le_trans ?_ h
    dsimp [rankFiveLowerCleanupCost]
    push_cast
    calc
      _ ≤ (n : ℝ) ^ 3 * u +
          (10 * (m : ℝ) + 3200 *
            (((n : ℝ) ^ 2) ^ 2 * ((tLower : ℝ) + 9 * (4 * (U : ℝ) ^ 2)) +
              20 * (4 * (U : ℝ) ^ 2) * m +
              ((n : ℝ) ^ 2) ^ 2 * (4 * (U : ℝ) ^ 2 * n) *
                (4 * (U : ℝ) ^ 2 * n) * (4 * (U : ℝ) ^ 2) /
                  ((tLower : ℝ) * u))) / q := by gcongr
      _ = _ := by ring
  have hUpper : rankFiveUpperCleanupCost n tUpper
      (4 * U ^ 2 * n ^ 2) (4 * U ^ 2 * n) (4 * U ^ 2) ≤
      1294 * ((n : ℝ) ^ 4 / U) := by
    convert upper_cleanup_scale_envelope n U tUpper hUr hnr hT hTu using 1
    dsimp [rankFiveUpperCleanupCost]
    push_cast
    ring
  have hInherit : rankFiveInheritanceCost n m 16 (U ^ 4) (4 * q) tLower
      (4 * U ^ 2 * n) (4 * U ^ 2) ≤
      640 * ((m : ℝ) / U) + 256 * ((n : ℝ) ^ 4 / U) := by
    have h := inheritance_scale_envelope n m U tLower q hUr hnr
      (by positivity) ht0r ht hq
    refine le_trans ?_ h
    dsimp [rankFiveInheritanceCost]
    push_cast
    calc
      _ ≤ 40 * 16 * (m : ℝ) / (U : ℝ) ^ 4 +
          4 * ((n : ℝ) ^ 2) ^ 2 * (4 * (U : ℝ) ^ 2 * n) *
            (4 * (U : ℝ) ^ 2) * (4 * (U : ℝ) ^ 2) / ((tLower : ℝ) * (4 * q)) := by
        gcongr
      _ = _ := by ring
  have hPrefix : rankFivePrefixCost n (4 * U ^ 2 * n) (4 * U ^ 2)
      (2 / (U : ℝ) ^ 4) ≤ 11 * ((n : ℝ) ^ 4 / U) := by
    have h := prefix_scale_envelope n U hUr hnr
    refine le_trans ?_ h
    have hD : ((1 + 2 * (4 * U ^ 2 - 1) : ℕ) : ℝ) ≤ 8 * (U : ℝ) ^ 2 := by
      have hNat : 1 + 2 * (4 * U ^ 2 - 1) ≤ 8 * U ^ 2 := by
        have : 1 ≤ U ^ 2 := Nat.one_le_pow 2 U hU
        omega
      exact_mod_cast hNat
    have hId : (2 / (U : ℝ) ^ 4) * (4 * (U : ℝ) ^ 2 * n) =
        8 * (n : ℝ) / (U : ℝ) ^ 2 := by field_simp; ring
    push_cast at hD
    dsimp [rankFivePrefixCost]
    push_cast
    rw [hId]
    calc
      _ ≤ (n : ℝ) ^ 3 * (8 * (U : ℝ) ^ 2) +
        Real.sqrt ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2 * (n : ℝ) ^ 2) *
          max 7 (1 + 8 * (n : ℝ) / (U : ℝ) ^ 2)) := by gcongr
      _ = _ := by
        congr 1
        · ring
        · congr 1
          ring
  dsimp [rankFiveStructuralError]
  have hN : 0 ≤ (n : ℝ) ^ 4 / U := by positivity
  have hM : 0 ≤ (m : ℝ) / U := by positivity
  linarith

end JSP523.Rank5
