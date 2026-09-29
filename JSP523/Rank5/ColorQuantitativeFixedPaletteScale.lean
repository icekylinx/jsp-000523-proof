import JSP523.Rank5.ColorQuantitativeFixedPaletteBudget

/-! # Real error envelope for the higher-rank majority cleanups

Writing the core and root powers as `x * n³` and `y * n²`
keeps the same arithmetic proof valid at both root sizes two and three.
-/

namespace JSP523.Rank5

private theorem palette_scale_monomial_bound (n U : ℝ) (hU : 1 ≤ U)
    (hn : U ^ 32 ≤ n) (j : ℕ) (hj : j + 1 ≤ 32) :
    U ^ j * n ^ 3 ≤ n ^ 4 / U := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 ≤ n := (by positivity : 0 ≤ U ^ 32).trans hn
  apply (le_div_iff₀ hUp).2
  have hp : U ^ (j + 1) ≤ n := (pow_le_pow_right₀ hU hj).trans hn
  calc
    U ^ j * n ^ 3 * U = U ^ (j + 1) * n ^ 3 := by rw [pow_succ]; ring
    _ ≤ n * n ^ 3 := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = n ^ 4 := by ring

/-- At the common higher-rank integer scales the full majority-cleanup
cost has only inverse-`U` ambient and mass errors. Here `x=n^(k-3)` and
`y=n^(s-2)`, while `B=choose(r,k)` and `C` is the palette constant. -/
theorem fixed_palette_cleanup_scale_envelope
    (n m U x y B C s k t u q : ℝ)
    (hU : 1 ≤ U) (hn : U ^ 32 ≤ n) (hm : 0 ≤ m)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hs : 0 ≤ s) (hk : 0 ≤ k) (ht0 : 0 < t)
    (ht : x * n / (2 * U ^ 9) ≤ t) (htu : t ≤ x * n / U ^ 9)
    (hu : y * n / (2 * U ^ 3) ≤ u) (huu : u ≤ y * n / U ^ 3)
    (hq : y * n / (2 * U ^ 6) ≤ q) :
    x * n ^ 3 * u +
      (B * m + 4 * C *
        ((y * n ^ 2) ^ 2 * (t + k * k * (4 * U ^ 2 * x)) +
          s * B * (4 * U ^ 2 * y) * m +
          (y * n ^ 2) ^ 2 * (4 * U ^ 2 * x * n) *
            (4 * U ^ 2 * y * n) * (4 * U ^ 2 * x) / (t * u))) / q ≤
      (1 + (2056 + 32 * k * k) * C) * (x * y * n ^ 4 / U) +
        (2 * B + 32 * C * s * B) * (m / U) := by
  have hUp : 0 < U := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have htLo : 0 < x * n / (2 * U ^ 9) := by positivity
  have huLo : 0 < y * n / (2 * U ^ 3) := by positivity
  have hqLo : 0 < y * n / (2 * U ^ 6) := by positivity
  have hBound :
      x * n ^ 3 * u +
        (B * m + 4 * C *
          ((y * n ^ 2) ^ 2 * (t + k * k * (4 * U ^ 2 * x)) +
            s * B * (4 * U ^ 2 * y) * m +
            (y * n ^ 2) ^ 2 * (4 * U ^ 2 * x * n) *
              (4 * U ^ 2 * y * n) * (4 * U ^ 2 * x) / (t * u))) / q ≤
      x * n ^ 3 * (y * n / U ^ 3) +
        (B * m + 4 * C *
          ((y * n ^ 2) ^ 2 * (x * n / U ^ 9 + k * k * (4 * U ^ 2 * x)) +
            s * B * (4 * U ^ 2 * y) * m +
            (y * n ^ 2) ^ 2 * (4 * U ^ 2 * x * n) *
              (4 * U ^ 2 * y * n) * (4 * U ^ 2 * x) /
                ((x * n / (2 * U ^ 9)) * (y * n / (2 * U ^ 3))))) /
          (y * n / (2 * U ^ 6)) := by gcongr
  have hId :
      x * n ^ 3 * (y * n / U ^ 3) +
        (B * m + 4 * C *
          ((y * n ^ 2) ^ 2 * (x * n / U ^ 9 + k * k * (4 * U ^ 2 * x)) +
            s * B * (4 * U ^ 2 * y) * m +
            (y * n ^ 2) ^ 2 * (4 * U ^ 2 * x * n) *
              (4 * U ^ 2 * y * n) * (4 * U ^ 2 * x) /
                ((x * n / (2 * U ^ 9)) * (y * n / (2 * U ^ 3))))) /
          (y * n / (2 * U ^ 6)) =
      x * y * n ^ 4 / U ^ 3 + 2 * B * (m * U ^ 6 / (y * n)) +
        8 * C * (x * y * n ^ 4 / U ^ 3) +
        32 * C * k * k * (x * y * (U ^ 8 * n ^ 3)) +
        32 * C * s * B * (m * U ^ 8 / n) +
        2048 * C * (x * y * (U ^ 24 * n ^ 3)) := by
    field_simp
    ring
  rw [hId] at hBound
  have hBase : x * y * n ^ 4 / U ^ 3 ≤ x * y * n ^ 4 / U := by
    apply div_le_div_of_nonneg_left (by positivity) hUp
    simpa using pow_le_pow_right₀ hU (by decide : 1 ≤ 3)
  have h8 := mul_le_mul_of_nonneg_left (palette_scale_monomial_bound n U hU hn 8 (by decide))
    (show 0 ≤ x * y by positivity)
  have h24 := mul_le_mul_of_nonneg_left (palette_scale_monomial_bound n U hU hn 24 (by decide))
    (show 0 ≤ x * y by positivity)
  rw [← mul_div_assoc] at h8 h24
  have h6m : m * U ^ 6 / (y * n) ≤ m / U := by
    apply (div_le_div_iff₀ (by positivity) hUp).2
    have hp : U ^ 7 ≤ n := (pow_le_pow_right₀ hU (by decide : 7 ≤ 32)).trans hn
    have hny : n ≤ y * n := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (hp.trans hny) hm]
  have h8m : m * U ^ 8 / n ≤ m / U := by
    apply (div_le_div_iff₀ hn0 hUp).2
    have hp : U ^ 9 ≤ n := (pow_le_pow_right₀ hU (by decide : 9 ≤ 32)).trans hn
    nlinarith [mul_le_mul_of_nonneg_left hp hm]
  calc
    _ ≤ x * y * n ^ 4 / U ^ 3 + 2 * B * (m * U ^ 6 / (y * n)) +
        8 * C * (x * y * n ^ 4 / U ^ 3) +
        32 * C * k * k * (x * y * (U ^ 8 * n ^ 3)) +
        32 * C * s * B * (m * U ^ 8 / n) +
        2048 * C * (x * y * (U ^ 24 * n ^ 3)) := hBound
    _ ≤ x * y * n ^ 4 / U + 2 * B * (m / U) +
        8 * C * (x * y * n ^ 4 / U) +
        32 * C * k * k * (x * y * n ^ 4 / U) +
        32 * C * s * B * (m / U) +
        2048 * C * (x * y * n ^ 4 / U) := by gcongr
    _ = _ := by ring

def fixedPaletteAmbientErrorConstant (k : ℕ) : ℕ :=
  1 + (2056 + 32 * k * k) * fixedPaletteMajorityConstant (fixedPaletteSampleSize k)

def fixedPaletteMassErrorConstant (r s k : ℕ) : ℕ :=
  2 * r.choose k +
    32 * fixedPaletteMajorityConstant (fixedPaletteSampleSize k) * s * r.choose k

/-- The real envelope bounds the actual numerical cleanup cost, with
all binomial coefficients and integer codegree caps present. -/
theorem fixed_palette_cleanup_cost_scale_bound
    (n m U r s k t u q : ℕ) (hU : 1 ≤ U) (hn : U ^ 32 ≤ n)
    (hs : 2 ≤ s) (hk : 3 ≤ k) (ht0 : 0 < t)
    (ht : (n : ℝ) ^ (k - 2) / (2 * (U : ℝ) ^ 9) ≤ t)
    (htu : (t : ℝ) ≤ (n : ℝ) ^ (k - 2) / (U : ℝ) ^ 9)
    (hu : (n : ℝ) ^ (s - 1) / (2 * (U : ℝ) ^ 3) ≤ u)
    (huu : (u : ℝ) ≤ (n : ℝ) ^ (s - 1) / (U : ℝ) ^ 3)
    (hq : (n : ℝ) ^ (s - 1) / (2 * (U : ℝ) ^ 6) ≤ q) :
    fixedPaletteCleanupCost n m r s k t u q
      (4 * U ^ 2 * n ^ (k - 2)) (4 * U ^ 2 * n ^ (k - 3))
      (4 * U ^ 2 * n ^ (s - 1)) (4 * U ^ 2 * n ^ (s - 2)) ≤
      (fixedPaletteAmbientErrorConstant k : ℝ) * ((n : ℝ) ^ (k + s - 1) / U) +
        (fixedPaletteMassErrorConstant r s k : ℝ) * ((m : ℝ) / U) := by
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hnr : (U : ℝ) ^ 32 ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := (one_le_pow₀ hUr).trans hnr
  have hPowK : (n : ℝ) ^ k = (n : ℝ) ^ (k - 3) * (n : ℝ) ^ 3 := by
    rw [← pow_add]; congr 1; omega
  have hPowS : (n : ℝ) ^ s = (n : ℝ) ^ (s - 2) * (n : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hPowKminus : (n : ℝ) ^ (k - 2) = (n : ℝ) ^ (k - 3) * n := by
    rw [← pow_succ]; congr 1; omega
  have hPowSminus : (n : ℝ) ^ (s - 1) = (n : ℝ) ^ (s - 2) * n := by
    rw [← pow_succ]; congr 1; omega
  have hPowTotal : (n : ℝ) ^ (k + s - 1) =
      (n : ℝ) ^ (k - 3) * (n : ℝ) ^ (s - 2) * (n : ℝ) ^ 4 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h := fixed_palette_cleanup_scale_envelope n m U
    ((n : ℝ) ^ (k - 3)) ((n : ℝ) ^ (s - 2)) (r.choose k)
    (fixedPaletteMajorityConstant (fixedPaletteSampleSize k)) s k t u q
    hUr hnr (Nat.cast_nonneg m) (one_le_pow₀ hn1) (one_le_pow₀ hn1)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast ht0)
    (by simpa only [hPowKminus] using ht) (by simpa only [hPowKminus] using htu)
    (by simpa only [hPowSminus] using hu) (by simpa only [hPowSminus] using huu)
    (by simpa only [hPowSminus] using hq)
  have hCk : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  have hCs : (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by exact_mod_cast Nat.choose_le_pow n s
  have hUp : (0 : ℝ) < U := by linarith
  have hnPos : (0 : ℝ) < n := by linarith
  have htPos : (0 : ℝ) < t := by exact_mod_cast ht0
  have huPos : (0 : ℝ) < u := lt_of_lt_of_le (by positivity) hu
  have hqPos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
  have hCost : fixedPaletteCleanupCost n m r s k t u q
      (4 * U ^ 2 * n ^ (k - 2)) (4 * U ^ 2 * n ^ (k - 3))
      (4 * U ^ 2 * n ^ (s - 1)) (4 * U ^ 2 * n ^ (s - 2)) ≤
      (n : ℝ) ^ k * u +
        ((r.choose k : ℝ) * m +
          4 * (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ) *
            (((n : ℝ) ^ s) ^ 2 * ((t : ℝ) + (k : ℝ) * k * (4 * (U : ℝ) ^ 2 * (n : ℝ) ^ (k - 3))) +
              (s : ℝ) * r.choose k * (4 * (U : ℝ) ^ 2 * (n : ℝ) ^ (s - 2)) * m +
              (((n : ℝ) ^ s) ^ 2 * (4 * (U : ℝ) ^ 2 * (n : ℝ) ^ (k - 2)) *
                (4 * (U : ℝ) ^ 2 * (n : ℝ) ^ (s - 1)) * (4 * (U : ℝ) ^ 2 * (n : ℝ) ^ (k - 3)) /
                  ((t : ℝ) * u)))) / q := by
    dsimp [fixedPaletteCleanupCost]
    push_cast
    gcongr
  rw [hPowK, hPowS, hPowKminus, hPowSminus] at hCost
  have hTotal := hCost.trans (by convert h using 1; ring)
  simpa only [fixedPaletteAmbientErrorConstant, fixedPaletteMassErrorConstant,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hPowTotal] using hTotal

end JSP523.Rank5
