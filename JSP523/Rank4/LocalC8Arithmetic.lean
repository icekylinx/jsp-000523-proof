import JSP523.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Numerical contraction in the rank-four near-star estimate
-/

namespace JSP523.Rank4

/-- The coefficient displayed in (III.C.8) is below `11/12` throughout the
range `w ≥ 1000`, `10000 q ≤ w³`. -/
theorem c8_coefficient_le_eleven_twelfths
    {w q : ℝ} (hw : 1000 ≤ w) (hq0 : 0 ≤ q)
    (hq : 10000 * q ≤ w ^ 3) :
    2 / 3 + 205 / (4 * w) + 27 / 2 * Real.sqrt (q / w ^ 3) +
      480 * (q / w ^ 3) + 442368 * (q / w ^ 3) ^ 2 ≤ 11 / 12 := by
  have hwpos : 0 < w := by linarith
  have hw3pos : 0 < w ^ 3 := by positivity
  have hx : 0 ≤ q / w ^ 3 := div_nonneg hq0 (le_of_lt hw3pos)
  have hxsmall : q / w ^ 3 ≤ 1 / 10000 := by
    rw [div_le_iff₀ hw3pos]
    nlinarith [hq]
  have hroot : Real.sqrt (q / w ^ 3) ≤ 1 / 100 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
    nlinarith [hxsmall]
  have h205 : 205 / (4 * w) ≤ 205 / 4000 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * w)
      (by norm_num : (0 : ℝ) < 4000)).2
    nlinarith
  have h480 : 480 * (q / w ^ 3) ≤ 480 / 10000 := by
    nlinarith [hxsmall]
  have h442 : 442368 * (q / w ^ 3) ^ 2 ≤ 442368 / 100000000 := by
    have hx2 := mul_le_mul hxsmall hxsmall hx (by norm_num)
    nlinarith [hx2]
  have h27 : 27 / 2 * Real.sqrt (q / w ^ 3) ≤ 27 / 200 := by
    nlinarith [hroot]
  nlinarith [h205, h480, h442, h27]

/-- The rational conclusion of (III.C.8): the outside-edge count obeys the
coarse interface used to eliminate the exceptional sets. -/
theorem c8_implies_coarse_interface
    {w q b : ℕ} (hw : 1000 ≤ w) (hq : 10000 * q ≤ w ^ 3)
    (hC8 : (b : ℝ) ≤ (w : ℝ) / 4 + (q : ℝ) *
      (2 / 3 + 205 / (4 * w) +
        27 / 2 * Real.sqrt ((q : ℝ) / (w : ℝ) ^ 3) +
        480 * ((q : ℝ) / (w : ℝ) ^ 3) +
        442368 * ((q : ℝ) / (w : ℝ) ^ 3) ^ 2)) :
    12 * b ≤ 3 * w + 11 * q := by
  have hcoeff := c8_coefficient_le_eleven_twelfths
    (w := (w : ℝ)) (q := (q : ℝ)) (by exact_mod_cast hw) (by positivity)
    (by exact_mod_cast hq)
  have hmul := mul_le_mul_of_nonneg_left hcoeff (by positivity : (0 : ℝ) ≤ q)
  have hlin : (b : ℝ) ≤ w / 4 + 11 * q / 12 := by
    linarith [hC8, hmul]
  have hnat : (12 : ℝ) * b ≤ 3 * w + 11 * q := by
    nlinarith [hlin]
  exact_mod_cast hnat

end JSP523.Rank4
