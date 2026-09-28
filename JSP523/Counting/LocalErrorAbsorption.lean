import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-!
# Clearing denominators in the local error absorption

This is the finite arithmetic behind choosing a large ground set and a
small fixed-rank density in Theorem IV.2.1. A linear `q/w` error and a
quadratic `q²/w^(r-1)` error are each absorbed by a quarter of `q`.
-/

namespace JSP523.Counting

/-- A denominator-free polynomial error budget is absorbed once `w` is
large relative to the linear coefficient and `q` is small relative to
`w^(t+1)` and the quadratic coefficient. -/
theorem absorb_linear_quadratic_power_error
    (w q err A B t : ℕ)
    (hwPos : 0 < w)
    (hLarge : 4 * A ≤ w)
    (hSmall : 4 * B * q ≤ w ^ (t + 1))
    (hBudget : w ^ (t + 1) * err ≤
      A * q * w ^ t + B * q ^ 2) :
    2 * err ≤ q := by
  have hPowPos : 0 < w ^ (t + 1) := pow_pos hwPos _
  have hLinear : 4 * (A * q * w ^ t) ≤ w ^ (t + 1) * q := by
    have hMul := Nat.mul_le_mul_right (q * w ^ t) hLarge
    calc
      4 * (A * q * w ^ t) = (4 * A) * (q * w ^ t) := by ring
      _ ≤ w * (q * w ^ t) := hMul
      _ = w ^ (t + 1) * q := by
        conv_rhs => rw [pow_succ]
        ac_rfl
  have hQuadratic : 4 * (B * q ^ 2) ≤ w ^ (t + 1) * q := by
    have hMul := Nat.mul_le_mul_right q hSmall
    calc
      4 * (B * q ^ 2) = (4 * B * q) * q := by ring
      _ ≤ w ^ (t + 1) * q := hMul
  have hScaled := Nat.mul_le_mul_left 4 hBudget
  have hTotal : w ^ (t + 1) * (4 * err) ≤
      w ^ (t + 1) * (2 * q) := by
    calc
      w ^ (t + 1) * (4 * err) =
          4 * (w ^ (t + 1) * err) := by ring
      _ ≤ 4 * (A * q * w ^ t + B * q ^ 2) := hScaled
      _ = 4 * (A * q * w ^ t) + 4 * (B * q ^ 2) := by ring
      _ ≤ w ^ (t + 1) * q + w ^ (t + 1) * q :=
        Nat.add_le_add hLinear hQuadratic
      _ = w ^ (t + 1) * (2 * q) := by ring
  have hCancel : 4 * err ≤ 2 * q :=
    Nat.le_of_mul_le_mul_left hTotal hPowPos
  omega

/-- Translate the manuscript's real density condition with the explicit
choice `δ = 1/(4B)` into the integer inequality used above. -/
theorem real_density_implies_power_small
    (w q B t : ℕ) (hB : 0 < B)
    (hDensity : (q : ℝ) ≤
      (1 / (4 * B : ℕ) : ℝ) * (w : ℝ) ^ t) :
    4 * B * q ≤ w ^ t := by
  have hDen : (0 : ℝ) < (4 * B : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < 4) hB)
  have hDiv : (q : ℝ) ≤ (w : ℝ) ^ t / (4 * B : ℕ) := by
    simpa [div_eq_mul_inv, mul_comm] using hDensity
  have hCast : ((4 * B * q : ℕ) : ℝ) ≤ ((w ^ t : ℕ) : ℝ) := by
    have hMul := (le_div_iff₀ hDen).mp hDiv
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hMul
  exact_mod_cast hCast

end JSP523.Counting
