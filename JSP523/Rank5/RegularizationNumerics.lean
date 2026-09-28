import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Finite numerical gap for heavy-root packings

These lemmas isolate the finite numerical check used in the heavy-root
matching argument. Rounding is represented by explicit integer inequalities.
-/

namespace JSP523.Rank5

/-- A direct finite sufficient condition for the heavy-root gap. The
first and second error budgets each consume less than half of `n^t`, while
the available tail budget is at least `n^t`. -/
theorem heavy_root_gap_of_budgets
    (N C B a d : ℕ)
    (hChoose : 2 * C ≤ N)
    (hOverlap : 2 * B < N)
    (hTail : N ≤ a * d) :
    C + B < a * d := by omega

/-- Scale form with `d ≥ T n^(t-1)` and `D ≤ R n^(t-2)`. The explicit
overlap check is `2 a² t R n^(t-2) < n^t`; it is a finite integer version
of the manuscript condition `T²/R` large when `a` is about `n/T`. -/
theorem heavy_root_gap_of_scale_parameters
    (n t R T a d D : ℕ)
    (ht : 2 ≤ t)
    (hChoose : 2 * n.choose t ≤ n ^ t)
    (haLower : n ≤ a * T)
    (hd : T * n ^ (t - 1) ≤ d)
    (hD : D ≤ R * n ^ (t - 2))
    (hOverlapScale :
      2 * a * a * t * (R * n ^ (t - 2)) < n ^ t) :
    n.choose t + a * a * t * D < a * d := by
  have hTail : n ^ t ≤ a * d := by
    have hPower : n * n ^ (t - 1) = n ^ t := by
      calc
        n * n ^ (t - 1) = n ^ (t - 1) * n := by ac_rfl
        _ = n ^ ((t - 1) + 1) := (pow_succ n (t - 1)).symm
        _ = n ^ t := by congr 1; omega
    calc
      n ^ t = n * n ^ (t - 1) := hPower.symm
      _ ≤ (a * T) * n ^ (t - 1) := Nat.mul_le_mul_right _ haLower
      _ = a * (T * n ^ (t - 1)) := by ring
      _ ≤ a * d := Nat.mul_le_mul_left a hd
  have hOverlap : 2 * (a * a * t * D) < n ^ t := by
    have hD' := Nat.mul_le_mul_left (2 * a * a * t) hD
    have hD'' : 2 * (a * a * t * D) ≤
        2 * a * a * t * (R * n ^ (t - 2)) := by
      calc
        _ = (2 * a * a * t) * D := by ring
        _ ≤ (2 * a * a * t) * (R * n ^ (t - 2)) := hD'
        _ = _ := by ring
    omega
  exact heavy_root_gap_of_budgets (n ^ t) (n.choose t)
    (a * a * t * D) a d hChoose hOverlap hTail

end JSP523.Rank5
