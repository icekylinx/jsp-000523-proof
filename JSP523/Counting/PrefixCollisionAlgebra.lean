import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Prefix-collision algebra

This is the algebraic final step behind (IV.B.1) in the all-rank manuscript.
The genuinely combinatorial work supplies a lower bound on the collision count
`S` and an upper bound on the same quantity.  This lemma records their exact
finite combination, independently of asymptotics.
-/

namespace JSP523

/--
If Cauchy gives `M^2 ≤ N (M + 2S)` and the structural decomposition gives
`2S ≤ p(D4-1)M + 2TB`, then (IV.B.1) follows.
-/
theorem prefix_collision_combine
    (M N S p D4 T B : ℝ)
    (hN : 0 ≤ N)
    (hLower : M * M ≤ N * (M + 2 * S))
    (hUpper : 2 * S ≤ p * (D4 - 1) * M + 2 * T * B) :
    M * M ≤ N * ((1 + p * (D4 - 1)) * M + 2 * T * B) := by
  have hInside :
      M + 2 * S ≤ (1 + p * (D4 - 1)) * M + 2 * T * B := by
    nlinarith
  exact hLower.trans (mul_le_mul_of_nonneg_left hInside hN)

end JSP523
