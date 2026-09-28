import JSP523.Rank5.BadRootPowerBounds

/-!
# Explicit power bound for the singleton-threshold error term

Combines the singleton bad-root power estimate with the finite difference
of binomial thresholds from §IV.2.2.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Clearing denominators, the singleton-root estimate controls the error
term `w * d * Δ` by the explicit rank constant times `(r+1)q`. -/
theorem actual_singleton_delta_error_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hr : 5 ≤ r) (hw : 4 * r ≤ W.card) :
    W.card * (badSingletonVertices H W v r).card *
        (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)) ≤
      (2 * (4 * r) ^ (r - 1) * (r - 1)) * (r + 1) *
        (missingStarFacets H W v r).card := by
  let w := W.card
  let d := (badSingletonVertices H W v r).card
  let q := (missingStarFacets H W v r).card
  let Cd := 2 * (4 * r) ^ (r - 1) * (r - 1)
  have hDelta := Counting.iv22_delta_binomial_bound r w hr hw
  have hPower := actual_bad_singleton_power_bound H W v r (by omega) hw
  change d * w ^ (r - 2) ≤ Cd * q at hPower
  change w * d * (w.choose (r - 2) - (w - r - 1).choose (r - 2)) ≤
      Cd * (r + 1) * q
  calc
    w * d * (w.choose (r - 2) - (w - r - 1).choose (r - 2)) ≤
        w * d * ((r + 1) * w ^ (r - 3)) := by
          exact Nat.mul_le_mul_left (w * d) hDelta
    _ = (r + 1) * (d * w ^ (r - 2)) := by
      rw [show r - 2 = (r - 3) + 1 by omega, pow_succ]
      ac_rfl
    _ ≤ (r + 1) * (Cd * q) :=
      Nat.mul_le_mul_left (r + 1) hPower
    _ = Cd * (r + 1) * q := by ac_rfl

end JSP523
