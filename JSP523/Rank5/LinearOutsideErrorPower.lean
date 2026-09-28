import JSP523.Rank5.HigherBadRootErrorPower
import JSP523.Rank5.DeltaErrorPower

/-!
# Combined explicit power bound for the actual linear outside errors

This packages the higher bad-root edge contribution and the singleton
threshold-difference contribution appearing in §IV.2.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Rank-only coefficient for the two actual linear error terms. -/
def linearOutsideErrorCoefficient (r : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 3 (r - 2),
      2 * (4 * r) ^ (r - 1) * (r - 1).choose k) +
    (2 * (4 * r) ^ (r - 1) * (r - 1)) * (r + 1)

/-- The combined actual higher-root and singleton-threshold error has
explicit `q / w` scale, in denominator-free form. -/
theorem actual_linear_outside_error_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hvW : v ∉ W) (hr : 5 ≤ r) (hw : 4 * r ≤ W.card) :
    W.card * ((actualHigherBadRootEdges H W v r).card +
      (badSingletonVertices H W v r).card *
        (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2))) ≤
      linearOutsideErrorCoefficient r *
        (missingStarFacets H W v r).card := by
  let Q := (missingStarFacets H W v r).card
  let A := ∑ k ∈ Finset.Icc 3 (r - 2),
      2 * (4 * r) ^ (r - 1) * (r - 1).choose k
  let B := (2 * (4 * r) ^ (r - 1) * (r - 1)) * (r + 1)
  have hHigher := actual_higher_bad_root_edges_power_bound H W v r
    hAdm hUniform hvW hr hw
  have hSingleton := actual_singleton_delta_error_power_bound H W v r hr hw
  change W.card * (actualHigherBadRootEdges H W v r).card ≤ A * Q at hHigher
  have hSingleton' : W.card * ((badSingletonVertices H W v r).card *
      (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2))) ≤ B * Q := by
    have hS := hSingleton
    change (W.card * (badSingletonVertices H W v r).card) *
      (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)) ≤
      (2 * (4 * r) ^ (r - 1) * (r - 1) * (r + 1)) *
        (missingStarFacets H W v r).card at hS
    simpa [B, Q, Nat.mul_assoc] using hS
  change W.card * ((actualHigherBadRootEdges H W v r).card +
      (badSingletonVertices H W v r).card *
        (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2))) ≤
      (A + B) * Q
  calc
    W.card * ((actualHigherBadRootEdges H W v r).card +
      (badSingletonVertices H W v r).card *
        (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)))
        = W.card * (actualHigherBadRootEdges H W v r).card +
          W.card * ((badSingletonVertices H W v r).card *
            (W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2))) := by
              rw [Nat.mul_add]
    _ ≤ A * Q + B * Q := Nat.add_le_add hHigher hSingleton'
    _ = (A + B) * Q := by rw [Nat.add_mul]

end JSP523
