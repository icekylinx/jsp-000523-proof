import JSP523.Rank5.BadPairErrorPower
import JSP523.Rank5.HigherBadRootErrorPower

/-!
# Polynomial-scale error estimate for all actual dirty outside edges

The dirty family is the union of the actual bad-pair and higher-root edge
families. This combines their denominator-free estimates without introducing
any new hypotheses.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Denominator-free error estimate for the full actual dirty outside family.
The pair contribution is quadratic in the missing-facet count; all higher
roots contribute to the linear term. -/
theorem actual_dirty_outside_error_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W) (hw : 4 * r ≤ W.card) :
    let q := (missingStarFacets H W v r).card
    let Cpair := 2 * (4 * r) ^ (r - 1) * (r - 1).choose 2
    let Chigh := ∑ k ∈ Finset.Icc 3 (r - 2),
      2 * (4 * r) ^ (r - 1) * (r - 1).choose k
    let A := Cpair + Chigh
    W.card ^ (r - 1) * (actualDirtyOutsideEdges H W v r).card ≤
      A * q * W.card ^ (r - 2) + 2 * Cpair ^ 2 * q ^ 2 := by
  classical
  let w := W.card
  let q := (missingStarFacets H W v r).card
  let Cpair := 2 * (4 * r) ^ (r - 1) * (r - 1).choose 2
  let Chigh := ∑ k ∈ Finset.Icc 3 (r - 2),
    2 * (4 * r) ^ (r - 1) * (r - 1).choose k
  let A := Cpair + Chigh
  let Bad₂ := badMissingSets H W v r 2 ((w - r - 2).choose (r - 3))
  let Pair := badPairEdges (ordinaryOutsideFamily H W v r) Bad₂
  let Higher := actualHigherBadRootEdges H W v r
  have hPair := actual_bad_pair_error_power_bound H W v r
    hAdm hUniform hr hvW hw
  have hPair' : w ^ (r - 1) * Pair.card ≤
      Cpair * q * w ^ (r - 2) + 2 * Cpair ^ 2 * q ^ 2 := by
    simpa [w, q, Cpair, Bad₂, Pair] using hPair
  have hHigher := actual_higher_bad_root_edges_power_bound H W v r
    hAdm hUniform hvW hr hw
  have hHigher' : w * Higher.card ≤ Chigh * q := by
    simpa [w, q, Chigh] using hHigher
  have hwPow : w ^ (r - 1) = w * w ^ (r - 2) := by
    rw [show r - 1 = 1 + (r - 2) by omega, pow_add, pow_one]
  have hHigherScaled : w ^ (r - 1) * Higher.card ≤
      Chigh * q * w ^ (r - 2) := by
    rw [hwPow]
    calc
      w * w ^ (r - 2) * Higher.card = (w * Higher.card) * w ^ (r - 2) := by
        ac_rfl
      _ ≤ (Chigh * q) * w ^ (r - 2) := Nat.mul_le_mul_right _ hHigher'
      _ = Chigh * q * w ^ (r - 2) := by ac_rfl
  have hUnion : (actualDirtyOutsideEdges H W v r).card ≤ Pair.card + Higher.card := by
    simpa [actualDirtyOutsideEdges, Pair, Higher, Bad₂, w] using
      (Finset.card_union_le Pair Higher)
  change w ^ (r - 1) *
      (actualDirtyOutsideEdges H W v r).card ≤
    A * q * w ^ (r - 2) + 2 * Cpair ^ 2 * q ^ 2
  calc
    _ ≤ w ^ (r - 1) * (Pair.card + Higher.card) :=
      Nat.mul_le_mul_left _ hUnion
    _ = w ^ (r - 1) * Pair.card + w ^ (r - 1) * Higher.card := by ring
    _ ≤ (Cpair * q * w ^ (r - 2) + 2 * Cpair ^ 2 * q ^ 2) +
        Chigh * q * w ^ (r - 2) := Nat.add_le_add hPair' hHigherScaled
    _ = A * q * w ^ (r - 2) + 2 * Cpair ^ 2 * q ^ 2 := by
      dsimp [A]
      ring

end JSP523
