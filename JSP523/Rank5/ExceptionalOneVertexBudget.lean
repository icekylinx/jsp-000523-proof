import JSP523.Rank5.ExceptionalOneVertex
import JSP523.Rank5.ExceptionalVertexIncidence

/-!
# The second inequality in (IV.2.9)

Combine the factor-two exceptional-vertex budget (IV.2.8) with the exact
binomial correction
`choose(|W|, r - 2) = Λ + Δ`, where
`Λ = choose(|W| - r - 1, r - 2)` and
`Δ = choose(|W|, r - 2) - Λ`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Finite second inequality of (IV.2.9), with `q_D`, `J`, `Λ`, and `Δ`
given by the explicit finite quantities in §IV.2.2. -/
theorem exceptional_one_vertex_budget_second_term
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hr : 3 ≤ r) :
    let M := missingStarFacets H W v r
    let D := badSingletonVertices H W v r
    let U := W \ D
    let qD := (M.filter fun S => (S ∩ D).Nonempty).card
    let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
    let Λ := (W.card - r - 1).choose (r - 2)
    let Δ := W.card.choose (r - 2) - Λ
    D.card * U.card.choose (r - 2) ≤ 2 * qD + 2 * J + D.card * Δ := by
  classical
  let M := missingStarFacets H W v r
  let D := badSingletonVertices H W v r
  let U := W \ D
  let qD := (M.filter fun S => (S ∩ D).Nonempty).card
  let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
  let Λ := (W.card - r - 1).choose (r - 2)
  let Δ := W.card.choose (r - 2) - Λ
  have hDsub : D ⊆ W := Finset.filter_subset _ _
  have hUsub : U ⊆ W := Finset.sdiff_subset
  have hUcard : U.card ≤ W.card := Finset.card_le_card hUsub
  have hChooseMono := Nat.choose_le_choose (r - 2) hUcard
  have hTop : W.card - r - 1 ≤ W.card := by omega
  have hLambda : Λ ≤ W.card.choose (r - 2) := by
    exact Nat.choose_le_choose (r - 2) hTop
  have hDelta : Λ + Δ = W.card.choose (r - 2) := by
    dsimp [Δ]
    exact Nat.add_sub_of_le hLambda
  have hBudget := bad_singleton_exceptional_budget H W v r hr
  change Λ * D.card ≤ 2 * (qD + J) at hBudget
  change D.card * U.card.choose (r - 2) ≤
    2 * qD + 2 * J + D.card * Δ
  calc
    D.card * U.card.choose (r - 2) ≤
        D.card * W.card.choose (r - 2) :=
      Nat.mul_le_mul_left D.card hChooseMono
    _ = D.card * Λ + D.card * Δ := by
      rw [← hDelta, Nat.mul_add]
    _ ≤ 2 * (qD + J) + D.card * Δ := by
      apply Nat.add_le_add_right
      simpa [Nat.mul_comm] using hBudget
    _ = 2 * qD + 2 * J + D.card * Δ := by
      rw [Nat.mul_add]

/-- The corresponding numerator inequality obtained by combining both
finite bounds for `b₁`. -/
theorem outside_one_bad_singleton_budget_numerator
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W) :
    let M := missingStarFacets H W v r
    let D := badSingletonVertices H W v r
    let qD := (M.filter fun S => (S ∩ D).Nonempty).card
    let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
    let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
    (r - 1) * (outsideOneBadSingleton H W v r).card ≤
      2 * qD + 2 * J + D.card * Δ := by
  let D := badSingletonVertices H W v r
  let U := W \ D
  let qD := ((missingStarFacets H W v r).filter
    fun S => (S ∩ D).Nonempty).card
  let J := D.card.choose 2 * (W.card - 2).choose (r - 3)
  let Δ := W.card.choose (r - 2) - (W.card - r - 1).choose (r - 2)
  have hInc := outside_one_bad_singleton_incidence_bound H W v r
    hAdm hUniform hr hvW
  have hBudget := exceptional_one_vertex_budget_second_term H W v r hr
  change (r - 1) * (outsideOneBadSingleton H W v r).card ≤
    D.card * U.card.choose (r - 2) at hInc
  change D.card * U.card.choose (r - 2) ≤
    2 * qD + 2 * J + D.card * Δ at hBudget
  change (r - 1) * (outsideOneBadSingleton H W v r).card ≤
    2 * qD + 2 * J + D.card * Δ
  exact hInc.trans hBudget

end JSP523
