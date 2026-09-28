import JSP523.Rank5.StarLayerCollision

/-!
# Global distinct-completion incidence for star layers

The local cell estimate in `StarLayerCollision` can be summed over all
ordered pairs of distinct completions. This is the distinct-completion
portion of the global collision reindexing in Lemma IV.3.2.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Global ordered incidence of distinct completions for two centers.
Each summand counts common tails for the two disjoint two-point roots. -/
def starLayerDistinctCompletionIncidence (H : Family α) (U : Edge α)
    (z w : α) (r : ℕ) : ℕ :=
  ∑ x ∈ U, ∑ y ∈ U.erase x,
    (starLayerCrossCell H U z w x y r).card

/-- The distinct-completion part of the IV.3.2 collision count is at most
`|U| (|U|-1) (r-2) D₃`. -/
theorem starLayerDistinctCompletionIncidence_le
    {H : Family α} {U : Edge α} {z w : α} {r D₃ : ℕ}
    (hH : Admissible H) (hzw : z ≠ w)
    (hzU : z ∉ U) (hwU : w ∉ U) (hr : 4 ≤ r)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    starLayerDistinctCompletionIncidence H U z w r ≤
      U.card * (U.card - 1) * (r - 2) * D₃ := by
  classical
  unfold starLayerDistinctCompletionIncidence
  calc
    (∑ x ∈ U, ∑ y ∈ U.erase x,
        (starLayerCrossCell H U z w x y r).card)
      ≤ ∑ x ∈ U, ∑ y ∈ U.erase x, (r - 2) * D₃ := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
        have hxU : x ∈ U := hx
        have hyU : y ∈ U := (Finset.mem_erase.mp hy).2
        exact starLayerCrossCell_card_le hH hzw hxy hzU hwU hxU hyU hr hD₃
    _ = U.card * (U.card - 1) * ((r - 2) * D₃) := by
      calc
        (∑ x ∈ U, ∑ y ∈ U.erase x, (r - 2) * D₃) =
            ∑ x ∈ U, (U.erase x).card * ((r - 2) * D₃) := by
          congr 1
          funext x
          simp
        _ =
            ∑ x ∈ U, (U.card - 1) * ((r - 2) * D₃) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.card_erase_of_mem hx]
        _ = U.card * (U.card - 1) * ((r - 2) * D₃) := by
          simp [Finset.sum_const, Nat.mul_assoc]
    _ = U.card * (U.card - 1) * (r - 2) * D₃ := by
      simp [Nat.mul_assoc]

/-- Combined equal and distinct completion budget. The first summand is the
equal-completion common-prefix cell; the second is the reindexed sum over
ordered distinct completion pairs. -/
theorem starLayerCompletionCollisionBudget_le
    {H : Family α} {U : Edge α} {z w : α} {r D₂ D₃ : ℕ}
    (hH : Admissible H) (hzw : z ≠ w)
    (hzU : z ∉ U) (hwU : w ∉ U) (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    (commonPrefixTails H U ({z} : Edge α) {w} (r - 1)).card +
        starLayerDistinctCompletionIncidence H U z w r ≤
      (r - 1) * (r - 1) * D₂ +
        U.card * (U.card - 1) * (r - 2) * D₃ := by
  have hr2 : 2 ≤ r := by omega
  have heq := starLayerEqualCompletionCell_card_le
    hH hzw hzU hwU hr2 hD₂
  have hcross := starLayerDistinctCompletionIncidence_le
    hH hzw hzU hwU hr hD₃
  have hrpos : 1 ≤ r - 1 := by omega
  calc
    (commonPrefixTails H U ({z} : Edge α) {w} (r - 1)).card +
        starLayerDistinctCompletionIncidence H U z w r
      ≤ (r - 1) * D₂ +
          U.card * (U.card - 1) * (r - 2) * D₃ := Nat.add_le_add heq hcross
    _ ≤ (r - 1) * (r - 1) * D₂ +
          U.card * (U.card - 1) * (r - 2) * D₃ := by
      have hcoef : r - 1 ≤ (r - 1) * (r - 1) := by
        nlinarith [hrpos]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right D₂ hcoef) _

end JSP523.Rank5
