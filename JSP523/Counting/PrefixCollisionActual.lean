import JSP523.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite disjoint-prefix collision counting

This module isolates the disjoint-prefix contribution to the collision upper
bound in §IV.B.  It is stated for arbitrary finite prefix and tail families;
the actual common-tail estimate is supplied as a hypothesis.
-/

namespace JSP523

open Classical


/-- Two-element families of prefixes whose two members are disjoint. -/
noncomputable def disjointPrefixPairs (F : Family α) : Finset (Family α) := by
  classical
  exact (F.powersetCard 2).filter fun q =>
    ∀ ⦃Y Z : Edge α⦄, Y ∈ q → Z ∈ q → Y ≠ Z → Disjoint Y Z

/-- A pair of prefixes occurs at a tail when both prefixes are assigned to it. -/
def prefixPairOccursAt (assigned : Edge α → Family α)
    (q : Family α) (P : Edge α) : Prop :=
  ∀ ⦃Y : Edge α⦄, Y ∈ q → Y ∈ assigned P

/-- Sum, over tails, of the numbers of disjoint assigned prefix pairs. -/
noncomputable def disjointPrefixCollisionCount (T F : Family α)
    (assigned : Edge α → Family α) : ℕ := by
  classical
  exact ∑ P ∈ T,
    ((disjointPrefixPairs F).filter (fun q => prefixPairOccursAt assigned q P)).card

/-- Exact finite double counting for disjoint assigned prefix pairs. -/
theorem disjoint_prefix_collision_count_eq_tail_sum
    (T F : Family α) (assigned : Edge α → Family α) :
    disjointPrefixCollisionCount T F assigned =
      ∑ q ∈ disjointPrefixPairs F,
        (T.filter (fun P => prefixPairOccursAt assigned q P)).card := by
  classical
  unfold disjointPrefixCollisionCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- If every disjoint prefix pair occurs at at most `B` tails, its total
contribution to the collision count is at most `B` times the number of such
prefix pairs. -/
theorem disjoint_prefix_collision_count_le
    (T F : Family α) (assigned : Edge α → Family α) (B : ℕ)
    (hCap : ∀ q ∈ disjointPrefixPairs F,
      (T.filter (fun P => prefixPairOccursAt assigned q P)).card ≤ B) :
    disjointPrefixCollisionCount T F assigned ≤
      B * (disjointPrefixPairs F).card := by
  classical
  rw [disjoint_prefix_collision_count_eq_tail_sum]
  calc
    (∑ q ∈ disjointPrefixPairs F,
        (T.filter (fun P => prefixPairOccursAt assigned q P)).card)
        ≤ ∑ _q ∈ disjointPrefixPairs F, B := by
          apply Finset.sum_le_sum
          intro q hq
          exact hCap q hq
    _ = B * (disjointPrefixPairs F).card := by simp [Nat.mul_comm]

/-- A coarser form that needs only the total number of available prefixes. -/
theorem disjoint_prefix_collision_count_le_choose
    (T F : Family α) (assigned : Edge α → Family α) (B : ℕ)
    (hCap : ∀ q ∈ disjointPrefixPairs F,
      (T.filter (fun P => prefixPairOccursAt assigned q P)).card ≤ B) :
    disjointPrefixCollisionCount T F assigned ≤ B * F.card.choose 2 := by
  classical
  have hPairs : (disjointPrefixPairs F).card ≤ F.card.choose 2 := by
    calc
      (disjointPrefixPairs F).card ≤ (F.powersetCard 2).card := by
        unfold disjointPrefixPairs
        exact Finset.card_filter_le _ _
      _ = F.card.choose 2 := Finset.card_powersetCard 2 F
  calc
    disjointPrefixCollisionCount T F assigned ≤
        B * (disjointPrefixPairs F).card :=
    disjoint_prefix_collision_count_le T F assigned B hCap
    _ ≤ B * F.card.choose 2 := Nat.mul_le_mul_left B hPairs


end JSP523
