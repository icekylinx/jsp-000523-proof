import JSP523.Rank4.GraphUnorderedExcessLedger

/-!
# Unordered selected excess has only used completion-pair support

At a valid base pair, every unordered completion pair with positive
selected excess is a used pair in the actual four-family. Hence the
graph's total excess is exactly the sum indexed by used completion
pairs in the native ledger.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual selected pair-link's unordered positive excess is the
sum over used completion pairs, at each valid base pair. -/
theorem actual_unordered_excess_eq_used_pair_sum
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2) :
    graphUnorderedCommonExcess
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) =
      ∑ P ∈ nonemptyCommonRoots D.K D.ground,
        actualSelectedPairExcessAtBase D Q P := by
  classical
  let F := selectedCompletionPairGraph D
    (actualEligiblePairSlotVertices D Q) Q
  let AllPairs := (Finset.univ : Finset α).powersetCard 2
  let Used := nonemptyCommonRoots D.K D.ground
  have hSub : Used ⊆ AllPairs := by
    intro P hUsed
    have hPcard :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).2
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hPcard⟩
  have hZeroOutside : ∀ P ∈ AllPairs, P ∉ Used →
      graphCommonMultiplicityAtPair F P - 1 = 0 := by
    intro P hAll hUnused
    have hPcard : P.card = 2 :=
      (Finset.mem_powersetCard.mp hAll).2
    let ab := pairRootRep P hPcard
    have hSpec := pair_root_rep_spec P hPcard
    have hUnusedAB : ({ab.1, ab.2} : Edge α) ∉ Used := by
      rw [← hSpec.2]
      exact hUnused
    have hZero := actual_selected_common_zero_of_unused
      D Q hQ ab.1 ab.2 hSpec.1 hUnusedAB
    unfold graphCommonMultiplicityAtPair
    rw [dite_eq_left hPcard]
    simpa only [F, ab] using congrArg (fun n : ℕ => n - 1) hZero
  have hRestrict := Finset.sum_subset hSub hZeroOutside
  unfold graphUnorderedCommonExcess
  rw [← hRestrict]
  apply Finset.sum_congr rfl
  intro P hUsed
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).2
  unfold graphCommonMultiplicityAtPair actualSelectedPairExcessAtBase
  rw [dite_eq_left hPcard]
  rw [dite_eq_left hPcard]

end JSP523.Rank4
