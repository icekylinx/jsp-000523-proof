import JSP523.Rank4.GraphActualColoredMultiplicity
import JSP523.Rank4.GraphActualAlgebra

/-!
# Actual marked graph payment over all base pairs

The selected pair links satisfy the colored-vertex multiplicity
hypothesis of the graph deficit lemma. Summing that lemma gives the
graph side of (III.B.10) with actual marked slots.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual selected graph potentials pay every unique-pair record
and every fully selected colored degree-three or degree-four slot. -/
theorem actual_colored_marked_total_payment
    (D : FiniteCompletionCliqueData α) :
    (∑ Q ∈ D.ground.powersetCard 2,
      (orderedUniquePairCount
        (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q) : ℚ)) / 4 +
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ)) / 2 +
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedFourSlots D Q).card : ℚ)) ≤
    actualSelectedPotentialTotal D := by
  classical
  have hLocal := Finset.sum_le_sum
    (s := D.ground.powersetCard 2)
    (fun Q hQ => actual_colored_marked_pair_link_payment D Q hQ)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div] at hLocal
  exact hLocal

end JSP523.Rank4
