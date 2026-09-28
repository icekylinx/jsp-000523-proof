import JSP523.Rank4.GraphActualExcessSum

/-!
# Pointwise support of the actual selected pair-link excess

For a used completion pair, positive selected multiplicity excess is
supported only at base pairs containing its unique label and disjoint
from the completion endpoints.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Away from an on-label, disjoint base pair, actual selected common
multiplicity contributes zero positive excess. -/
theorem actual_selected_pair_excess_zero_off_support
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (a b : α) (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hOff : chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α) ∉ Q ∨
      ¬ Disjoint Q ({a, b} : Edge α)) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b - 1 = 0 := by
  classical
  rcases hOff with hzQ | hInter
  · have hAtMost := actual_eligible_pair_common_le_one_off_label
      D Q hQ fallback hCenters a b haU hbU hab hUsed hzQ
    omega
  · obtain ⟨x, hxQ, hxP⟩ := Finset.not_disjoint_iff.mp hInter
    have hxPair : x = a ∨ x = b := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxP
    rcases hxPair with hxa | hxb
    · have haQ : a ∈ Q := hxa.symm ▸ hxQ
      rw [actual_selected_common_zero_of_left_mem_base D Q a b haQ]
    · have hbQ : b ∈ Q := hxb.symm ▸ hxQ
      rw [actual_selected_common_zero_of_right_mem_base D Q a b hbQ]

/-- The same support statement phrased with a positive excess:
the base pair must contain the label and omit both endpoints. -/
theorem actual_selected_pair_positive_excess_support
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (a b : α) (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hPos : 0 < graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b - 1) :
    chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α) ∈ Q ∧
      Disjoint Q ({a, b} : Edge α) := by
  by_contra h
  have hOff : chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α) ∉ Q ∨
      ¬ Disjoint Q ({a, b} : Edge α) := by
    exact not_and_or.mp h
  have hZero := actual_selected_pair_excess_zero_off_support
    D fallback hCenters Q hQ a b haU hbU hab hUsed hOff
  omega

end JSP523.Rank4
