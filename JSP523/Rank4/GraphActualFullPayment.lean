import JSP523.Rank4.GraphActualEdgeBalance

/-! # The rank-four finite deficit after full reciprocal cleanup -/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Full reciprocal cleanup satisfies the finite rank-four deficit.
The exact edge balance and its nonnegative reserve are proved from
actual opposite facets and selected pair-link occurrences. -/
theorem rank_four_full_cleanup_deficit
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters
      (clearReciprocalFully D).K D.ground)
    (hSeparated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D)) :
    10 * (clearReciprocalFully D).K.card +
      (rankFourNonprivateFacets
        (clearReciprocalFully D).K D.ground).card +
      6 * (rankFourAllPrivateEdges
        (clearReciprocalFully D).K D.ground).card ≤
    2 * nativeTailVertexTotal
      (clearReciprocalFully D).K D.ground
      (nonemptyCommonRoots
        (clearReciprocalFully D).K D.ground)
        (chosenCommonRootLabel
          (clearReciprocalFully D).K D.ground fallback hCenters) +
      4 * (rankFourFacetShadow
        (clearReciprocalFully D).K D.ground).card := by
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have hGround₂ : ∀ E ∈ D₂.K, E ⊆ D.ground := by
    intro E hE
    exact hGround E
      (clear_reciprocal_different_witnesses_sub D
        (clear_reciprocal_wrong_common_witnesses_sub D₁ hE))
  have hEdge := actual_selected_edge_total_eq_signed_edge_balance D₂ hGround₂
  rw [actual_edge_reciprocal_exclusion_occurrences_card] at hEdge
  push_cast at hEdge
  exact rank_four_full_cleanup_deficit_of_edge_balance D fallback
    hGround hCenters hSeparated
    (∑ E ∈ D₂.K, (actualEdgeSlack D₂ E : ℚ)) hEdge
    (actual_edge_slack_sum_ge_all_private D₂ hGround₂)

end JSP523.Rank4
