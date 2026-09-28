import JSP523.Rank4.GraphActualExcessOverBases

/-!
# Global selected pair-link excess and native vertices

The actual selected excess can now be summed over every used completion
pair. The resulting total is exactly the native degree-excess total,
which together with the native degree-sum ledger gives twice the
facet-completion-pair count.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual selected multiplicity excess, summed over used
completion pairs and all valid base pairs, is the native degree excess. -/
theorem actual_selected_excess_used_total_eq_native_degree_excess_total
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ Q ∈ D.ground.powersetCard 2,
        actualSelectedPairExcessAtBase D Q P) =
      nativeTailDegreeExcessTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) := by
  rw [← selected_on_label_excess_total_eq_native_degree_excess_total
    D fallback hCenters]
  apply Finset.sum_congr rfl
  intro P hUsed
  exact actual_selected_excess_over_bases_eq_on_label_tails
    D fallback hCenters P hUsed

/-- The actual selected excess plus the native active-vertex count is
twice the number of completion pairs over actual triple facets. -/
theorem actual_selected_excess_plus_native_vertices_eq_facet_pairs
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ Q ∈ D.ground.powersetCard 2,
        actualSelectedPairExcessAtBase D Q P) +
      nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) =
      2 * (∑ T ∈ D.ground.powersetCard 3,
        (facetCompletions D.K D.ground T).card.choose 2) := by
  rw [actual_selected_excess_used_total_eq_native_degree_excess_total
    D fallback hCenters]
  exact native_tail_degree_excess_facet_ledger
    D.K D.ground fallback D.uniform_four hCenters

end JSP523.Rank4
