import JSP523.Rank4.GraphActualAlgebra
import JSP523.Rank4.GlobalActualMaster

/-!
# The remaining actual graph payment for the finite rank-four deficit

The exact native representation and squared-degree accounting are already
proved for actual selected pair links. The statement below isolates their
remaining global payment as one inequality in the actual facet and graph
statistics. It then yields the finite deficit needed by the master budget.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Supported triple facets of actual completion degree one. -/
def rankFourPrivateFacets (K : Family α) (U : Edge α) : Family α :=
  (U.powersetCard 3).filter fun T =>
    (facetCompletions K U T).card = 1

omit [Fintype α] in
/-- The actual facet shadow splits exactly into private and nonprivate
facets, giving the `s-b` term in (III.B.9). -/
theorem rank_four_facet_shadow_private_nonprivate
    (K : Family α) (U : Edge α) :
    (rankFourFacetShadow K U).card =
      (rankFourPrivateFacets K U).card +
      (rankFourNonprivateFacets K U).card := by
  classical
  have h_union : rankFourFacetShadow K U =
      rankFourPrivateFacets K U ∪ rankFourNonprivateFacets K U := by
    ext T
    simp only [rankFourFacetShadow, rankFourPrivateFacets,
      rankFourNonprivateFacets, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hT, hpos⟩
      by_cases h1 : (facetCompletions K U T).card = 1
      · exact Or.inl ⟨hT, h1⟩
      · exact Or.inr ⟨hT, by omega⟩
    · rintro (⟨hT, h1⟩ | ⟨hT, h2⟩)
      · exact ⟨hT, by omega⟩
      · exact ⟨hT, by omega⟩
  have h_disjoint : Disjoint
      (rankFourPrivateFacets K U)
      (rankFourNonprivateFacets K U) := by
    apply Finset.disjoint_left.mpr
    intro T h_private h_nonprivate
    have h1 := (Finset.mem_filter.mp h_private).2
    have h2 := (Finset.mem_filter.mp h_nonprivate).2
    omega
  rw [h_union, Finset.card_union_of_disjoint h_disjoint]

/-- The actual squared-degree payment suffices for the manuscript's finite
deficit (III.B.7). Its terms are concrete functions of the cleaned family
and its selected pair links; the proof uses the closed identity (III.B.8). -/
theorem rank_four_actual_deficit_of_graph_payment
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_centers : UniqueCommonRootCenters D.K D.ground)
    (h_payment :
      18 * (D.K.card : ℚ) +
        ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
        6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) +
        actualSelectedDegreeSquareTotal D +
        actualSelectedActiveVertexTotal D ≤
      2 * actualFacetCompletionDegreeSquareTotal D +
        4 * (actualSelectedEdgeTotal D : ℚ) +
        2 * actualSelectedPotentialTotal D +
        4 * ((rankFourFacetShadow D.K D.ground).card : ℚ)) :
    10 * D.K.card +
      (rankFourNonprivateFacets D.K D.ground).card +
      6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
    2 * nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback h_centers) +
    4 * (rankFourFacetShadow D.K D.ground).card := by
  have h_identity := actual_graph_squared_accounting_identity
    D h_ground fallback h_centers
  have h_nat :
      (10 * D.K.card +
        (rankFourNonprivateFacets D.K D.ground).card +
        6 * (rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
      (2 * nativeTailVertexTotal D.K D.ground
          (nonemptyCommonRoots D.K D.ground)
            (chosenCommonRootLabel D.K D.ground fallback h_centers) +
        4 * (rankFourFacetShadow D.K D.ground).card : ℕ) := by
    push_cast
    linarith
  exact_mod_cast h_nat

end JSP523.Rank4
