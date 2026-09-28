import JSP523.Rank4.GraphPotentialUnordered
import JSP523.Rank4.GlobalDegreeTail
import Mathlib.Data.Nat.Choose.Cast

/-!
# The global algebra before facet-type accounting in (III.B.9)

This module converts the actual native identity into the squared-degree
formula displayed immediately after (III.B.9). It uses actual selected
pair links and actual facet completion degrees, leaving the later
monochromatic/colored facet classification as a separate step.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Actual selected pair-link edge total `e_*`. -/
noncomputable def actualSelectedEdgeTotal
    (D : FiniteCompletionCliqueData α) : ℕ :=
  ∑ Q ∈ D.ground.powersetCard 2,
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q).edgeFinset.card

/-- Sum of squared selected degrees across every base pair and vertex. -/
noncomputable def actualSelectedDegreeSquareTotal
    (D : FiniteCompletionCliqueData α) : ℚ :=
  ∑ Q ∈ D.ground.powersetCard 2,
    ∑ x : α,
      ((selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ) ^ 2

/-- Sum of selected nonisolated-vertex counts. -/
noncomputable def actualSelectedActiveVertexTotal
    (D : FiniteCompletionCliqueData α) : ℚ :=
  ∑ Q ∈ D.ground.powersetCard 2,
    activeVertexCount
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q)

/-- Sum of the actual graph potentials `q(F_Q)-e(F_Q)+v(F_Q)/2`. -/
noncomputable def actualSelectedPotentialTotal
    (D : FiniteCompletionCliqueData α) : ℚ :=
  ∑ Q ∈ D.ground.powersetCard 2,
    graphDeficit
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q)

/-- Sum of squared actual facet completion degrees. -/
def actualFacetCompletionDegreeSquareTotal
    (D : FiniteCompletionCliqueData α) : ℚ :=
  ∑ T ∈ D.ground.powersetCard 3,
    ((facetCompletions D.K D.ground T).card : ℚ) ^ 2

omit [DecidableEq α] in
/-- For one graph, squared degrees split into twice the degree-pair
count and twice the edge count. -/
theorem graph_degree_square_eq_twice_degree_pairs_add_edges
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ x : α, (F.degree x : ℚ) ^ 2) =
      2 * (∑ x : α, ((F.degree x).choose 2 : ℚ)) +
        2 * (F.edgeFinset.card : ℚ) := by
  have hScalar (x : α) :
      (F.degree x : ℚ) ^ 2 =
        2 * ((F.degree x).choose 2 : ℚ) + F.degree x := by
    rw [Nat.cast_choose_two]
    ring
  have hHand : (∑ x : α, (F.degree x : ℚ)) =
      2 * (F.edgeFinset.card : ℚ) := by
    exact_mod_cast F.sum_degrees_eq_twice_card_edges
  calc
    (∑ x : α, (F.degree x : ℚ) ^ 2) =
        ∑ x : α,
          (2 * ((F.degree x).choose 2 : ℚ) + F.degree x) := by
            apply Finset.sum_congr rfl
            intro x _
            exact hScalar x
    _ = 2 * (∑ x : α, ((F.degree x).choose 2 : ℚ)) +
        ∑ x : α, (F.degree x : ℚ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hHand]

/-- The actual selected squared-degree total is `2W+2e_*`. -/
theorem actual_selected_square_eq_degree_pairs_add_edges
    (D : FiniteCompletionCliqueData α) :
    actualSelectedDegreeSquareTotal D =
      2 * (actualSelectedDegreePairTotal D : ℚ) +
        2 * (actualSelectedEdgeTotal D : ℚ) := by
  classical
  unfold actualSelectedDegreeSquareTotal actualSelectedDegreePairTotal
    actualSelectedEdgeTotal
  calc
    (∑ Q ∈ D.ground.powersetCard 2,
      ∑ x : α,
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ) ^ 2) =
      ∑ Q ∈ D.ground.powersetCard 2,
        (2 * (∑ x : α,
          (((selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q).degree x).choose 2 : ℚ)) +
          2 * ((selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q).edgeFinset.card : ℚ)) := by
            apply Finset.sum_congr rfl
            intro Q _
            exact graph_degree_square_eq_twice_degree_pairs_add_edges _
    _ = 2 * (∑ Q ∈ D.ground.powersetCard 2,
        ∑ x : α,
          (((selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q).degree x).choose 2 : ℚ)) +
        2 * (∑ Q ∈ D.ground.powersetCard 2,
          ((selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q).edgeFinset.card : ℚ)) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.mul_sum]
    _ = _ := by push_cast; ring

/-- Summing the graph potentials rewrites the total common-pair count as
potential plus selected edges, with the active-vertex correction. -/
theorem actual_selected_common_pairs_plus_active_half
    (D : FiniteCompletionCliqueData α) :
    (actualSelectedCommonPairTotal D : ℚ) +
      actualSelectedActiveVertexTotal D / 2 =
      actualSelectedPotentialTotal D +
        (actualSelectedEdgeTotal D : ℚ) := by
  classical
  unfold actualSelectedCommonPairTotal actualSelectedActiveVertexTotal
    actualSelectedPotentialTotal actualSelectedEdgeTotal
  have hPoint (Q : Edge α) :
      (graphCommonPairCount
          (selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q) : ℚ) +
        activeVertexCount
          (selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q) / 2 =
      graphDeficit
          (selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q) +
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).edgeFinset.card : ℚ) := by
    rw [graph_deficit_eq_unordered_common_potential]
    ring
  simp only [Nat.cast_sum, Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q _
  exact hPoint Q

/-- The first exact algebraic identity after (III.B.8), summed over
actual facets and selected links. -/
theorem actual_graph_squared_accounting_identity
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    2 * (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) +
      actualSelectedDegreeSquareTotal D +
      actualSelectedActiveVertexTotal D + 8 * (D.K.card : ℚ) =
    2 * actualFacetCompletionDegreeSquareTotal D +
      4 * (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  classical
  let R3 := ∑ T ∈ D.ground.powersetCard 3,
    (facetCompletions D.K D.ground T).card.choose 2
  have hB8 := actual_native_representation_iii_b8 D fallback hCenters
  have hB8q : (actualSelectedDegreePairTotal D : ℚ) +
      (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) =
      (actualSelectedCommonPairTotal D : ℚ) + 2 * (R3 : ℚ) := by
    exact_mod_cast hB8
  have hPotential := actual_selected_common_pairs_plus_active_half D
  have hSquare := actual_selected_square_eq_degree_pairs_add_edges D
  have hFacetChoose : 2 * (R3 : ℚ) =
      actualFacetCompletionDegreeSquareTotal D -
        (∑ T ∈ D.ground.powersetCard 3,
          (facetCompletions D.K D.ground T).card : ℚ) := by
    dsimp [R3, actualFacetCompletionDegreeSquareTotal]
    rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    rw [Nat.cast_choose_two]
    ring
  have hFacetDegrees := rank_four_facet_completion_degree_sum
    D.K D.ground D.uniform_four hGround
  have hFacetDegreesQ :
      (∑ T ∈ D.ground.powersetCard 3,
        (facetCompletions D.K D.ground T).card : ℚ) =
        4 * (D.K.card : ℚ) := by
    exact_mod_cast hFacetDegrees
  have hFacetChoose' := hFacetChoose
  rw [hFacetDegreesQ] at hFacetChoose'
  nlinarith [hB8q, hPotential, hSquare, hFacetChoose']

/-- The same actual identity in the rearranged form displayed after
(III.B.9): twice the native vertex total is the facet square contribution
minus all selected slot squares and positive-slot indicators, plus the
edge and graph-potential terms and the `-8m` correction. -/
theorem actual_graph_squared_accounting_identity_rearranged
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    2 * (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) =
      2 * actualFacetCompletionDegreeSquareTotal D -
        actualSelectedDegreeSquareTotal D -
        actualSelectedActiveVertexTotal D - 8 * (D.K.card : ℚ) +
        4 * (actualSelectedEdgeTotal D : ℚ) +
        2 * actualSelectedPotentialTotal D := by
  have h := actual_graph_squared_accounting_identity
    D hGround fallback hCenters
  linarith

end JSP523.Rank4
