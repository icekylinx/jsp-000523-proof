import JSP523.Rank4.GraphActualUnorderedExcess

/-!
# The actual native representation (III.B.8)

All terms are defined from the manuscript's actual selected pair links:
vertices are selected exactly when their facet is nonprivate and colored,
or monochromatic with center in the base pair. The identity is stated
in additive natural-number form to avoid truncated subtraction.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `W`: the sum of degree-binomial terms over all actual selected
pair links. -/
noncomputable def actualSelectedDegreePairTotal
    (D : FiniteCompletionCliqueData α) : ℕ :=
  ∑ Q ∈ D.ground.powersetCard 2,
    ∑ x : α,
      ((selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x).choose 2

/-- The sum of `q(F_Q)`, unordered endpoint pairs with a common
neighbor, over all actual selected pair links. -/
noncomputable def actualSelectedCommonPairTotal
    (D : FiniteCompletionCliqueData α) : ℕ :=
  ∑ Q ∈ D.ground.powersetCard 2,
    graphCommonPairCount
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q)

/-- The exact finite native representation (III.B.8), in additive
form: `W+V = Σ_Q q(F_Q)+2R₃`. -/
theorem actual_native_representation_III_B8
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    actualSelectedDegreePairTotal D +
      nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) =
      actualSelectedCommonPairTotal D +
        2 * (∑ T ∈ D.ground.powersetCard 3,
          (facetCompletions D.K D.ground T).card.choose 2) := by
  classical
  let F : Edge α → SimpleGraph α := fun Q =>
    selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q
  let E := ∑ Q ∈ D.ground.powersetCard 2,
    graphUnorderedCommonExcess (F Q)
  have hGraph : actualSelectedDegreePairTotal D =
      actualSelectedCommonPairTotal D + E := by
    unfold actualSelectedDegreePairTotal actualSelectedCommonPairTotal
    calc
      (∑ Q ∈ D.ground.powersetCard 2,
        ∑ x : α, ((F Q).degree x).choose 2) =
          ∑ Q ∈ D.ground.powersetCard 2,
            (graphCommonPairCount (F Q) +
              graphUnorderedCommonExcess (F Q)) := by
                apply Finset.sum_congr rfl
                intro Q _
                exact graph_degree_pairs_eq_common_pairs_add_excess (F Q)
      _ = (∑ Q ∈ D.ground.powersetCard 2,
          graphCommonPairCount (F Q)) + E := by
            rw [Finset.sum_add_distrib]
  have hExcess : E =
      nativeTailDegreeExcessTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) := by
    calc
      E = ∑ Q ∈ D.ground.powersetCard 2,
          ∑ P ∈ nonemptyCommonRoots D.K D.ground,
            actualSelectedPairExcessAtBase D Q P := by
              unfold E
              apply Finset.sum_congr rfl
              intro Q hQ
              exact actual_unordered_excess_eq_used_pair_sum D Q hQ
      _ = ∑ P ∈ nonemptyCommonRoots D.K D.ground,
          ∑ Q ∈ D.ground.powersetCard 2,
            actualSelectedPairExcessAtBase D Q P := by
              rw [Finset.sum_comm]
      _ = _ := actual_selected_excess_used_total_eq_native_degree_excess_total
        D fallback hCenters
  have hNative := native_tail_degree_excess_facet_ledger
    D.K D.ground fallback D.uniform_four hCenters
  rw [hExcess] at hGraph
  omega

end JSP523.Rank4
