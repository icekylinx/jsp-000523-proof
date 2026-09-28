import JSP523.Rank4.GraphCommonExcessLedger
import JSP523.Rank4.GraphActualEligibleSlots

/-!
# Support of selected pair-link common-neighbor excess

Only used completion pairs can have a common neighbor. A base pair
containing either endpoint of the completion pair has multiplicity zero.
These are the support facts needed to reindex the selected excess in
(III.B.8).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- If a graph vertex has no incident edges, every common multiplicity
with that vertex is zero. -/
theorem graph_common_multiplicity_zero_of_no_neighbors
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (a b : α) (hNo : ∀ x, ¬ F.Adj a x) :
    graphCommonMultiplicity F a b = 0 := by
  have hEmpty : F.neighborFinset a = ∅ := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, hNo x]
  simp [graphCommonMultiplicity, hEmpty]

omit [Fintype α] in
/-- A selected pair link has no incident edge at a vertex lying in its
base pair. -/
theorem actual_selected_pair_link_no_edges_at_base
    (D : FiniteCompletionCliqueData α) (Q : Edge α)
    (a : α) (haQ : a ∈ Q) :
    ∀ x, ¬ (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q).Adj a x := by
  intro x hAdj
  exact hAdj.1.1 haQ

/-- A completion endpoint lying in the base pair has no common
neighbors in the actual selected pair link. -/
theorem actual_selected_common_zero_of_left_mem_base
    (D : FiniteCompletionCliqueData α) (Q : Edge α)
    (a b : α) (haQ : a ∈ Q) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b = 0 := by
  classical
  exact graph_common_multiplicity_zero_of_no_neighbors _ a b
    (actual_selected_pair_link_no_edges_at_base D Q a haQ)

/-- The same zero statement for the right completion endpoint. -/
theorem actual_selected_common_zero_of_right_mem_base
    (D : FiniteCompletionCliqueData α) (Q : Edge α)
    (a b : α) (hbQ : b ∈ Q) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b = 0 := by
  classical
  rw [graph_common_multiplicity_symm]
  exact actual_selected_common_zero_of_left_mem_base D Q b a hbQ

/-- A positive common-neighbor multiplicity in an actual selected
pair link certifies that its endpoint pair is a used completion pair. -/
theorem actual_selected_common_positive_implies_used
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (a b : α) (hab : a ≠ b)
    (hPos : 0 < graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b) :
    ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground := by
  classical
  let F := selectedCompletionPairGraph D
    (actualEligiblePairSlotVertices D Q) Q
  unfold graphCommonMultiplicity at hPos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hPos
  have hx' := Finset.mem_filter.mp hx
  have hAx : F.Adj a x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx'.1
  have hBx : F.Adj b x := hx'.2
  have hRawAx : (rawPairLinkGraph D.K D.ground Q).Adj a x := hAx.1
  have hRawBx : (rawPairLinkGraph D.K D.ground Q).Adj b x := hBx.1
  have haU : a ∈ D.ground :=
    ((rawPairLinkGraph_adj D.K D.ground Q a x).mp hRawAx).2.2.1
  have hbU : b ∈ D.ground :=
    ((rawPairLinkGraph_adj D.K D.ground Q b x).mp hRawBx).2.2.1
  have hCell := raw_pair_common_neighbor_gives_cell
    D.K D.ground Q D.uniform_four hQ a b x haU hbU hab
    hRawAx hRawBx
  apply Finset.mem_filter.mpr
  refine ⟨?_, Finset.card_pos.mpr ⟨insert x Q, hCell⟩⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, Finset.card_pair hab⟩
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact haU
  · exact (Finset.mem_singleton.mp ht) ▸ hbU

/-- Unused completion pairs have zero common-neighbor multiplicity in
every actual selected pair link over a valid base pair. -/
theorem actual_selected_common_zero_of_unused
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (a b : α) (hab : a ≠ b)
    (hUnused : ({a, b} : Edge α) ∉
      nonemptyCommonRoots D.K D.ground) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b = 0 := by
  by_contra h
  have hPos : 0 < graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b := by omega
  exact hUnused
    (actual_selected_common_positive_implies_used D Q hQ a b hab hPos)

end JSP523.Rank4
