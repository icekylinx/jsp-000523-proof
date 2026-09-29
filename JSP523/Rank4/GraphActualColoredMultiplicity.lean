import JSP523.Rank4.GraphColoredFacetClassification
import JSP523.Rank4.GraphActualEligibleSlots
import JSP523.Rank4.GraphMarkedCapacity

/-!
# Two-color obstruction for a colored completion facet

The common neighbors of two selected pair-link vertices receive pair
labels in their common base pair. A colored facet makes every triangle
of these neighbors rainbow. Since the base pair has two vertices, the
common-neighbor set has size at most two, as used before (III.B.10).
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Three common neighbors cannot form a rainbow labeled triangle when
all three labels lie in the same two-element base pair. -/
theorem colored_shared_neighbor_card_le_two
    (D : FiniteCompletionCliqueData α)
    (C N Q : Finset α)
    (hNC : N ⊆ C)
    (hQ : Q.card ≤ 2)
    (hRainbow : CompletionTriangleRainbow D C)
    (hLabels : ∀ a ∈ N, ∀ b ∈ N,
      a ≠ b → D.label a b ∈ Q) :
    N.card ≤ 2 := by
  classical
  by_contra hNot
  have hLarge : 2 < N.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hLarge
  have hColors := hRainbow a (hNC ha) b (hNC hb) c (hNC hc)
    hab hac hbc
  have hAB := hLabels a ha b hb hab
  have hAC := hLabels a ha c hc hac
  have hBC := hLabels b hb c hc hbc
  have hColorSet :
      ({D.label a b, D.label a c, D.label b c} : Finset α).card = 3 :=
    Finset.card_eq_three.mpr
      ⟨D.label a b, D.label a c, D.label b c,
        hColors.1, hColors.2.1, hColors.2.2, rfl⟩
  have hColorSubset :
      ({D.label a b, D.label a c, D.label b c} : Finset α) ⊆ Q := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hBC
  have hAtMost := Finset.card_le_card hColorSubset
  omega

/-- A rainbow facet slot has at most two common neighbors with any
other distinct slot in the actual raw pair link. -/
theorem rainbow_slot_raw_common_multiplicity_le_two
    [Fintype α]
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (x y : α)
    (hxU : x ∈ D.ground) (hxQ : x ∉ Q)
    (hyU : y ∈ D.ground) (hyQ : y ∉ Q)
    (hxy : x ≠ y)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (insert x Q))) :
    graphCommonMultiplicity (rawPairLinkGraph D.K D.ground Q) x y ≤ 2 := by
  classical
  let F := rawPairLinkGraph D.K D.ground Q
  let N := (F.neighborFinset x).filter fun z => F.Adj y z
  have hQsub : Q ⊆ D.ground := (Finset.mem_powersetCard.mp hQ).1
  have hQcard : Q.card = 2 := (Finset.mem_powersetCard.mp hQ).2
  have hTxcard : (insert x Q).card = 3 := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
  have hTycard : (insert y Q).card = 3 := by
    rw [Finset.card_insert_of_notMem hyQ, hQcard]
  have hTxsub : insert x Q ⊆ D.ground :=
    Finset.insert_subset hxU hQsub
  have hTysub : insert y Q ⊆ D.ground :=
    Finset.insert_subset hyU hQsub
  have hNeighborX (z : α) (hz : z ∈ N) :
      z ∈ graphFacetCompletions D.K D.ground (insert x Q) := by
    have hAdj : F.Adj x z := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_filter.mp hz).1
    exact (raw_pair_link_slot_adj_iff_facet_completion
      D Q hQ x z hxU hxQ).mp hAdj
  have hNeighborY (z : α) (hz : z ∈ N) :
      z ∈ graphFacetCompletions D.K D.ground (insert y Q) := by
    have hAdj : F.Adj y z := (Finset.mem_filter.mp hz).2
    exact (raw_pair_link_slot_adj_iff_facet_completion
      D Q hQ y z hyU hyQ).mp hAdj
  have hLabels : ∀ a ∈ N, ∀ b ∈ N,
      a ≠ b → D.label a b ∈ Q := by
    intro a ha b hb hab
    have hLabelX := completion_pair_label_mem_facet D
      (insert x Q) hTxcard hTxsub a b
        (hNeighborX a ha) (hNeighborX b hb) hab
    have hLabelY := completion_pair_label_mem_facet D
      (insert y Q) hTycard hTysub a b
        (hNeighborY a ha) (hNeighborY b hb) hab
    rcases Finset.mem_insert.mp hLabelY with hEq | hInQ
    · have hYX := Finset.mem_insert.mp (hEq ▸ hLabelX)
      rcases hYX with hYX | hYQ
      · exact False.elim (hxy hYX.symm)
      · exact False.elim (hyQ hYQ)
    · exact hInQ
  have hNcard := colored_shared_neighbor_card_le_two
    D (graphFacetCompletions D.K D.ground (insert x Q)) N Q
      (by intro z hz; exact hNeighborX z hz)
      (by omega) hRainbow hLabels
  exact hNcard

/-- The same two-common-neighbor bound holds in the actually selected
pair link, for every choice of selected vertices. -/
theorem rainbow_slot_selected_common_multiplicity_le_two
    [Fintype α]
    (D : FiniteCompletionCliqueData α)
    (S : Finset α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    [DecidableRel (selectedCompletionPairGraph D S Q).Adj]
    (x y : α)
    (hxU : x ∈ D.ground) (hxQ : x ∉ Q)
    (hyU : y ∈ D.ground) (hyQ : y ∉ Q)
    (hxy : x ≠ y)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (insert x Q))) :
    graphCommonMultiplicity (selectedCompletionPairGraph D S Q) x y ≤ 2 := by
  classical
  calc
    graphCommonMultiplicity (selectedCompletionPairGraph D S Q) x y ≤
        graphCommonMultiplicity (rawPairLinkGraph D.K D.ground Q) x y := by
      apply graph_common_multiplicity_le_of_adj_mono
        (F := selectedCompletionPairGraph D S Q)
        (G := rawPairLinkGraph D.K D.ground Q)
      intro a b hab
      simpa only [completion_pair_link_eq_raw D Q] using hab.1
    _ ≤ 2 := rainbow_slot_raw_common_multiplicity_le_two
      D Q hQ x y hxU hxQ hyU hyQ hxy hRainbow

/-- The selected-link colored-slot bound in the exact predicate used
by the manuscript's slot selection. -/
theorem actual_colored_slot_common_multiplicity_le_two
    [Fintype α]
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (x y : α)
    (hxU : x ∈ D.ground) (hxQ : x ∉ Q)
    (hyU : y ∈ D.ground) (hyQ : y ∉ Q)
    (hxy : x ≠ y)
    (hColored : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground (insert x Q)) D.label) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) x y ≤ 2 := by
  classical
  have hQparts := Finset.mem_powersetCard.mp hQ
  have hTcard : (insert x Q).card = 3 := by
    rw [Finset.card_insert_of_notMem hxQ, hQparts.2]
  have hTsub : insert x Q ⊆ D.ground :=
    Finset.insert_subset hxU hQparts.1
  have hNoMono := divergent_completion_facet_no_monochromatic_triangle
    D (insert x Q) hTcard hTsub hColored
  have hRainbow := completion_facet_triangle_rainbow_of_no_mono
    D (insert x Q) hTcard hNoMono
  exact rainbow_slot_selected_common_multiplicity_le_two
    D (actualEligiblePairSlotVertices D Q) Q hQ
      x y hxU hxQ hyU hyQ hxy hRainbow

/-- A vertex outside the selected set has no common neighbors in the
selected pair link. -/
theorem selected_pair_link_common_multiplicity_zero_of_not_mem
    [Fintype α]
    (D : FiniteCompletionCliqueData α)
    (S : Finset α) (Q : Edge α)
    [DecidableRel (selectedCompletionPairGraph D S Q).Adj]
    (x y : α) (hy : y ∉ S) :
    graphCommonMultiplicity (selectedCompletionPairGraph D S Q) x y = 0 := by
  classical
  unfold graphCommonMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro z hz
  have hAdj := (Finset.mem_filter.mp hz).2
  exact hy hAdj.2.1

/-- The actual colored slots of completion degree three whose full
facet degree survives in the selected pair link. -/
noncomputable def actualColoredMarkedThreeSlots
    [Fintype α] (D : FiniteCompletionCliqueData α)
    (Q : Edge α) : Finset α := by
  classical
  exact D.ground.filter fun x =>
    x ∉ Q ∧
      (graphFacetCompletions D.K D.ground (insert x Q)).card = 3 ∧
      FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground (insert x Q)) D.label ∧
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x = 3

/-- The analogous marked slots of completion degree four. -/
noncomputable def actualColoredMarkedFourSlots
    [Fintype α] (D : FiniteCompletionCliqueData α)
    (Q : Edge α) : Finset α := by
  classical
  exact D.ground.filter fun x =>
    x ∉ Q ∧
      (graphFacetCompletions D.K D.ground (insert x Q)).card = 4 ∧
      FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground (insert x Q)) D.label ∧
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x = 4

/-- The actual marked sets satisfy every premise of the marked graph
deficit inequality at one base pair. -/
theorem actual_colored_marked_pair_link_payment
    [Fintype α]
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2) :
    let F := selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q
    orderedUniquePairCount F / 4 +
      ((actualColoredMarkedThreeSlots D Q).card : ℚ) / 2 +
      ((actualColoredMarkedFourSlots D Q).card : ℚ) ≤
    graphDeficit F := by
  classical
  let S := actualEligiblePairSlotVertices D Q
  let F := selectedCompletionPairGraph D S Q
  let M3 := actualColoredMarkedThreeSlots D Q
  let M4 := actualColoredMarkedFourSlots D Q
  have hDisj : Disjoint M3 M4 := by
    apply Finset.disjoint_left.mpr
    intro x hx3 hx4
    have h3 := (Finset.mem_filter.mp hx3).2.2.1
    have h4 := (Finset.mem_filter.mp hx4).2.2.1
    omega
  have hMarked (m : ℕ) (x : α)
      (hxU : x ∈ D.ground) (hxQ : x ∉ Q)
      (hColored : FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground (insert x Q)) D.label)
      (hDegree : F.degree x = m) :
      F.degree x = m ∧
        ∀ y : α, y ≠ x → graphCommonMultiplicity F x y ≤ 2 := by
    refine ⟨hDegree, ?_⟩
    intro y hxy
    by_cases hyS : y ∈ S
    · have hS := (Finset.mem_filter.mp hyS)
      exact actual_colored_slot_common_multiplicity_le_two
        D Q hQ x y hxU hxQ hS.1 hS.2.1 hxy.symm hColored
    · rw [selected_pair_link_common_multiplicity_zero_of_not_mem
        D S Q x y hyS]
      omega
  have h3 : ∀ x ∈ M3, F.degree x = 3 ∧
      ∀ y : α, y ≠ x → graphCommonMultiplicity F x y ≤ 2 := by
    intro x hx
    have h := Finset.mem_filter.mp hx
    exact hMarked 3 x h.1 h.2.1 h.2.2.2.1 h.2.2.2.2
  have h4 : ∀ x ∈ M4, F.degree x = 4 ∧
      ∀ y : α, y ≠ x → graphCommonMultiplicity F x y ≤ 2 := by
    intro x hx
    have h := Finset.mem_filter.mp hx
    exact hMarked 4 x h.1 h.2.1 h.2.2.2.1 h.2.2.2.2
  exact graph_deficit_marked F M3 M4 hDisj h3 h4

end JSP523.Rank4
