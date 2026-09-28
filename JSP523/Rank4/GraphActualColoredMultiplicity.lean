import JSP523.Rank4.GraphColoredFacetClassification
import JSP523.Rank4.GraphActualEligibleSlots

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
    D (insert x Q) hNoMono
  exact rainbow_slot_selected_common_multiplicity_le_two
    D (actualEligiblePairSlotVertices D Q) Q hQ
      x y hxU hxQ hyU hyQ hxy hRainbow

end JSP523.Rank4
