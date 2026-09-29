import JSP523.Rank4.GraphActualEdgeReindex
import JSP523.Rank4.GraphActualFacetSlotReindex
import JSP523.Rank4.GraphActualEdgeSlack
import JSP523.Rank4.GraphActualReciprocalCharge

/-!
# Global edge and facet incidence balance in (III.B.9)

Each four-edge has four opposite triple facets. Reindexing these
incidences by the triple facet gives its completion degree.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Erasing one vertex of a four-set enumerates its four triple facets. -/
theorem four_set_opposite_facets_eq_powersetCard
    (E : Edge α) (hE : E.card = 4) :
    E.image (fun a => E.erase a) = E.powersetCard 3 := by
  classical
  have hSub : E.image (fun a => E.erase a) ⊆ E.powersetCard 3 := by
    intro T hT
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.erase_subset _ _, by
        rw [Finset.card_erase_of_mem ha, hE]⟩
  have hInj : Set.InjOn (fun a => E.erase a) E :=
    Finset.erase_injOn E
  have hCard : (E.image (fun a => E.erase a)).card =
      (E.powersetCard 3).card := by
    rw [Finset.card_image_of_injOn hInj,
      Finset.card_powersetCard, hE]
    decide
  exact Finset.eq_of_subset_of_card_le hSub (by omega)

omit [Fintype α] in
/-- A weighted opposite-facet sum on one four-edge. -/
theorem four_set_opposite_facet_sum
    (E : Edge α) (hE : E.card = 4) (f : Edge α → ℚ) :
    (∑ a ∈ E, f (E.erase a)) =
      ∑ T ∈ E.powersetCard 3, f T := by
  classical
  rw [← four_set_opposite_facets_eq_powersetCard E hE]
  symm
  exact Finset.sum_image (Finset.erase_injOn E)

omit [Fintype α] in
/-- The global weighted incidence identity for actual rank-four facets. -/
theorem actual_opposite_facet_weighted_sum
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (f : Edge α → ℚ) :
    (∑ E ∈ D.K, ∑ a ∈ E, f (E.erase a)) =
      ∑ T ∈ D.ground.powersetCard 3,
        ((facetCompletions D.K D.ground T).card : ℚ) * f T := by
  classical
  let C := D.ground.powersetCard 3
  have hPerEdge (E : Edge α) (hE : E ∈ D.K) :
      (∑ a ∈ E, f (E.erase a)) =
        ∑ T ∈ C, if T ⊆ E then f T else 0 := by
    rw [four_set_opposite_facet_sum E (D.uniform_four hE)]
    have hSet : C.filter (fun T => T ⊆ E) = E.powersetCard 3 := by
      ext T
      constructor
      · intro hT
        have h := Finset.mem_filter.mp hT
        exact Finset.mem_powersetCard.mpr
          ⟨h.2, (Finset.mem_powersetCard.mp h.1).2⟩
      · intro hT
        have h := Finset.mem_powersetCard.mp hT
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr
            ⟨h.1.trans (hGround E hE), h.2⟩, h.1⟩
    rw [← hSet, Finset.sum_filter]
  calc
    (∑ E ∈ D.K, ∑ a ∈ E, f (E.erase a)) =
        ∑ E ∈ D.K, ∑ T ∈ C, if T ⊆ E then f T else 0 := by
          apply Finset.sum_congr rfl
          exact hPerEdge
    _ = ∑ T ∈ C, ∑ E ∈ D.K, if T ⊆ E then f T else 0 :=
      Finset.sum_comm
    _ = ∑ T ∈ C, ((rankFourFacetParents D.K T).card : ℚ) * f T := by
      apply Finset.sum_congr rfl
      intro T hT
      unfold rankFourFacetParents
      rw [← Finset.sum_filter]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [facet_completions_card_eq_parent_edges D.K D.ground T
        D.uniform_four hGround (Finset.mem_powersetCard.mp hT).2]

omit [Fintype α] in
/-- Counting only opposite facets in a specified family. -/
theorem actual_opposite_facet_membership_count
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (C : Family α) (hC : C ⊆ D.ground.powersetCard 3) :
    (∑ E ∈ D.K, ∑ a ∈ E,
      if E.erase a ∈ C then (1 : ℚ) else 0) =
      ∑ T ∈ C, ((facetCompletions D.K D.ground T).card : ℚ) := by
  classical
  rw [actual_opposite_facet_weighted_sum D hGround
    (fun T => if T ∈ C then (1 : ℚ) else 0)]
  calc
    (∑ T ∈ D.ground.powersetCard 3,
      ((facetCompletions D.K D.ground T).card : ℚ) *
        if T ∈ C then (1 : ℚ) else 0) =
        ∑ T ∈ D.ground.powersetCard 3,
          if T ∈ C then
            ((facetCompletions D.K D.ground T).card : ℚ) else 0 := by
              apply Finset.sum_congr rfl
              intro T _
              split_ifs <;> simp
    _ = ∑ T ∈ (D.ground.powersetCard 3).filter (· ∈ C),
        ((facetCompletions D.K D.ground T).card : ℚ) := by
          rw [Finset.sum_filter]
    _ = _ := by
      congr 1
      ext T
      simp [hC]

omit [Fintype α] in
/-- Private opposite-facet incidences are counted once each. -/
theorem actual_private_opposite_facet_row_count
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    (∑ E ∈ D.K, ∑ a ∈ E,
      if E.erase a ∈ rankFourPrivateFacets D.K D.ground
      then (1 : ℚ) else 0) =
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) := by
  classical
  have hSub : rankFourPrivateFacets D.K D.ground ⊆
      D.ground.powersetCard 3 := Finset.filter_subset _ _
  rw [actual_opposite_facet_membership_count D hGround _ hSub]
  calc
    (∑ T ∈ rankFourPrivateFacets D.K D.ground,
      ((facetCompletions D.K D.ground T).card : ℚ)) =
        ∑ _T ∈ rankFourPrivateFacets D.K D.ground, (1 : ℚ) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact_mod_cast (Finset.mem_filter.mp hT).2
    _ = _ := by simp

omit [Fintype α] in
/-- Colored opposite-facet incidences contribute `3r₃+4r₄`. -/
theorem actual_colored_opposite_facet_row_count
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    (∑ E ∈ D.K, ∑ a ∈ E,
      if E.erase a ∈ actualColoredFacets D
      then (1 : ℚ) else 0) =
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) := by
  classical
  have hSub : actualColoredFacets D ⊆
      D.ground.powersetCard 3 := Finset.filter_subset _ _
  rw [actual_opposite_facet_membership_count D hGround _ hSub]
  exact actual_colored_facet_degree_sum D

omit [Fintype α] in
/-- Private rows of an actual edge are exactly its private opposite
facets. -/
theorem actual_edge_private_row_iff_private_facet
    (D : FiniteCompletionCliqueData α)
    (E : Edge α) (hE : E ∈ D.K)
    (hGround : E ⊆ D.ground)
    (a : α) (ha : a ∈ E) :
    a ∈ actualEdgePrivateRows D E ↔
      E.erase a ∈ rankFourPrivateFacets D.K D.ground := by
  classical
  have hTcard : (E.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem ha, D.uniform_four hE]
  have hTsub : E.erase a ⊆ D.ground :=
    (Finset.erase_subset _ _).trans hGround
  simp only [actualEdgePrivateRows, rankFourPrivateFacets,
    Finset.mem_filter, Finset.mem_powersetCard]
  exact and_iff_right ha |>.trans
    (and_iff_right ⟨hTsub, hTcard⟩).symm

omit [Fintype α] in
/-- Colored rows of an actual edge are exactly its colored opposite
facets. -/
theorem actual_edge_colored_row_iff_colored_facet
    (D : FiniteCompletionCliqueData α)
    (E : Edge α) (hE : E ∈ D.K)
    (hGround : E ⊆ D.ground)
    (a : α) (ha : a ∈ E) :
    a ∈ actualEdgeColoredRows D E ↔
      E.erase a ∈ actualColoredFacets D := by
  classical
  have hTcard : (E.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem ha, D.uniform_four hE]
  have hTsub : E.erase a ⊆ D.ground :=
    (Finset.erase_subset _ _).trans hGround
  simp only [actualEdgeColoredRows, actualEdgeNonprivateRows,
    actualColoredFacets, Finset.mem_filter, Finset.mem_powersetCard]
  simp [ha, hTsub, hTcard,
    graphFacetCompletions, facetCompletions]

omit [Fintype α] in
/-- The sum of actual private opposite row counts is the private facet
count. -/
theorem actual_private_row_card_sum
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    (∑ E ∈ D.K, ((actualEdgePrivateRows D E).card : ℚ)) =
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) := by
  classical
  rw [← actual_private_opposite_facet_row_count D hGround]
  apply Finset.sum_congr rfl
  intro E hE
  have hPoint (a : α) (ha : a ∈ E) :
      (a ∈ actualEdgePrivateRows D E) ↔
        E.erase a ∈ rankFourPrivateFacets D.K D.ground :=
    actual_edge_private_row_iff_private_facet D E hE (hGround E hE) a ha
  rw [show actualEdgePrivateRows D E =
      E.filter (fun a => E.erase a ∈
        rankFourPrivateFacets D.K D.ground) by
        ext a
        by_cases ha : a ∈ E
        · simpa only [Finset.mem_filter, ha, true_and] using hPoint a ha
        · simp [actualEdgePrivateRows, ha]]
  rw [Finset.card_filter]
  push_cast
  rfl

omit [Fintype α] in
/-- The sum of actual colored opposite row counts is `3r₃+4r₄`. -/
theorem actual_colored_row_card_sum
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    (∑ E ∈ D.K, ((actualEdgeColoredRows D E).card : ℚ)) =
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) := by
  classical
  rw [← actual_colored_opposite_facet_row_count D hGround]
  apply Finset.sum_congr rfl
  intro E hE
  have hPoint (a : α) (ha : a ∈ E) :
      (a ∈ actualEdgeColoredRows D E) ↔
        E.erase a ∈ actualColoredFacets D :=
    actual_edge_colored_row_iff_colored_facet D E hE (hGround E hE) a ha
  rw [show actualEdgeColoredRows D E =
      E.filter (fun a => E.erase a ∈ actualColoredFacets D) by
        ext a
        by_cases ha : a ∈ E
        · simpa only [Finset.mem_filter, ha, true_and] using hPoint a ha
        · simp [actualEdgeColoredRows, actualEdgeNonprivateRows, ha]]
  rw [Finset.card_filter]
  push_cast
  rfl

omit [Fintype α] in
/-- The local signed reserve is exactly the difference between the
selected occurrence count and the four elementary edge counts. -/
theorem actual_edge_slack_point_balance
    (D : FiniteCompletionCliqueData α) (E : Edge α) :
    ((actualEdgeSelectedOccurrences D E).card : ℚ) +
      (actualEdgeSlack D E : ℚ) =
      2 + ((actualEdgeColoredRows D E).card : ℚ) +
        ((actualEdgePrivateRows D E).card : ℚ) +
        ((actualEdgeReciprocalExclusions D E).card : ℚ) := by
  unfold actualEdgeSlack
  push_cast
  ring

/-- Exact global selected-edge occurrence balance, including the
genuine double slot exclusions and the sum of nonnegative edge slack. -/
theorem actual_selected_edge_total_eq_signed_edge_balance
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    (actualSelectedEdgeTotal D : ℚ) =
      2 * (D.K.card : ℚ) +
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) +
      ((actualEdgeReciprocalExclusionOccurrences D).card : ℚ) -
      (∑ E ∈ D.K, (actualEdgeSlack D E : ℚ)) := by
  classical
  let Z : ℚ := ∑ E ∈ D.K, (actualEdgeSlack D E : ℚ)
  have hSelected : (actualSelectedEdgeTotal D : ℚ) =
      ∑ E ∈ D.K, ((actualEdgeSelectedOccurrences D E).card : ℚ) := by
    rw [actual_selected_edge_total_eq_sum_edge_occurrences D hGround]
    push_cast
    rfl
  have hReciprocal :
      ((actualEdgeReciprocalExclusionOccurrences D).card : ℚ) =
        ∑ E ∈ D.K,
          ((actualEdgeReciprocalExclusions D E).card : ℚ) := by
    rw [actual_edge_reciprocal_exclusion_occurrences_card]
    push_cast
    rfl
  have hPrivate := actual_private_row_card_sum D hGround
  have hColored := actual_colored_row_card_sum D hGround
  have hSum :
      (actualSelectedEdgeTotal D : ℚ) + Z =
        2 * (D.K.card : ℚ) +
        (∑ E ∈ D.K, ((actualEdgeColoredRows D E).card : ℚ)) +
        (∑ E ∈ D.K, ((actualEdgePrivateRows D E).card : ℚ)) +
        (∑ E ∈ D.K,
          ((actualEdgeReciprocalExclusions D E).card : ℚ)) := by
    rw [hSelected]
    change (∑ E ∈ D.K,
      ((actualEdgeSelectedOccurrences D E).card : ℚ)) +
        (∑ E ∈ D.K, (actualEdgeSlack D E : ℚ)) = _
    rw [← Finset.sum_add_distrib]
    conv_lhs =>
      arg 2
      ext E
      rw [actual_edge_slack_point_balance]
    simp only [Finset.sum_add_distrib]
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm, add_assoc]
  dsimp [Z] at hSum ⊢
  linarith

end JSP523.Rank4
