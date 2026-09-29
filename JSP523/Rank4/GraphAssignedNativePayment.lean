import JSP523.Rank4.GraphAssignedNativeIdentity
import JSP523.Rank4.PreprocessReciprocalAssembly

/-! # Rank-four deficit using the retained completion labels -/

namespace JSP523.Rank4.AssignedNative

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem actual_graph_squared_accounting_identity
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α) :
    2 * (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) : ℚ) +
      actualSelectedDegreeSquareTotal D +
      actualSelectedActiveVertexTotal D + 8 * (D.K.card : ℚ) =
    2 * actualFacetCompletionDegreeSquareTotal D +
      4 * (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  classical
  let R3 := ∑ T ∈ D.ground.powersetCard 3,
    (facetCompletions D.K D.ground T).card.choose 2
  have hB8 := actual_native_representation_iii_b8 D fallback
  have hB8q : (actualSelectedDegreePairTotal D : ℚ) +
      (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) : ℚ) =
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
    (fallback : α) :
    2 * (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) : ℚ) =
      2 * actualFacetCompletionDegreeSquareTotal D -
        actualSelectedDegreeSquareTotal D -
        actualSelectedActiveVertexTotal D - 8 * (D.K.card : ℚ) +
        4 * (actualSelectedEdgeTotal D : ℚ) +
        2 * actualSelectedPotentialTotal D := by
  have h := actual_graph_squared_accounting_identity
    D hGround fallback
  linarith


theorem actual_native_facet_slot_accounting
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α) :
    2 * (nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) : ℚ) =
      (∑ T ∈ D.ground.powersetCard 3,
        actualFacetSlotBracket D T) -
      8 * (D.K.card : ℚ) +
      4 * (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  have hGraph := actual_graph_squared_accounting_identity
    D hGround fallback
  have hBracket := actual_global_facet_slot_bracket_identity D
  linarith

/-- The exact actual facet-side accounting after classifying private,
monochromatic, and colored facets and using the selected graph
handshake. The only graph edge term left is `-e_*`. -/
theorem actual_native_classified_facet_accounting
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α) :
    2 * (nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) : ℚ) =
      2 * ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      5 * (∑ T ∈ actualMonochromaticFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) -
      2 * ((actualMonochromaticFacets D).card : ℚ) +
      (∑ T ∈ actualColoredFacets D,
        (-((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
          (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3)) +
      (∑ T ∈ actualMonochromaticFacets D,
        actualFacetSlotSlackSum D T) +
      (∑ T ∈ actualColoredFacets D,
        actualFacetSlotSlackSum D T) -
      8 * (D.K.card : ℚ) -
      (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  have hNative := actual_native_facet_slot_accounting
    D hGround fallback
  rw [actual_global_facet_bracket_by_type] at hNative
  have hDegrees := actual_facet_selected_degree_sum_eq_twice_edges D
  rw [actual_facet_selected_degree_sum_by_type] at hDegrees
  unfold actualMonochromaticBracketTerm actualColoredBracketTerm at hNative
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hNative ⊢
  linarith

/-- The complete actual facet-side signed balance for `2S`, before
the retained-edge occurrence count is exchanged for `Z` and `R`.
All colored coefficients are actual rainbow/proper-K4 facet counts. -/
theorem actual_facet_side_signed_balance
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α) :
    2 * (nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) : ℚ) +
      4 * ((rankFourFacetShadow D.K D.ground).card : ℚ) -
      10 * (D.K.card : ℚ) =
    2 * (D.K.card : ℚ) +
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      2 * ((actualMonochromaticFacets D).card : ℚ) -
      (1 / 2) * ((actualColoredThreeFacets D).card : ℚ) -
      5 * ((actualColoredFourFacets D).card : ℚ) +
      (∑ T ∈ actualMonochromaticFacets D,
        actualFacetSlotSlackSum D T) +
      (∑ T ∈ actualColoredFacets D,
        actualFacetSlotSlackSum D T) -
      (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  have hNative := actual_native_classified_facet_accounting
    D hGround fallback
  have hColorBase := actual_colored_facet_base_sum D
  have hDegree := actual_facet_degree_count_by_colored_type D hGround
  have hShadow := actual_facet_shadow_card_by_type D
  have hShadowRat :
      ((rankFourFacetShadow D.K D.ground).card : ℚ) =
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      ((actualMonochromaticFacets D).card : ℚ) +
      ((actualColoredThreeFacets D).card : ℚ) +
      ((actualColoredFourFacets D).card : ℚ) := by
    exact_mod_cast hShadow
  linarith


theorem rank_four_actual_deficit_of_bounded_edge_exclusions
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (Z R : ℚ)
    (hEdge : (actualSelectedEdgeTotal D : ℚ) =
      2 * (D.K.card : ℚ) +
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) + R - Z)
    (hEdgeSlack : 6 *
      ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤ Z)
    (hReciprocalCharge : R ≤
      ((rankFourNonprivateFacets D.K D.ground).card : ℚ)) :
    10 * D.K.card +
      (rankFourNonprivateFacets D.K D.ground).card +
      6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
    2 * nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) +
      4 * (rankFourFacetShadow D.K D.ground).card := by
  have hFacet := actual_facet_side_signed_balance
    D hGround fallback
  have hNonprivate := actual_nonprivate_facet_card_by_type D
  have hNonprivateRat :
      ((rankFourNonprivateFacets D.K D.ground).card : ℚ) =
      ((actualMonochromaticFacets D).card : ℚ) +
      ((actualColoredThreeFacets D).card : ℚ) +
      ((actualColoredFourFacets D).card : ℚ) := by
    exact_mod_cast hNonprivate
  have hMixed := actual_mixed_colored_payment_on_facet_families D
  have hMono := actual_monochromatic_facet_slack_sum_nonneg D
  have hColor := actual_colored_signed_charge_of_mixed_payment
    D (actualColoredThreeFacets D).card (actualColoredFourFacets D).card
      (∑ T ∈ actualColoredFacets D, actualFacetSlotSlackSum D T)
      ((∑ T ∈ actualMonochromaticFacets D,
          actualFacetSlotSlackSum D T) +
        (∑ T ∈ actualColoredFacets D,
          actualFacetSlotSlackSum D T))
      hMixed (by linarith)
  have hDeficitRat :
      (10 * D.K.card +
        (rankFourNonprivateFacets D.K D.ground).card +
        6 * (rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
      (2 * nativeTailVertexTotal D.K D.ground
          (nonemptyCommonRoots D.K D.ground)
            (dataRootLabel D fallback) +
        4 * (rankFourFacetShadow D.K D.ground).card : ℕ) := by
    push_cast
    linarith
  exact_mod_cast hDeficitRat


theorem rank_four_full_cleanup_deficit_of_edge_balance
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hSeparated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D))
    (Z : ℚ)
    (hEdge : (actualSelectedEdgeTotal (clearReciprocalFully D) : ℚ) =
      2 * ((clearReciprocalFully D).K.card : ℚ) +
      ((rankFourPrivateFacets
        (clearReciprocalFully D).K D.ground).card : ℚ) +
      3 * ((actualColoredThreeFacets
        (clearReciprocalFully D)).card : ℚ) +
      4 * ((actualColoredFourFacets
        (clearReciprocalFully D)).card : ℚ) +
      ((∑ E ∈ (clearReciprocalFully D).K,
        (actualEdgeReciprocalExclusions
          (clearReciprocalFully D) E).card) : ℚ) - Z)
    (hEdgeSlack : 6 *
      ((rankFourAllPrivateEdges
        (clearReciprocalFully D).K D.ground).card : ℚ) ≤ Z) :
    10 * (clearReciprocalFully D).K.card +
      (rankFourNonprivateFacets
        (clearReciprocalFully D).K D.ground).card +
      6 * (rankFourAllPrivateEdges
        (clearReciprocalFully D).K D.ground).card ≤
    2 * nativeTailVertexTotal
      (clearReciprocalFully D).K D.ground
      (nonemptyCommonRoots
        (clearReciprocalFully D).K D.ground)
        (dataRootLabel (clearReciprocalFully D) fallback) +
      4 * (rankFourFacetShadow
        (clearReciprocalFully D).K D.ground).card := by
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have hGround₂ : ∀ E ∈ D₂.K, E ⊆ D.ground := by
    intro E hE
    exact hGround E
      (clear_reciprocal_different_witnesses_sub D
        (clear_reciprocal_wrong_common_witnesses_sub D₁ hE))
  have hR := clear_reciprocal_fully_edge_exclusions_le_nonprivate
    D hGround hSeparated
  have hRRat :
      ((∑ E ∈ D₂.K,
        (actualEdgeReciprocalExclusions D₂ E).card) : ℚ) ≤
      ((rankFourNonprivateFacets D₂.K D.ground).card : ℚ) := by
    exact_mod_cast hR
  exact rank_four_actual_deficit_of_bounded_edge_exclusions
    D₂ fallback hGround₂ Z
      ((∑ E ∈ D₂.K,
        (actualEdgeReciprocalExclusions D₂ E).card) : ℚ)
      hEdge hEdgeSlack hRRat


theorem rank_four_full_cleanup_deficit
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
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
        (dataRootLabel (clearReciprocalFully D) fallback) +
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
    hGround hSeparated
    (∑ E ∈ D₂.K, (actualEdgeSlack D₂ E : ℚ)) hEdge
    (actual_edge_slack_sum_ge_all_private D₂ hGround₂)


end JSP523.Rank4.AssignedNative
