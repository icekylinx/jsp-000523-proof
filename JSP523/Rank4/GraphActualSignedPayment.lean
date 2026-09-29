import JSP523.Rank4.GraphActualFacetBracket
import JSP523.Rank4.GraphActualColoredSlackBridge
import JSP523.Rank4.GraphActualPaymentBridge
import JSP523.Rank4.GraphReciprocalAccounting

/-!
# Assembling the signed payment in (III.B.9)

This module isolates the final exact algebra after facet-slot and edge
accounting.  The reciprocal term is the actual finite occurrence set;
its charge to nonprivate facets uses the degree-two theorem.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The facet accounting becomes the manuscript's signed identity
once the selected-edge occurrence total is expressed via edge slack
and reciprocal occurrences. -/
theorem actual_signed_identity_of_edge_occurrence_balance
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (Z : ℚ)
    (hEdge : (actualSelectedEdgeTotal D : ℚ) =
      2 * (D.K.card : ℚ) +
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) +
      ((actualReciprocalUnorderedOccurrences D).card : ℚ) - Z) :
    (nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
          (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) +
      2 * ((rankFourFacetShadow D.K D.ground).card : ℚ) -
      5 * (D.K.card : ℚ) =
    ((rankFourNonprivateFacets D.K D.ground).card : ℚ) -
      ((actualReciprocalUnorderedOccurrences D).card : ℚ) / 2 +
      Z / 2 -
      (11 / 4) * ((actualColoredThreeFacets D).card : ℚ) -
      (11 / 2) * ((actualColoredFourFacets D).card : ℚ) +
      ((∑ T ∈ actualMonochromaticFacets D,
          actualFacetSlotSlackSum D T) +
        (∑ T ∈ actualColoredFacets D,
          actualFacetSlotSlackSum D T)) / 2 +
      actualSelectedPotentialTotal D := by
  have hFacet := actual_facet_side_signed_balance
    D hGround fallback hCenters
  have hNonprivate := actual_nonprivate_facet_card_by_type D
  have hNonprivateRat :
      ((rankFourNonprivateFacets D.K D.ground).card : ℚ) =
      ((actualMonochromaticFacets D).card : ℚ) +
      ((actualColoredThreeFacets D).card : ℚ) +
      ((actualColoredFourFacets D).card : ℚ) := by
    exact_mod_cast hNonprivate
  linarith

/-- The mixed colored payment is stronger than the colored charge
appearing in the signed (III.B.9) identity. -/
theorem actual_colored_signed_charge_of_mixed_payment
    (D : FiniteCompletionCliqueData α)
    (r3 r4 : ℕ) (coloredSlack G : ℚ)
    (hMixed :
      3 * (r3 : ℚ) + 6 * (r4 : ℚ) ≤
        actualSelectedPotentialTotal D + coloredSlack / 2)
    (hSlack : coloredSlack ≤ G) :
    (11 / 4) * (r3 : ℚ) + (11 / 2) * (r4 : ℚ) ≤
      G / 2 + actualSelectedPotentialTotal D := by
  have hr3 : (0 : ℚ) ≤ r3 := Nat.cast_nonneg _
  have hr4 : (0 : ℚ) ≤ r4 := Nat.cast_nonneg _
  linarith

/-- The actual (III.B.9) identity, colored payment, nonnegative edge
slack, and degree-two reciprocal incidence bound imply the finite
rank-four deficit.  The signed identity and colored payment remain
explicit, independently checkable premises. -/
theorem rank_four_actual_deficit_of_signed_identity
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (r3 r4 : ℕ) (Z G : ℚ)
    (hSigned :
      (nativeTailVertexTotal D.K D.ground
          (nonemptyCommonRoots D.K D.ground)
            (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) +
        2 * ((rankFourFacetShadow D.K D.ground).card : ℚ) -
        5 * (D.K.card : ℚ) =
      ((rankFourNonprivateFacets D.K D.ground).card : ℚ) -
        ((actualReciprocalUnorderedOccurrences D).card : ℚ) / 2 +
        Z / 2 - (11 / 4) * (r3 : ℚ) -
        (11 / 2) * (r4 : ℚ) + G / 2 +
        actualSelectedPotentialTotal D)
    (hColored :
      (11 / 4) * (r3 : ℚ) + (11 / 2) * (r4 : ℚ) ≤
        G / 2 + actualSelectedPotentialTotal D)
    (hEdgeSlack : 6 *
      ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤ Z)
    (hReciprocalDegreeTwo :
      ∀ p ∈ actualReciprocalDirectedOccurrences D,
        (graphFacetCompletions D.K D.ground
          (p.1.erase p.2.1)).card = 2) :
    10 * D.K.card +
      (rankFourNonprivateFacets D.K D.ground).card +
      6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
    2 * nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) +
      4 * (rankFourFacetShadow D.K D.ground).card := by
  have hReciprocal := actual_reciprocal_unordered_card_le_nonprivate
    D hGround hReciprocalDegreeTwo
  have hReciprocalRat :
      ((actualReciprocalUnorderedOccurrences D).card : ℚ) ≤
        ((rankFourNonprivateFacets D.K D.ground).card : ℚ) := by
    exact_mod_cast hReciprocal
  have hDeficitRat :
      (10 * D.K.card +
        (rankFourNonprivateFacets D.K D.ground).card +
        6 * (rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
      (2 * nativeTailVertexTotal D.K D.ground
          (nonemptyCommonRoots D.K D.ground)
            (chosenCommonRootLabel D.K D.ground fallback hCenters) +
        4 * (rankFourFacetShadow D.K D.ground).card : ℕ) := by
    push_cast
    linarith
  exact_mod_cast hDeficitRat

/-- Actual colored payment and monochromatic slack close the signed
facet argument; only edge occurrence slack and reciprocal incidence
remain as combinatorial inputs. -/
theorem rank_four_actual_deficit_of_edge_occurrence_balance
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (Z : ℚ)
    (hEdge : (actualSelectedEdgeTotal D : ℚ) =
      2 * (D.K.card : ℚ) +
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) +
      ((actualReciprocalUnorderedOccurrences D).card : ℚ) - Z)
    (hEdgeSlack : 6 *
      ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤ Z)
    (hReciprocalDegreeTwo :
      ∀ p ∈ actualReciprocalDirectedOccurrences D,
        (graphFacetCompletions D.K D.ground
          (p.1.erase p.2.1)).card = 2) :
    10 * D.K.card +
      (rankFourNonprivateFacets D.K D.ground).card +
      6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
    2 * nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) +
      4 * (rankFourFacetShadow D.K D.ground).card := by
  let coloredSlack : ℚ :=
    ∑ T ∈ actualColoredFacets D, actualFacetSlotSlackSum D T
  let G : ℚ :=
    (∑ T ∈ actualMonochromaticFacets D,
      actualFacetSlotSlackSum D T) + coloredSlack
  have hMixed := actual_mixed_colored_payment_on_facet_families D
  have hMono := actual_monochromatic_facet_slack_sum_nonneg D
  have hColored := actual_colored_signed_charge_of_mixed_payment
    D (actualColoredThreeFacets D).card (actualColoredFourFacets D).card
      coloredSlack G hMixed (by dsimp [G]; linarith)
  exact rank_four_actual_deficit_of_signed_identity D fallback hGround hCenters
    (actualColoredThreeFacets D).card (actualColoredFourFacets D).card Z G
    (actual_signed_identity_of_edge_occurrence_balance
      D fallback hGround hCenters Z hEdge)
    hColored hEdgeSlack hReciprocalDegreeTwo

/-- The final payment can use the reciprocal exclusion count supplied
by the edge decomposition directly. Its only local charging input is
the bound by the nonprivate facet count. -/
theorem rank_four_actual_deficit_of_bounded_edge_exclusions
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
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
        (chosenCommonRootLabel D.K D.ground fallback hCenters) +
      4 * (rankFourFacetShadow D.K D.ground).card := by
  have hFacet := actual_facet_side_signed_balance
    D hGround fallback hCenters
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
            (chosenCommonRootLabel D.K D.ground fallback hCenters) +
        4 * (rankFourFacetShadow D.K D.ground).card : ℕ) := by
    push_cast
    linarith
  exact_mod_cast hDeficitRat

end JSP523.Rank4
