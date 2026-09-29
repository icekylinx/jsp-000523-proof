import JSP523.Rank4.GraphActualEdgeOccurrence
import JSP523.Rank4.GraphActualSignedPayment
import JSP523.Rank4.GraphReciprocalDegreeTwo

/-!
# Charging true double exclusions to nonprivate facets

The edgewise reciprocal correction in (III.B.9) consists of pairs
excluded at both selected slots. It embeds into the actual reciprocal
occurrences, and full reciprocal cleanup bounds those occurrences by
the number of nonprivate facets.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Genuine double exclusions, with their containing four-edge retained. -/
noncomputable def actualEdgeReciprocalExclusionOccurrences
    (D : FiniteCompletionCliqueData α) : Finset (Edge α × Edge α) := by
  classical
  exact (D.K.product (Finset.univ : Finset (Edge α))).filter fun p =>
    p.2 ∈ actualEdgeReciprocalExclusions D p.1

/-- The global double-exclusion count is the sum of its edgewise counts. -/
theorem actual_edge_reciprocal_exclusion_occurrences_card
    (D : FiniteCompletionCliqueData α) :
    (actualEdgeReciprocalExclusionOccurrences D).card =
      ∑ E ∈ D.K, (actualEdgeReciprocalExclusions D E).card := by
  classical
  let A := actualEdgeReciprocalExclusionOccurrences D
  have hMaps : (A : Set (Edge α × Edge α)).MapsTo Prod.fst D.K := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro E hE
  have hFiber : (A.filter fun p => p.1 = E) =
      ({E} : Finset (Edge α)).product
        (actualEdgeReciprocalExclusions D E) := by
    ext p
    rcases p with ⟨E', P⟩
    constructor
    · intro hp
      obtain ⟨hpA, hEq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hProd, hP⟩ := Finset.mem_filter.mp hpA
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hEq, hEq ▸ hP⟩
    · intro hp
      obtain ⟨hEq, hP⟩ := Finset.mem_product.mp hp
      have hEq' : E' = E := Finset.mem_singleton.mp hEq
      subst E'
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hE, Finset.mem_univ _⟩, hP⟩
      · rfl
  rw [hFiber]
  simp

/-- Every true double exclusion is an actual reciprocal occurrence. -/
theorem actual_edge_reciprocal_exclusion_occurrences_sub
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    actualEdgeReciprocalExclusionOccurrences D ⊆
      actualReciprocalUnorderedOccurrences D := by
  classical
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hE := (Finset.mem_product.mp hp'.1).1
  exact actual_edge_reciprocal_exclusion_implies_actual_reciprocal
    D p.1 p.2 hE (hGround p.1 hE) hp'.2

/-- Full reciprocal cleanup charges the edgewise double exclusions
to actual nonprivate facets. -/
theorem clear_reciprocal_fully_edge_exclusions_le_nonprivate
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hSeparated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D)) :
    (∑ E ∈ (clearReciprocalFully D).K,
      (actualEdgeReciprocalExclusions (clearReciprocalFully D) E).card) ≤
      (rankFourNonprivateFacets
        (clearReciprocalFully D).K D.ground).card := by
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have hGround₂ : ∀ E ∈ D₂.K, E ⊆ D.ground := by
    intro E hE
    exact hGround E
      (clear_reciprocal_different_witnesses_sub D
        (clear_reciprocal_wrong_common_witnesses_sub D₁ hE))
  rw [← actual_edge_reciprocal_exclusion_occurrences_card D₂]
  exact (Finset.card_le_card
    (actual_edge_reciprocal_exclusion_occurrences_sub D₂ hGround₂)).trans
      (clear_reciprocal_fully_unordered_card_le_nonprivate
        D hGround hSeparated)

/-- The full-cleanup rank-four deficit follows from the exact edge
balance and the nonnegative edge reserve. The reciprocal charge is
provided by the cleanup's isolated-triangle theorem. -/
theorem rank_four_full_cleanup_deficit_of_edge_balance
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters
      (clearReciprocalFully D).K D.ground)
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
        (chosenCommonRootLabel
          (clearReciprocalFully D).K D.ground fallback hCenters) +
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
    D₂ fallback hGround₂ hCenters Z
      ((∑ E ∈ D₂.K,
        (actualEdgeReciprocalExclusions D₂ E).card) : ℚ)
      hEdge hEdgeSlack hRRat

end JSP523.Rank4
