import JSP523.Rank4.GlobalStabilityFinite
import JSP523.Rank4.GraphCompletionData

set_option maxHeartbeats 1000000

/-!
# The actual finite rank-four master estimate

The graph deficit is kept as one precise premise on the actual cleaned
completion data. All facet counts, the shadow, and the native vertex count
below are computed from that data, rather than supplied as unrelated numbers.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The master budget with its combinatorial quantities instantiated on
the actual cleaned four-family. -/
theorem rank_four_actual_cleaned_master
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap : ℕ)
    (h_centers : UniqueCommonRootCenters D.K D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (h_centers_vertices : ∀ c ∈ centers, c ∈ V)
    (h_centers_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b
          (chosenCommonRootLabel D.K D.ground fallback h_centers
            ({a, b} : Edge α)))
    (h_core_parent : D.K ⊆ B)
    (h_overlap :
      ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
        rankFourFacetShadow B D.ground).card ≤ parent_overlap)
    (h_deficit :
      10 * D.K.card +
        (rankFourNonprivateFacets D.K D.ground).card +
        6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
      2 * nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
          (chosenCommonRootLabel D.K D.ground fallback h_centers) +
      4 * (rankFourFacetShadow D.K D.ground).card) :
    10 * ((centers.biUnion (pairOwnerCleanedLink L owner)).card +
      D.K.card) +
      (rankFourNonprivateFacets D.K D.ground).card +
      6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
    10 * D.ground.card.choose 3 +
      2 * (D.ground.card ^ 2 * (Nat.sqrt D.ground.card + 1)) +
      4 * parent_overlap := by
  exact cleaned_star_chosen_native_master D.K B L centers owner fallback
    (rankFourNonprivateFacets D.K D.ground).card
    (rankFourAllPrivateEdges D.K D.ground).card parent_overlap
    h_centers h_h h_ground_vertices h_centers_vertices h_centers_outside
    h_layer_edges h_layer_ground h_ground_size h_tails h_core_parent
    h_overlap h_deficit

/-- The same actual budget carried back to the original family, with
only the finite decomposition and cleanup losses charged. -/
theorem rank_four_actual_original_bound
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap outer_loss cleanup_loss : ℕ)
    (h_centers : UniqueCommonRootCenters D.K D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (h_centers_vertices : ∀ c ∈ centers, c ∈ V)
    (h_centers_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b
          (chosenCommonRootLabel D.K D.ground fallback h_centers
            ({a, b} : Edge α)))
    (h_core_parent : D.K ⊆ B)
    (h_overlap :
      ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
        rankFourFacetShadow B D.ground).card ≤ parent_overlap)
    (h_deficit :
      10 * D.K.card +
        (rankFourNonprivateFacets D.K D.ground).card +
        6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
      2 * nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
          (chosenCommonRootLabel D.K D.ground fallback h_centers) +
      4 * (rankFourFacetShadow D.K D.ground).card)
    (h_original : H.card ≤
      (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      B.card + outer_loss)
    (h_cleanup : (B \ D.K).card ≤ cleanup_loss) :
    10 * H.card +
      (rankFourNonprivateFacets D.K D.ground).card +
      6 * (rankFourAllPrivateEdges D.K D.ground).card ≤
    10 * D.ground.card.choose 3 +
      2 * (D.ground.card ^ 2 * (Nat.sqrt D.ground.card + 1)) +
      4 * parent_overlap + 10 * (outer_loss + cleanup_loss) := by
  have h_master := rank_four_actual_cleaned_master D H B V L centers
    owner fallback parent_overlap h_centers h_h h_ground_vertices
    h_centers_vertices h_centers_outside h_layer_edges h_layer_ground
    h_ground_size h_tails h_core_parent h_overlap h_deficit
  have h_parent_card := Finset.card_sdiff_add_card_eq_card h_core_parent
  omega

end JSP523.Rank4
