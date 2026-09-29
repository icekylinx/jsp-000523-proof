import JSP523.Rank4.GraphActualFullPayment
import JSP523.Rank4.PreprocessReciprocalAssembly

/-! # The actual rank-four master estimate after proved preprocessing

The graph payment and used-parent separation are proved for the actual
three-stage survivor. Unique common-root centers and the corresponding
parent-tail hypotheses are still required on that survivor; they are not
asserted to persist under deletion.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Three-stage preprocessing supplies the finite graph deficit without
an assumed graph payment or used-parent separation condition. -/
theorem rank_four_preprocessed_deficit
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : UniqueCommonRootCenters
      (clearUsedParentThenReciprocal D).K D.ground) :
    10 * (clearUsedParentThenReciprocal D).K.card +
      (rankFourNonprivateFacets
        (clearUsedParentThenReciprocal D).K D.ground).card +
      6 * (rankFourAllPrivateEdges
        (clearUsedParentThenReciprocal D).K D.ground).card ≤
    2 * nativeTailVertexTotal
      (clearUsedParentThenReciprocal D).K D.ground
      (nonemptyCommonRoots
        (clearUsedParentThenReciprocal D).K D.ground)
        (chosenCommonRootLabel
          (clearUsedParentThenReciprocal D).K D.ground fallback hCenters) +
      4 * (rankFourFacetShadow
        (clearUsedParentThenReciprocal D).K D.ground).card := by
  let D₁ := clearUsedParentPairSeparation D
  have hGround₁ : ∀ E ∈ D₁.K, E ⊆ D.ground := by
    intro E hE
    exact hGround E (clear_used_parent_pair_separation_sub D hE)
  exact rank_four_full_cleanup_deficit D₁ fallback hGround₁ hCenters
    (clear_used_parent_then_reciprocal_separated D)

/-- The actual master budget with its graph-deficit premise discharged
by the three-stage cleanup theorem. -/
theorem rank_four_preprocessed_cleaned_master
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_centers : UniqueCommonRootCenters (clearUsedParentThenReciprocal D).K D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (h_centers_vertices : ∀ c ∈ centers, c ∈ V)
    (h_centers_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots (clearUsedParentThenReciprocal D).K D.ground →
        HasThreeParentTails H V D.ground a b
          (chosenCommonRootLabel (clearUsedParentThenReciprocal D).K D.ground fallback h_centers
            ({a, b} : Edge α)))
    (h_core_parent : (clearUsedParentThenReciprocal D).K ⊆ B)
    (h_overlap :
      ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
        rankFourFacetShadow B D.ground).card ≤ parent_overlap) :
    10 * ((centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (clearUsedParentThenReciprocal D).K.card) +
      (rankFourNonprivateFacets (clearUsedParentThenReciprocal D).K D.ground).card +
      6 * (rankFourAllPrivateEdges (clearUsedParentThenReciprocal D).K D.ground).card ≤
    10 * D.ground.card.choose 3 +
      2 * (D.ground.card ^ 2 * (Nat.sqrt D.ground.card + 1)) +
      4 * parent_overlap := by
  have hDeficit := rank_four_preprocessed_deficit D fallback h_ground h_centers
  exact rank_four_actual_cleaned_master (clearUsedParentThenReciprocal D)
    H B V L centers owner fallback parent_overlap h_centers
    h_h h_ground_vertices h_centers_vertices h_centers_outside
    h_layer_edges h_layer_ground h_ground_size h_tails h_core_parent
    h_overlap hDeficit

/-- The actual master budget with its graph-deficit premise discharged
by the three-stage cleanup theorem. -/
theorem rank_four_preprocessed_original_bound
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap outer_loss cleanup_loss : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_centers : UniqueCommonRootCenters (clearUsedParentThenReciprocal D).K D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (h_centers_vertices : ∀ c ∈ centers, c ∈ V)
    (h_centers_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots (clearUsedParentThenReciprocal D).K D.ground →
        HasThreeParentTails H V D.ground a b
          (chosenCommonRootLabel (clearUsedParentThenReciprocal D).K D.ground fallback h_centers
            ({a, b} : Edge α)))
    (h_core_parent : (clearUsedParentThenReciprocal D).K ⊆ B)
    (h_overlap :
      ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
        rankFourFacetShadow B D.ground).card ≤ parent_overlap)
    (h_original : H.card ≤
      (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      B.card + outer_loss)
    (h_cleanup : (B \ (clearUsedParentThenReciprocal D).K).card ≤ cleanup_loss) :
    10 * H.card +
      (rankFourNonprivateFacets (clearUsedParentThenReciprocal D).K D.ground).card +
      6 * (rankFourAllPrivateEdges (clearUsedParentThenReciprocal D).K D.ground).card ≤
    10 * D.ground.card.choose 3 +
      2 * (D.ground.card ^ 2 * (Nat.sqrt D.ground.card + 1)) +
      4 * parent_overlap + 10 * (outer_loss + cleanup_loss) := by
  have hDeficit := rank_four_preprocessed_deficit D fallback h_ground h_centers
  exact rank_four_actual_original_bound (clearUsedParentThenReciprocal D)
    H B V L centers owner fallback parent_overlap outer_loss cleanup_loss h_centers
    h_h h_ground_vertices h_centers_vertices h_centers_outside
    h_layer_edges h_layer_ground h_ground_size h_tails h_core_parent
    h_overlap hDeficit h_original h_cleanup

end JSP523.Rank4
