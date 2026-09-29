import JSP523.Rank4.GraphAssignedNativeMaster
import JSP523.Rank4.PreprocessActualRootInheritance

/-! # Parent-tail inheritance through actual completion cleanup

Native labels remain fixed under deletion. Initial unique centers may
therefore supply parent witnesses even when the survivor has several
common vertices in one root cell.
-/

namespace JSP523.Rank4.AssignedNative

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- The native label depends only on the retained completion label map. -/
theorem data_root_label_eq_of_label_eq
    (D' D : FiniteCompletionCliqueData α) (fallback : α)
    (hLabel : D'.label = D.label) :
    dataRootLabel D' fallback = dataRootLabel D fallback := by
  funext P
  unfold dataRootLabel
  split <;> simp only [hLabel]

omit [Fintype α] in
/-- Parent witnesses selected before deletion remain valid for every
used root of a later label-preserving subfamily. -/
theorem parent_tails_of_initial_unique_centers
    (D' D : FiniteCompletionCliqueData α) (fallback : α)
    (H : Family α) (V : Edge α)
    (hGround : D'.ground = D.ground)
    (hLabel : D'.label = D.label)
    (hFamily : D'.K ⊆ D.K)
    (hCenters : JSP523.Rank4.UniqueCommonRootCenters D.K D.ground)
    (hTails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b
          (JSP523.Rank4.chosenCommonRootLabel D.K D.ground fallback hCenters {a, b})) :
    ∀ a ∈ D'.ground, ∀ b ∈ D'.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D'.K D'.ground →
        HasThreeParentTails H V D'.ground a b (dataRootLabel D' fallback {a, b}) := by
  intro a ha b hb hUsed
  rw [hGround] at ha hb hUsed ⊢
  have hOldUsed := nonempty_common_roots_mono hFamily hUsed
  have hab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
  rw [data_root_label_eq_of_label_eq D' D fallback hLabel,
    data_root_label_pair D fallback a b hab,
    JSP523.Rank4.actual_pair_label_eq_chosen_center D fallback hCenters a b hab hOldUsed]
  exact hTails a ha b hb hOldUsed

/-- The actual three-stage survivor inherits the original parent tails,
without requiring unique common-root centers on the survivor. -/
theorem preprocessed_parent_tails_of_initial_unique_centers
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (H : Family α) (V : Edge α)
    (hCenters : JSP523.Rank4.UniqueCommonRootCenters D.K D.ground)
    (hTails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b
          (JSP523.Rank4.chosenCommonRootLabel D.K D.ground fallback hCenters {a, b})) :
    ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈
        nonemptyCommonRoots (clearUsedParentThenReciprocal D).K D.ground →
        HasThreeParentTails H V D.ground a b
          (dataRootLabel (clearUsedParentThenReciprocal D) fallback {a, b}) := by
  apply parent_tails_of_initial_unique_centers
    (clearUsedParentThenReciprocal D) D fallback H V rfl rfl _ hCenters hTails
  exact (clear_reciprocal_wrong_common_witnesses_sub
    (clearReciprocalDifferentWitnesses (clearUsedParentPairSeparation D))).trans
      ((clear_reciprocal_different_witnesses_sub
        (clearUsedParentPairSeparation D)).trans
          (clear_used_parent_pair_separation_sub D))


/-- The master estimate uses initial weak-cell centers only. Parent
witnesses and completion labels are transported through all later deletions. -/
theorem rank_four_preprocessed_cleaned_master_of_initial_centers
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : JSP523.Rank4.UniqueCommonRootCenters D.K D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (hCenters_vertices : ∀ c ∈ centers, c ∈ V)
    (hCenters_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b
          (JSP523.Rank4.chosenCommonRootLabel D.K D.ground fallback hCenters {a, b}))
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
  have hFinalTails := preprocessed_parent_tails_of_initial_unique_centers
    D fallback H V hCenters h_tails
  exact rank_four_preprocessed_cleaned_master D H B V L centers owner fallback
    parent_overlap h_ground h_h h_ground_vertices
    hCenters_vertices hCenters_outside h_layer_edges h_layer_ground
    h_ground_size hFinalTails h_core_parent h_overlap

/-- The master estimate uses initial weak-cell centers only. Parent
witnesses and completion labels are transported through all later deletions. -/
theorem rank_four_preprocessed_original_bound_of_initial_centers
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap outer_loss cleanup_loss : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (hCenters : JSP523.Rank4.UniqueCommonRootCenters D.K D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (hCenters_vertices : ∀ c ∈ centers, c ∈ V)
    (hCenters_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b
          (JSP523.Rank4.chosenCommonRootLabel D.K D.ground fallback hCenters {a, b}))
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
  have hFinalTails := preprocessed_parent_tails_of_initial_unique_centers
    D fallback H V hCenters h_tails
  exact rank_four_preprocessed_original_bound D H B V L centers owner fallback
    parent_overlap outer_loss cleanup_loss h_ground h_h h_ground_vertices
    hCenters_vertices hCenters_outside h_layer_edges h_layer_ground
    h_ground_size hFinalTails h_core_parent h_overlap h_original h_cleanup

end JSP523.Rank4.AssignedNative
