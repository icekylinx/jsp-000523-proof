import JSP523.Rank4.GraphAssignedNativePayment

/-! # The actual master bound without unique survivor centers

The retained completion labels supply native centers after every deletion.
Only the parent-tail condition for these labels remains an explicit input.
-/

namespace JSP523.Rank4.AssignedNative

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem chosen_native_tail_vertex_total_le
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : CenterAssignment K U) :
    nativeTailVertexTotal K U (nonemptyCommonRoots K U)
      (chosenCommonRootLabel K U fallback hCenters) ≤
      (U.card - 3) * (nonemptyCommonRoots K U).card := by
  classical
  apply native_tail_vertex_total_le
  · intro P hP
    exact (Finset.mem_filter.mp hP).1
  · intro P hP
    exact chosen_common_root_label_valid K U fallback hCenters P hP


theorem cleaned_star_chosen_native_sqrt_budget
    {H : Family α} {V U : Edge α}
    (K : Family α) (L : α → Family α) (centers : Finset α)
    (owner : Edge α → α) (fallback : α)
    (hCenters : CenterAssignment K U)
    (hH : Admissible H)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hTails : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        HasThreeParentTails H V U a b
          (chosenCommonRootLabel K U fallback hCenters
            ({a, b} : Edge α))) :
    3 * (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      nativeTailVertexTotal K U (nonemptyCommonRoots K U)
        (chosenCommonRootLabel K U fallback hCenters) ≤
      3 * U.card.choose 3 +
        U.card ^ 2 * (Nat.sqrt U.card + 1) := by
  have hUsed : nonemptyCommonRoots K U ⊆ U.powersetCard 2 := by
    intro P hP
    exact (Finset.mem_filter.mp hP).1
  exact cleaned_star_native_sqrt_budget L centers owner
    (chosenCommonRootLabel K U fallback hCenters)
    (nonemptyCommonRoots K U)
    (nativeTailVertexTotal K U (nonemptyCommonRoots K U)
      (chosenCommonRootLabel K U fallback hCenters))
    hH hUsubV hCentersV hCentersU hLayerEdges hLayerGround
    hUsed hU hTails
    (chosen_native_tail_vertex_total_le K U fallback hCenters)


theorem cleaned_star_chosen_native_master
    {H : Family α} {V U : Edge α}
    (K B : Family α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (nonprivateFacets allPrivateEdges
      parentOverlap : ℕ)
    (hCenters : CenterAssignment K U)
    (hH : Admissible H)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hTails : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        HasThreeParentTails H V U a b
          (chosenCommonRootLabel K U fallback hCenters
            ({a, b} : Edge α)))
    (hKB : K ⊆ B)
    (hOverlap :
      ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
        rankFourFacetShadow B U).card ≤ parentOverlap)
    (hDeficit :
      10 * K.card + nonprivateFacets + 6 * allPrivateEdges ≤
        2 * nativeTailVertexTotal K U (nonemptyCommonRoots K U)
          (chosenCommonRootLabel K U fallback hCenters) +
        4 * (rankFourFacetShadow K U).card) :
    10 * ((centers.biUnion (pairOwnerCleanedLink L owner)).card + K.card) +
        nonprivateFacets + 6 * allPrivateEdges ≤
      10 * U.card.choose 3 +
        2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) +
        4 * parentOverlap := by
  classical
  let A := centers.biUnion (pairOwnerCleanedLink L owner)
  have hA : A ⊆ U.powersetCard 3 := by
    intro T hT
    obtain ⟨c, hc, hTc⟩ := Finset.mem_biUnion.mp hT
    have hTL : T ∈ L c := by
      simp only [pairOwnerCleanedLink, Finset.mem_filter] at hTc
      exact hTc.1
    exact hLayerGround c hc T hTL
  have hStar := cleaned_star_chosen_native_sqrt_budget
    K L centers owner fallback hCenters hH hUsubV
    hCentersV hCentersU hLayerEdges hLayerGround hU hTails
  exact rank_four_master_with_parent_overlap A K B U
    (nativeTailVertexTotal K U (nonemptyCommonRoots K U)
      (chosenCommonRootLabel K U fallback hCenters))
    nonprivateFacets allPrivateEdges
    (U.card ^ 2 * (Nat.sqrt U.card + 1)) parentOverlap
    hKB hA hOverlap hStar hDeficit


theorem rank_four_actual_cleaned_master
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap : ℕ)
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
          (dataRootLabel D fallback
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
          (dataRootLabel D fallback) +
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
    (dataCenterAssignment D fallback) h_h h_ground_vertices hCenters_vertices hCenters_outside
    h_layer_edges h_layer_ground h_ground_size h_tails h_core_parent
    h_overlap h_deficit

/-- The same actual budget carried back to the original family, with
only the finite decomposition and cleanup losses charged. -/
theorem rank_four_actual_original_bound
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap outer_loss cleanup_loss : ℕ)
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
          (dataRootLabel D fallback
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
          (dataRootLabel D fallback) +
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
    owner fallback parent_overlap h_h h_ground_vertices
    hCenters_vertices hCenters_outside h_layer_edges h_layer_ground
    h_ground_size h_tails h_core_parent h_overlap h_deficit
  have h_parent_card := Finset.card_sdiff_add_card_eq_card h_core_parent
  omega


theorem rank_four_preprocessed_deficit
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    10 * (clearUsedParentThenReciprocal D).K.card +
      (rankFourNonprivateFacets
        (clearUsedParentThenReciprocal D).K D.ground).card +
      6 * (rankFourAllPrivateEdges
        (clearUsedParentThenReciprocal D).K D.ground).card ≤
    2 * nativeTailVertexTotal
      (clearUsedParentThenReciprocal D).K D.ground
      (nonemptyCommonRoots
        (clearUsedParentThenReciprocal D).K D.ground)
        (dataRootLabel (clearUsedParentThenReciprocal D) fallback) +
      4 * (rankFourFacetShadow
        (clearUsedParentThenReciprocal D).K D.ground).card := by
  let D₁ := clearUsedParentPairSeparation D
  have hGround₁ : ∀ E ∈ D₁.K, E ⊆ D.ground := by
    intro E hE
    exact hGround E (clear_used_parent_pair_separation_sub D hE)
  exact rank_four_full_cleanup_deficit D₁ fallback hGround₁
    (clear_used_parent_then_reciprocal_separated D)

/-- The actual master budget with its graph-deficit premise discharged
by the three-stage cleanup theorem. -/
theorem rank_four_preprocessed_cleaned_master
    (D : FiniteCompletionCliqueData α)
    (H B : Family α) (V : Edge α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (parent_overlap : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (hCenters_vertices : ∀ c ∈ centers, c ∈ V)
    (hCenters_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots (clearUsedParentThenReciprocal D).K D.ground →
        HasThreeParentTails H V D.ground a b
          (dataRootLabel (clearUsedParentThenReciprocal D) fallback
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
  have hDeficit := rank_four_preprocessed_deficit D fallback h_ground
  exact rank_four_actual_cleaned_master (clearUsedParentThenReciprocal D)
    H B V L centers owner fallback parent_overlap
    h_h h_ground_vertices hCenters_vertices hCenters_outside
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
    (h_h : Admissible H)
    (h_ground_vertices : D.ground ⊆ V)
    (hCenters_vertices : ∀ c ∈ centers, c ∈ V)
    (hCenters_outside : ∀ c ∈ centers, c ∉ D.ground)
    (h_layer_edges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (h_layer_ground : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ D.ground.powersetCard 3)
    (h_ground_size : 3 ≤ D.ground.card)
    (h_tails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots (clearUsedParentThenReciprocal D).K D.ground →
        HasThreeParentTails H V D.ground a b
          (dataRootLabel (clearUsedParentThenReciprocal D) fallback
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
  have hDeficit := rank_four_preprocessed_deficit D fallback h_ground
  exact rank_four_actual_original_bound (clearUsedParentThenReciprocal D)
    H B V L centers owner fallback parent_overlap outer_loss cleanup_loss
    h_h h_ground_vertices hCenters_vertices hCenters_outside
    h_layer_edges h_layer_ground h_ground_size h_tails h_core_parent
    h_overlap hDeficit h_original h_cleanup


end JSP523.Rank4.AssignedNative
