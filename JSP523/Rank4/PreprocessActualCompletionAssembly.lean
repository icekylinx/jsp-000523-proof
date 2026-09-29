import JSP523.Rank4.PreprocessCompletionDegreeCaps

/-! # Actual weak-cell, coloring, and reciprocal preprocessing

This closes the construction-to-payment interface. The coloring deletion
is measured by its actual bad-facet edge set; its asymptotic wedge estimate
is a separate quantitative step.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Label-preserving deletion transports parent tails for the actual
native label, without any unique-center hypothesis. -/
theorem AssignedNative.parent_tails_mono_retained_labels
    (D' D : FiniteCompletionCliqueData α) (fallback : α)
    (H : Family α) (V : Edge α)
    (hGround : D'.ground = D.ground) (hLabel : D'.label = D.label)
    (hFamily : D'.K ⊆ D.K)
    (hTails : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b (dataRootLabel D fallback {a, b})) :
    ∀ a ∈ D'.ground, ∀ b ∈ D'.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D'.K D'.ground →
        HasThreeParentTails H V D'.ground a b (dataRootLabel D' fallback {a, b}) := by
  intro a ha b hb hUsed
  rw [hGround] at ha hb hUsed ⊢
  rw [data_root_label_eq_of_label_eq D' D fallback hLabel]
  exact hTails a ha b hb (nonempty_common_roots_mono hFamily hUsed)

/-- Weak-cell clearing, bad-facet deletion and the three reciprocal
rounds produce the actual finite deficit and actual parent tails. All
losses in this statement are the edge sets that are really deleted. -/
theorem exists_actual_completion_cleanup_with_deficit_and_tails
    {H : Family α} {U V : Edge α} (t d : ℕ) (fallback : α)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H U T).card ≤ d)
    (hLarge : 9 * d < t) :
    ∃ K : Family α, ∃ hCenters : UniqueCommonRootCenters K U,
      ∃ D : FiniteCompletionCliqueData α,
        D.ground = U ∧ D.K ⊆ fixedDecompositionCore H U ∧
        let F := clearUsedParentThenReciprocal D
        (fixedDecompositionCore H U \ F.K).card ≤
          2 * (t - 1) * U.card.choose 2 +
            (bicoloredCompletionDeletionEdges K U
              (fun a b => chosenCommonRootLabel K U fallback hCenters {a, b})).card +
            (D.K \ F.K).card ∧
        (10 * F.K.card + (rankFourNonprivateFacets F.K U).card +
          6 * (rankFourAllPrivateEdges F.K U).card ≤
          2 * nativeTailVertexTotal F.K U (nonemptyCommonRoots F.K U)
            (AssignedNative.dataRootLabel F fallback) +
          4 * (rankFourFacetShadow F.K U).card) ∧
        (∀ a ∈ U, ∀ b ∈ U.erase a,
          ({a, b} : Edge α) ∈ nonemptyCommonRoots F.K U →
            HasThreeParentTails H V U a b (AssignedNative.dataRootLabel F fallback {a, b})) := by
  obtain ⟨K, hCenters, D, hDU, hDK, hKB, hLoss, hTails⟩ :=
    exists_completion_data_after_weak_and_bicolored_cleanup t d fallback
      hH hUniform hUsubV hCap hLarge
  let F := clearUsedParentThenReciprocal D
  have hDB : D.K ⊆ fixedDecompositionCore H U := hDK.trans hKB
  have hFD : F.K ⊆ D.K :=
    (clear_reciprocal_wrong_common_witnesses_sub
      (clearReciprocalDifferentWitnesses (clearUsedParentPairSeparation D))).trans
        ((clear_reciprocal_different_witnesses_sub
          (clearUsedParentPairSeparation D)).trans (clear_used_parent_pair_separation_sub D))
  have hGround : ∀ E ∈ D.K, E ⊆ D.ground := by
    intro E hE
    rw [hDU]
    exact (Finset.mem_filter.mp (hDB hE)).2
  refine ⟨K, hCenters, D, hDU, hDB, ?_, ?_, ?_⟩
  · have h1 := Finset.card_sdiff_add_card_eq_card hDB
    have h2 := Finset.card_sdiff_add_card_eq_card hFD
    have h3 := Finset.card_sdiff_add_card_eq_card (hFD.trans hDB)
    dsimp only [F] at h2 h3
    omega
  · have hDeficit := AssignedNative.rank_four_preprocessed_deficit D fallback hGround
    simpa only [hDU] using hDeficit
  · have hTailsD : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
        ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
          HasThreeParentTails H V D.ground a b (AssignedNative.dataRootLabel D fallback {a, b}) := by
      simpa only [hDU] using hTails
    have hFinal := AssignedNative.parent_tails_mono_retained_labels
      F D fallback H V rfl rfl hFD hTailsD
    change ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots F.K D.ground →
        HasThreeParentTails H V D.ground a b (AssignedNative.dataRootLabel F fallback {a, b}) at hFinal
    simpa only [hDU] using hFinal



/-- The weak-cell existence theorem now feeds the actual original-family
master bound. Its coloring and reciprocal losses are concrete deletion
sets; no completion-data, center, tail, or graph-payment premise is supplied. -/
theorem exists_actual_original_master_after_cleanup
    {H : Family α} {U V : Edge α} (t d : ℕ) (fallback : α)
    (L : α → Family α) (centers : Finset α) (owner : Edge α → α)
    (overlap outerLoss : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H U T).card ≤ d)
    (hLarge : 9 * d < t)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c, Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hOverlap : ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card ≤ overlap)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss) :
    ∃ K : Family α, ∃ hCenters : UniqueCommonRootCenters K U,
      ∃ D : FiniteCompletionCliqueData α,
        D.ground = U ∧ D.K ⊆ fixedDecompositionCore H U ∧
        let F := clearUsedParentThenReciprocal D
        10 * H.card + (rankFourNonprivateFacets F.K U).card +
          6 * (rankFourAllPrivateEdges F.K U).card ≤
          10 * U.card.choose 3 + 2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) +
          4 * overlap + 10 * (outerLoss +
            (2 * (t - 1) * U.card.choose 2 +
              (bicoloredCompletionDeletionEdges K U
                (fun a b => chosenCommonRootLabel K U fallback hCenters {a, b})).card +
              (D.K \ F.K).card)) := by
  obtain ⟨K, hCenters, D, hDU, hDB, hLoss, hDeficit, hTails⟩ :=
    exists_actual_completion_cleanup_with_deficit_and_tails t d fallback
      hH hUniform hUsubV hCap hLarge
  let F := clearUsedParentThenReciprocal D
  have hFU : F.ground = U := hDU
  have hFD : F.K ⊆ D.K :=
    (clear_reciprocal_wrong_common_witnesses_sub
      (clearReciprocalDifferentWitnesses (clearUsedParentPairSeparation D))).trans
        ((clear_reciprocal_different_witnesses_sub
          (clearUsedParentPairSeparation D)).trans (clear_used_parent_pair_separation_sub D))
  refine ⟨K, hCenters, D, hDU, hDB, ?_⟩
  have hMaster := AssignedNative.rank_four_actual_original_bound F H
    (fixedDecompositionCore H U) V L centers owner fallback overlap outerLoss
    (2 * (t - 1) * U.card.choose 2 +
      (bicoloredCompletionDeletionEdges K U
        (fun a b => chosenCommonRootLabel K U fallback hCenters {a, b})).card +
      (D.K \ F.K).card) hH
    (by simpa only [hFU] using hUsubV) hCentersV
    (by simpa only [hFU] using hCentersU) hLayerEdges
    (by simpa only [hFU] using hLayerGround)
    (by simpa only [hFU] using hU)
    (by simpa only [hFU] using hTails) (hFD.trans hDB)
    (by simpa only [hFU] using hOverlap)
    (by simpa only [hFU] using hDeficit) hOriginal hLoss
  simpa only [hFU] using hMaster



/-- The actual master bound with the bicolored deletion fully replaced
by its repeated-color wedge estimate and the center-graph cap derived
from the original pair degrees and weak-cell threshold. -/
theorem exists_actual_original_master_of_degree_caps
    {H : Family α} {U V : Edge α} (t d M κ : ℕ) (fallback : α)
    (L : α → Family α) (centers : Finset α) (owner : Edge α → α)
    (overlap outerLoss : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H U T).card ≤ d)
    (hLarge : 9 * d < t)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree (fixedDecompositionCore H U) P ≤ M)
    (hScale : (d - 1) * M ≤ t * κ)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c, Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hOverlap : ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card ≤ overlap)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss) :
    ∃ D : FiniteCompletionCliqueData α,
      D.ground = U ∧ D.K ⊆ fixedDecompositionCore H U ∧
      (∀ a b, (reciprocalUsedLabelFiber D a b).card ≤ κ) ∧
      let F := clearUsedParentThenReciprocal D
      10 * H.card + (rankFourNonprivateFacets F.K U).card +
        6 * (rankFourAllPrivateEdges F.K U).card ≤
        10 * U.card.choose 3 + 2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) +
        4 * overlap + 10 * (outerLoss +
          (2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 +
            (D.K \ F.K).card)) := by
  obtain ⟨D, hDU, hDB, hInitialLoss, hFiber, hTails⟩ :=
    exists_completion_data_after_weak_bicolored_cleanup_of_degree_caps t d M κ fallback
      hH hUniform hUsubV hCap hLarge hPair hScale
  let F := clearUsedParentThenReciprocal D
  have hFU : F.ground = U := hDU
  have hFD : F.K ⊆ D.K :=
    (clear_reciprocal_wrong_common_witnesses_sub
      (clearReciprocalDifferentWitnesses (clearUsedParentPairSeparation D))).trans
        ((clear_reciprocal_different_witnesses_sub
          (clearUsedParentPairSeparation D)).trans (clear_used_parent_pair_separation_sub D))
  have hGround : ∀ E ∈ D.K, E ⊆ D.ground := by
    intro E hE
    rw [hDU]
    exact (Finset.mem_filter.mp (hDB hE)).2
  have hDeficit := AssignedNative.rank_four_preprocessed_deficit D fallback hGround
  have hTailsD : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b (AssignedNative.dataRootLabel D fallback {a, b}) := by
    simpa only [hDU] using hTails
  have hFinalTails := AssignedNative.parent_tails_mono_retained_labels
    F D fallback H V rfl rfl hFD hTailsD
  have hLoss : (fixedDecompositionCore H U \ F.K).card ≤
      2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 +
        (D.K \ F.K).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hDB
    have h2 := Finset.card_sdiff_add_card_eq_card hFD
    have h3 := Finset.card_sdiff_add_card_eq_card (hFD.trans hDB)
    omega
  refine ⟨D, hDU, hDB, hFiber, ?_⟩
  have hMaster := AssignedNative.rank_four_actual_original_bound F H
    (fixedDecompositionCore H U) V L centers owner fallback overlap outerLoss
    (2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 +
      (D.K \ F.K).card) hH
    (by simpa only [hFU] using hUsubV) hCentersV
    (by simpa only [hFU] using hCentersU) hLayerEdges
    (by simpa only [hFU] using hLayerGround)
    (by simpa only [hFU] using hU) hFinalTails (hFD.trans hDB)
    (by simpa only [hFU] using hOverlap) hDeficit hOriginal hLoss
  simpa only [hFU] using hMaster

end JSP523.Rank4
