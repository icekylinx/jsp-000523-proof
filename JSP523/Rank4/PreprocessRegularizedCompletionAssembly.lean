import JSP523.Rank4.PreprocessActualCompletionAssembly
import JSP523.Rank4.PreprocessActualDegreeTailChoice

/-! # Feeding actual regularization into the original-family master -/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem HasThreeParentTails.mono_family
    {H K : Family α} {V U : Edge α} {a b z : α}
    (hKH : K ⊆ H) (hTails : HasThreeParentTails K V U a b z) :
    HasThreeParentTails H V U a b z := by
  obtain ⟨R, S, T, hz, hRS, hRT, hST, hRU, hSU, hTU, hR, hS, hT⟩ := hTails
  exact ⟨R, S, T, hz, hRS, hRT, hST, hRU, hSU, hTU,
    common_triple_cell_mono_family_ground hKH (Finset.Subset.refl V) hR,
    common_triple_cell_mono_family_ground hKH (Finset.Subset.refl V) hS,
    common_triple_cell_mono_family_ground hKH (Finset.Subset.refl V) hT⟩

/-- The completion data is constructed from the regularized subfamily B₁,
while stars and parent tails remain actual edges of the original H.
The original induced core pays its actual regularization loss once. -/
theorem exists_actual_original_master_after_regularization
    {H B₁ : Family α} {U V : Edge α} (t d M κ : ℕ) (fallback : α)
    (L : α → Family α) (centers : Finset α) (owner : Edge α → α)
    (overlap outerLoss : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hB₁ : B₁ ⊆ fixedDecompositionCore H U)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions B₁ U T).card ≤ d)
    (hLarge : 9 * d < t)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree B₁ P ≤ M)
    (hScale : (d - 1) * M ≤ t * κ)
    (hCentersV : ∀ c ∈ centers, c ∈ V) (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c, Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hOverlap : ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card ≤ overlap)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss) :
    ∃ D : FiniteCompletionCliqueData α,
      D.ground = U ∧ D.K ⊆ B₁ ∧
      (∀ a b, (reciprocalUsedLabelFiber D a b).card ≤ κ) ∧
      (∀ T : Edge α, T.card = 3 → (D.K.filter fun E => T ⊆ E).card ≤ d) ∧
      let F := clearUsedParentThenReciprocal D
      (fixedDecompositionCore H U \ F.K).card ≤
        (fixedDecompositionCore H U \ B₁).card +
          (2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 + (D.K \ F.K).card) ∧
      10 * H.card + (rankFourNonprivateFacets F.K U).card +
        6 * (rankFourAllPrivateEdges F.K U).card ≤
        10 * U.card.choose 3 + 2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) +
          4 * overlap + 10 * (outerLoss + ((fixedDecompositionCore H U \ B₁).card +
            (2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 +
              (D.K \ F.K).card))) := by
  have hB₁H : B₁ ⊆ H := fun E hE => (Finset.mem_filter.mp (hB₁ hE)).1
  have hGround₁ : ∀ E ∈ B₁, E ⊆ U := fun E hE => (Finset.mem_filter.mp (hB₁ hE)).2
  have hUniform₁ : Uniform 4 B₁ := fun _ hE => hUniform (hB₁H hE)
  have hCore₁ : fixedDecompositionCore B₁ U = B₁ := by
    apply Finset.filter_true_of_mem
    exact hGround₁
  obtain ⟨D, hDU, hDB, hInitialLoss, hFiber, hTails⟩ :=
    exists_completion_data_after_weak_bicolored_cleanup_of_degree_caps t d M κ fallback
      (admissible_mono hB₁H hH) hUniform₁ hUsubV hCap hLarge
      (by simpa only [hCore₁] using hPair) hScale
  rw [hCore₁] at hDB hInitialLoss
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
    exact hGround₁ E (hDB hE)
  have hDeficit := AssignedNative.rank_four_preprocessed_deficit D fallback hGround
  have hTailsH : ∀ a ∈ D.ground, ∀ b ∈ D.ground.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground →
        HasThreeParentTails H V D.ground a b (AssignedNative.dataRootLabel D fallback {a, b}) := by
    rw [hDU]
    intro a ha b hb hUsed
    exact (hTails a ha b hb hUsed).mono_family hB₁H
  have hFinalTails := AssignedNative.parent_tails_mono_retained_labels F D fallback H V rfl rfl hFD hTailsH
  have hLoss : (fixedDecompositionCore H U \ F.K).card ≤
      (fixedDecompositionCore H U \ B₁).card +
        (2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 + (D.K \ F.K).card) := by
    have h1 := Finset.card_sdiff_add_card_eq_card hB₁
    have h2 := Finset.card_sdiff_add_card_eq_card hDB
    have h3 := Finset.card_sdiff_add_card_eq_card hFD
    have h4 := Finset.card_sdiff_add_card_eq_card ((hFD.trans hDB).trans hB₁)
    omega
  refine ⟨D, hDU, hDB, hFiber, ?_, hLoss, ?_⟩
  · intro T hT
    have hParents : (B₁.filter fun E => T ⊆ E).card ≤ d := by
      change (rankFourFacetParents B₁ T).card ≤ d
      rw [← facet_completions_card_eq_parent_edges B₁ U T hUniform₁ hGround₁ hT]
      exact hCap T hT
    apply (Finset.card_le_card ?_).trans hParents
    intro E hE
    exact Finset.mem_filter.mpr ⟨hDB (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩
  · have hMaster := AssignedNative.rank_four_actual_original_bound F H
      (fixedDecompositionCore H U) V L centers owner fallback overlap outerLoss
      ((fixedDecompositionCore H U \ B₁).card +
        (2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 + (D.K \ F.K).card)) hH
      (by simpa only [hFU] using hUsubV) hCentersV
      (by simpa only [hFU] using hCentersU) hLayerEdges
      (by simpa only [hFU] using hLayerGround) (by simpa only [hFU] using hU)
      hFinalTails ((hFD.trans hDB).trans hB₁)
      (by simpa only [hFU] using hOverlap) hDeficit hOriginal hLoss
    simpa only [hFU] using hMaster

end JSP523.Rank4
