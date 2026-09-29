import JSP523.Rank4.GraphAssignedNativeInheritance

/-! # Constructing completion data by deleting bicolored triple facets

The original chosen common-root labels are fixed before deletion. Removing
all edges through a triple facet with a bicolored completion triangle
provides exactly the clique condition required by the graph payment.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bad triple facets, measured using the original family and labels. -/
noncomputable def bicoloredCompletionFacets
    (K : Family α) (U : Edge α) (label : α → α → α) : Family α := by
  classical
  exact (U.powersetCard 3).filter fun T =>
    ∃ x ∈ graphFacetCompletions K U T,
      ∃ y ∈ graphFacetCompletions K U T,
        ∃ z ∈ graphFacetCompletions K U T,
          x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
            bicoloredTriangle (label x y) (label x z) (label y z)

/-- Every original edge through a bad triple facet is deleted. -/
noncomputable def bicoloredCompletionDeletionEdges
    (K : Family α) (U : Edge α) (label : α → α → α) : Family α := by
  classical
  exact K.filter fun E => ∃ T ∈ bicoloredCompletionFacets K U label, T ⊆ E

/-- Fixed symmetric common-root labels become completion clique data
after the actual bad-facet deletion. -/
noncomputable def clearBicoloredCompletionData
    (K : Family α) (U : Edge α) (label : α → α → α)
    (hUniform : Uniform 4 K) (hAdmissible : Admissible K)
    (hGround : ∀ E ∈ K, E ⊆ U)
    (hSymm : ∀ x y, label x y = label y x)
    (hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T) :
    FiniteCompletionCliqueData α := by
  classical
  let K' := K \ bicoloredCompletionDeletionEdges K U label
  have hSub : K' ⊆ K := Finset.sdiff_subset
  refine ⟨U, K', (fun _ hE => hUniform (hSub hE)),
    admissible_mono hSub hAdmissible, label, hSymm, ?_, ?_⟩
  · intro x y hxy T hT
    exact hCenter x y hxy T
      (common_triple_cell_mono_family_ground hSub (Finset.Subset.refl U) hT)
  · intro T hTcard x hx y hy z hz hxy hxz hyz hBicolor
    have hComp (a : α) (ha : a ∈ graphFacetCompletions K' U T) :
        a ∈ graphFacetCompletions K U T :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,
        hSub (Finset.mem_filter.mp ha).2⟩
    have hxEdge := Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).2
    have hTU : T ⊆ U := (Finset.subset_insert x T).trans (hGround _ hxEdge.1)
    have hBad : T ∈ bicoloredCompletionFacets K U label := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powersetCard.mpr ⟨hTU, hTcard⟩,
        x, hComp x hx, y, hComp y hy, z, hComp z hz,
        hxy, hxz, hyz, hBicolor⟩
    exact hxEdge.2 (Finset.mem_filter.mpr
      ⟨hxEdge.1, T, hBad, Finset.subset_insert x T⟩)

omit [Fintype α] in
/-- The original unique-center choice is a symmetric ordered-pair label. -/
theorem chosen_pair_label_symm
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U) (a b : α) :
    chosenCommonRootLabel K U fallback hCenters {a, b} =
      chosenCommonRootLabel K U fallback hCenters {b, a} := by
  rw [Finset.pair_comm]

omit [Fintype α] in
/-- The original chosen pair label centers each of its actual common triples. -/
theorem chosen_pair_label_centers_common_triples
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (hGround : ∀ E ∈ K, E ⊆ U)
    (a b : α) (hab : a ≠ b)
    (T : Edge α) (hT : T ∈ commonTripleCell K U a b) :
    chosenCommonRootLabel K U fallback hCenters {a, b} ∈ T := by
  classical
  have hc : ({a, b} : Edge α).card = 2 := Finset.card_pair hab
  have hSpec := (pair_root_rep_spec ({a, b} : Edge α) hc).2
  have hRoot : commonRootCell K U {a, b} = commonTripleCell K U a b := by
    simp only [commonRootCell, dite_eq_left hc]
    exact common_triple_cell_eq_of_pair_eq K U hSpec.symm
  have hParts := mem_common_triple_cell.mp hT
  have haU := hGround _ hParts.2.2.2.1 (Finset.mem_insert_self a T)
  have hbU := hGround _ hParts.2.2.2.2 (Finset.mem_insert_self b T)
  have hUsed : ({a, b} : Edge α) ∈ nonemptyCommonRoots K U := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, hc⟩, ?_⟩
    · intro x hx
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx : x = a ∨ x = b) with rfl | rfl
      · exact haU
      · exact hbU
    · rw [hRoot]
      exact Finset.card_pos.mpr ⟨T, hT⟩
  exact chosen_common_root_label_center K U fallback hCenters {a, b} hUsed T (hRoot ▸ hT)

/-- Completion clique data from the initial weak-cell centers, with no
extra coloring premise. -/
noncomputable def completionDataFromInitialCenters
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (hUniform : Uniform 4 K) (hAdmissible : Admissible K)
    (hGround : ∀ E ∈ K, E ⊆ U) : FiniteCompletionCliqueData α :=
  clearBicoloredCompletionData K U
    (fun a b => chosenCommonRootLabel K U fallback hCenters {a, b})
    hUniform hAdmissible hGround
    (chosen_pair_label_symm K U fallback hCenters)
    (chosen_pair_label_centers_common_triples K U fallback hCenters hGround)



omit [Fintype α] in
/-- Each bad triple facet costs at most its actual number of parents. -/
theorem bicolored_completion_deletion_card_le
    (K : Family α) (U : Edge α) (label : α → α → α) (d : ℕ)
    (hUniform : Uniform 4 K) (hGround : ∀ E ∈ K, E ⊆ U)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions K U T).card ≤ d) :
    (bicoloredCompletionDeletionEdges K U label).card ≤
      d * (bicoloredCompletionFacets K U label).card := by
  classical
  have hCover : bicoloredCompletionDeletionEdges K U label ⊆
      (bicoloredCompletionFacets K U label).biUnion (rankFourFacetParents K) := by
    intro E hE
    obtain ⟨hEK, T, hT, hTE⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_biUnion.mpr ⟨T, hT, Finset.mem_filter.mpr ⟨hEK, hTE⟩⟩
  calc
    _ ≤ ((bicoloredCompletionFacets K U label).biUnion (rankFourFacetParents K)).card :=
      Finset.card_le_card hCover
    _ ≤ ∑ T ∈ bicoloredCompletionFacets K U label, (rankFourFacetParents K T).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ bicoloredCompletionFacets K U label, d := by
      apply Finset.sum_le_sum
      intro T hT
      have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
      rw [← facet_completions_card_eq_parent_edges K U T hUniform hGround hc]
      exact hCap T hc
    _ = _ := by simp [Nat.mul_comm]

omit [Fintype α] in
/-- The actual weak-cell existence theorem now supplies genuine
completion clique data after the necessary bad-facet deletion. Parent
witnesses remain those chosen before that deletion. -/
theorem exists_completion_data_after_weak_and_bicolored_cleanup
    {H : Family α} {U V : Edge α} (t d : ℕ) (fallback : α)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H U T).card ≤ d)
    (hLarge : 9 * d < t) :
    ∃ K : Family α, ∃ hCenters : UniqueCommonRootCenters K U,
      ∃ D : FiniteCompletionCliqueData α,
        D.ground = U ∧ D.K ⊆ K ∧ K ⊆ fixedDecompositionCore H U ∧
        (fixedDecompositionCore H U \ D.K).card ≤
          2 * (t - 1) * U.card.choose 2 +
            (bicoloredCompletionDeletionEdges K U
              (fun a b => chosenCommonRootLabel K U fallback hCenters {a, b})).card ∧
        (∀ a ∈ U, ∀ b ∈ U.erase a,
          ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K U →
            HasThreeParentTails H V U a b (AssignedNative.dataRootLabel D fallback {a, b})) := by
  classical
  obtain ⟨K, hCenters, hKB, hLoss, hTails, _hInheritance⟩ :=
    clear_small_cells_with_actual_parent_label_inheritance t d fallback hH hUsubV hCap hLarge
  have hKH : K ⊆ H := fun E hE => (Finset.mem_filter.mp (hKB hE)).1
  have hGround : ∀ E ∈ K, E ⊆ U := fun E hE => (Finset.mem_filter.mp (hKB hE)).2
  have hUniformK : Uniform 4 K := fun E hE => hUniform (hKH hE)
  let D := completionDataFromInitialCenters K U fallback hCenters
    hUniformK (admissible_mono hKH hH) hGround
  let bad := bicoloredCompletionDeletionEdges K U
    (fun a b => chosenCommonRootLabel K U fallback hCenters {a, b})
  have hDK : D.K = K \ bad := rfl
  have hDsub : D.K ⊆ K := by rw [hDK]; exact Finset.sdiff_subset
  refine ⟨K, hCenters, D, rfl, hDsub, hKB, ?_, ?_⟩
  · have hExtra : (K \ D.K).card ≤ bad.card := by
      apply Finset.card_le_card
      intro E hE
      obtain ⟨hEK, hNot⟩ := Finset.mem_sdiff.mp hE
      by_contra hBad
      exact hNot (hDK ▸ Finset.mem_sdiff.mpr ⟨hEK, hBad⟩)
    dsimp only [bad] at hExtra
    have h1 := Finset.card_sdiff_add_card_eq_card hKB
    have h2 := Finset.card_sdiff_add_card_eq_card hDsub
    have h3 := Finset.card_sdiff_add_card_eq_card (hDsub.trans hKB)
    omega
  · intro a ha b hb hUsed
    have hUsedK := nonempty_common_roots_mono hDsub hUsed
    rw [AssignedNative.data_root_label_pair D fallback a b (Finset.mem_erase.mp hb).1.symm]
    exact hTails a ha b hb hUsedK

end JSP523.Rank4
