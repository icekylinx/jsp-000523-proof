import JSP523.Rank4.PreprocessWeakCellThresholdData

/-! # Actual completion data with the quantitative coloring budget -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Weak-cell clearing and repeated-color wedge deletion construct the
completion data and its used-center degree cap with explicit finite loss. -/
theorem exists_completion_data_after_weak_bicolored_cleanup_of_degree_caps
    {H : Family α} {U V : Edge α} (t d M κ : ℕ) (fallback : α)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions H U T).card ≤ d)
    (hLarge : 9 * d < t)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree (fixedDecompositionCore H U) P ≤ M)
    (hScale : (d - 1) * M ≤ t * κ) :
    ∃ D : FiniteCompletionCliqueData α,
      D.ground = U ∧ D.K ⊆ fixedDecompositionCore H U ∧
      (fixedDecompositionCore H U \ D.K).card ≤
        2 * (t - 1) * U.card.choose 2 + d ^ 2 * U.card ^ 2 * κ ^ 2 ∧
      (∀ a b, (reciprocalUsedLabelFiber D a b).card ≤ κ) ∧
      (∀ a ∈ U, ∀ b ∈ U.erase a,
        ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K U →
          HasThreeParentTails H V U a b (AssignedNative.dataRootLabel D fallback {a, b})) := by
  classical
  obtain ⟨K, hCenters, hRoots, hKB, hLoss, hTails⟩ :=
    clear_small_cells_and_get_chosen_parent_tails_with_threshold t d fallback hH hUsubV hCap hLarge
  have hKH : K ⊆ H := fun E hE => (Finset.mem_filter.mp (hKB hE)).1
  have hGround : ∀ E ∈ K, E ⊆ U := fun E hE => (Finset.mem_filter.mp (hKB hE)).2
  have hUniformK : Uniform 4 K := fun E hE => hUniform (hKH hE)
  let label := fun a b => chosenCommonRootLabel K U fallback hCenters {a, b}
  have hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T :=
    chosen_pair_label_centers_common_triples K U fallback hCenters hGround
  have hCapK : ∀ T : Edge α, T.card = 3 → (facetCompletions K U T).card ≤ d := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hKH (Finset.mem_filter.mp hx).2⟩
  have hPairK : ∀ P : Edge α, P.card = 2 → rankFourPairDegree K P ≤ M := by
    intro P hP
    apply (Finset.card_le_card ?_).trans (hPair P hP)
    intro E hE
    exact Finset.mem_filter.mpr ⟨hKB (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩
  have hFiber := raw_used_label_fiber_card_le_of_cleared_roots K U label t d M κ
    hUniformK hGround hCenter (by omega) hRoots hCapK hPairK hScale
  have hBad := bicolored_completion_deletion_card_le_wedge_budget K U label d κ
    hUniformK hGround (chosen_pair_label_symm K U fallback hCenters) hCenter hCapK hFiber
  let D := completionDataFromInitialCenters K U fallback hCenters
    hUniformK (admissible_mono hKH hH) hGround
  let bad := bicoloredCompletionDeletionEdges K U label
  have hDK : D.K = K \ bad := rfl
  have hDsub : D.K ⊆ K := by rw [hDK]; exact Finset.sdiff_subset
  refine ⟨D, rfl, hDsub.trans hKB, ?_, ?_, ?_⟩
  · have hExtra : (K \ D.K).card ≤ bad.card := by
      apply Finset.card_le_card
      intro E hE
      obtain ⟨hEK, hNot⟩ := Finset.mem_sdiff.mp hE
      by_contra hBad
      exact hNot (hDK ▸ Finset.mem_sdiff.mpr ⟨hEK, hBad⟩)
    change bad.card ≤ _ at hBad
    have h1 := Finset.card_sdiff_add_card_eq_card hKB
    have h2 := Finset.card_sdiff_add_card_eq_card hDsub
    have h3 := Finset.card_sdiff_add_card_eq_card (hDsub.trans hKB)
    omega
  · intro a b
    apply (Finset.card_le_card ?_).trans (hFiber a b)
    intro r hr
    have hParts := Finset.mem_filter.mp hr
    obtain ⟨T, hT⟩ := hParts.2
    exact Finset.mem_filter.mpr ⟨hParts.1, T,
      common_triple_cell_mono_family_ground hDsub (Finset.Subset.refl U) hT⟩
  · intro a ha b hb hUsed
    have hUsedK := nonempty_common_roots_mono hDsub hUsed
    rw [AssignedNative.data_root_label_pair D fallback a b (Finset.mem_erase.mp hb).1.symm]
    exact hTails a ha b hb hUsedK

end JSP523.Rank4
