import JSP523.Rank4.PreprocessInitialOuterCoverScale

/-! # Connecting the actual initial outer cover to touching loss -/

namespace JSP523.Rank4

/-- The vertex cap obtained after removing the actual high-degree set
supplies the radius premise of the existing touching-cover allocation. -/
theorem initial_outer_cover_touching_loss
    {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n))
    (D : ℝ) (M radius : ℕ) [Nonempty {c // c ∈ X}]
    (hUniform : Uniform 4 H)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree H P ≤ M)
    (hVertex : ∀ z : Fin n,
      (((fixedDecompositionCore H (Finset.univ \ Z)).filter fun E => z ∈ E).card : ℝ) ≤ D)
    (hRadius : 6 * D ≤ (radius : ℝ) ^ 3) :
    let W : Edge (Fin n) := Finset.univ \ Z
    let H₀ := fixedDecompositionCore H W
    let U := W \ X
    let L := fun i : {c // c ∈ X} => rankFourStarLink H₀ U i.val
    let owner := maximumDegreePairOwner L
    3 * (H₀ \ fixedDecompositionCore H₀ U).card ≤
      3 * (X.card.choose 2 * M) +
        3 * (∑ i : {c // c ∈ X}, (L i \ pairOwnerCleanedLink L owner i).card) +
        (radius + 3) * U.card.choose 2 := by
  classical
  let W : Edge (Fin n) := Finset.univ \ Z
  let H₀ := fixedDecompositionCore H W
  have hH₀H : H₀ ⊆ H := Finset.filter_subset _ _
  have hUniform₀ : Uniform 4 H₀ := fun E hE => hUniform (hH₀H hE)
  have hGround₀ : ∀ E ∈ H₀, E ⊆ W := fun E hE => (Finset.mem_filter.mp hE).2
  have hPair₀ : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree H₀ P ≤ M := by
    intro P hP
    apply le_trans _ (hPair P hP)
    exact Finset.card_le_card (Finset.filter_subset_filter (fun E => P ⊆ E) hH₀H)
  have hSize : ∀ c ∈ X, 6 * (H₀.filter fun E => c ∈ E).card ≤ radius ^ 3 := by
    intro c _
    have hReal : (6 : ℝ) * (H₀.filter fun E => c ∈ E).card ≤ (radius : ℝ) ^ 3 := by
      have h := hVertex c
      change ((H₀.filter fun E => c ∈ E).card : ℝ) ≤ D at h
      linarith only [h, hRadius]
    exact_mod_cast hReal
  exact actual_touching_cover_loss H₀ W X M radius hUniform₀ hGround₀ hPair₀ hSize

/-- Ordinary three-set codegrees from the initial cover are the actual
completion-degree caps needed by the preprocessing modules. -/
theorem initial_outer_core_completion_cap
    {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n)) (t : ℕ)
    (hUniform : Uniform 4 H)
    (hParents : ∀ T : Edge (Fin n), T.card = 3 →
      (rankFourFacetParents (fixedDecompositionCore H (Finset.univ \ (Z ∪ X))) T).card < t) :
    ∀ T : Edge (Fin n), T.card = 3 →
      (facetCompletions (fixedDecompositionCore H (Finset.univ \ (Z ∪ X)))
        (Finset.univ \ (Z ∪ X)) T).card < t := by
  intro T hT
  rw [facet_completions_card_eq_parent_edges
    (fixedDecompositionCore H (Finset.univ \ (Z ∪ X)))
    (Finset.univ \ (Z ∪ X)) T
    (fun E hE => hUniform (Finset.mem_filter.mp hE).1)
    (fun E hE => (Finset.mem_filter.mp hE).2) hT]
  exact hParents T hT

end JSP523.Rank4
