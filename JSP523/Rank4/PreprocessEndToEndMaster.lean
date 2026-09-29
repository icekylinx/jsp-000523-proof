import JSP523.Rank4.PreprocessRegularizedCompletionAssembly
import JSP523.Rank4.GlobalActualParameterChoice

/-! # Actual regularization through the finite rank-four master -/

namespace JSP523.Rank4

/-- Starting from the initial degree range of the original induced core,
construct both the regularized family and the fully classified completion
data.  No completion-data, deficit, or native-center premise is supplied. -/
theorem exists_actual_master_from_initial_degree_range
    {n : ℕ} (H : Family (Fin n)) (U V : Edge (Fin n))
    (q level : ℕ) (a : ℝ) (fallback : Fin n)
    (L : Fin n → Family (Fin n)) (centers : Finset (Fin n)) (owner : Edge (Fin n) → Fin n)
    (overlap outerLoss : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H) (hUsubV : U ⊆ V)
    (hLevel : 256 ≤ level) (hRange : q ^ 11 ≤ n) (ha : 0 < a)
    (hVertex : ∀ v, ((fixedDecompositionCore H U).filter fun E => v ∈ E).card ≤ q ^ 8 * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree (fixedDecompositionCore H U) P ≤ q ^ 8 * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 →
      (facetCompletions (fixedDecompositionCore H U) Finset.univ Q).card ≤ q ^ 8)
    (hLarge : 9 * level ^ 8 < actualWeakCellThreshold a n)
    (hCentersV : ∀ c ∈ centers, c ∈ V) (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c, Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hOverlap : ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card ≤ overlap)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss) :
    let d := level ^ 8
    let κ := actualUsedCenterCap d d a
    ∃ B₁ : Family (Fin n), ∃ D : FiniteCompletionCliqueData (Fin n),
      B₁ ⊆ fixedDecompositionCore H U ∧
      level * (fixedDecompositionCore H U \ B₁).card ≤ 256 * n ^ 3 ∧
      D.ground = U ∧ D.K ⊆ B₁ ∧
      (∀ x y, (reciprocalUsedLabelFiber D x y).card ≤ κ) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → (D.K.filter fun E => Q ⊆ E).card ≤ d) ∧
      let F := clearUsedParentThenReciprocal D
      (fixedDecompositionCore H U \ F.K).card ≤
        (fixedDecompositionCore H U \ B₁).card +
          (2 * (actualWeakCellThreshold a n - 1) * U.card.choose 2 +
            d ^ 2 * U.card ^ 2 * κ ^ 2 + (D.K \ F.K).card) ∧
      10 * H.card + (rankFourNonprivateFacets F.K U).card + 6 * (rankFourAllPrivateEdges F.K U).card ≤
        10 * U.card.choose 3 + 2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) + 4 * overlap +
          10 * (outerLoss + ((fixedDecompositionCore H U \ B₁).card +
            (2 * (actualWeakCellThreshold a n - 1) * U.card.choose 2 +
              d ^ 2 * U.card ^ 2 * κ ^ 2 + (D.K \ F.K).card))) := by
  classical
  let B := fixedDecompositionCore H U
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hUniformB : Uniform 4 B := fun _ hE => hUniform (hBH hE)
  obtain ⟨B₁, hB₁B, hLoss, _, hPair₁, hFacet₁⟩ := exists_actual_bounded_degree_regularization
    B q level hLevel hRange (admissible_mono hBH hH) hUniformB hVertex hPair hFacet
  have hFacetU : ∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions B₁ U Q).card ≤ level ^ 8 := by
    intro Q hQ
    apply (Finset.card_le_card ?_).trans (hFacet₁ Q hQ)
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
  have hScale := actual_used_center_cap_scale (level ^ 8) (level ^ 8) n a ha
  obtain ⟨D, hDU, hDB, hFiber, hCap, hMaster⟩ := exists_actual_original_master_after_regularization
    (actualWeakCellThreshold a n) (level ^ 8) (level ^ 8 * n)
    (actualUsedCenterCap (level ^ 8) (level ^ 8) a) fallback L centers owner overlap outerLoss
    hH hUniform hUsubV hB₁B hFacetU hLarge hPair₁ hScale hCentersV hCentersU
    hLayerEdges hLayerGround hU hOverlap hOriginal
  exact ⟨B₁, D, hB₁B, hLoss, hDU, hDB, hFiber, hCap, hMaster⟩

end JSP523.Rank4
