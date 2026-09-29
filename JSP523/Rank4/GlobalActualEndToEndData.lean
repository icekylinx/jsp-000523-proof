import JSP523.Rank4.PreprocessEndToEndMaster
import JSP523.Rank4.PreprocessInitialOuterCoverRegularization
import JSP523.Rank4.GlobalActualEndToEndLimits

/-! # Actual eventual preprocessing data for the original finite master -/

namespace JSP523.Rank4

structure ActualEndToEndData {n : ℕ} (H : Family (Fin n)) (U : Edge (Fin n))
    (level : ℕ) (a : ℝ) (overlap outerLoss : ℕ) where
  regularized : Family (Fin n)
  completion : FiniteCompletionCliqueData (Fin n)
  regularized_sub : regularized ⊆ fixedDecompositionCore H U
  regularized_loss : level * (fixedDecompositionCore H U \ regularized).card ≤ 256 * n ^ 3
  ground_eq : completion.ground = U
  completion_sub : completion.K ⊆ regularized
  fiber_cap : ∀ x y, (reciprocalUsedLabelFiber completion x y).card ≤ actualUsedCenterCap (level ^ 8) (level ^ 8) a
  facet_cap : ∀ Q : Edge (Fin n), Q.card = 3 → (completion.K.filter fun E => Q ⊆ E).card ≤ level ^ 8
  cleanup_bound : (fixedDecompositionCore H U \ (clearUsedParentThenReciprocal completion).K).card ≤
    (fixedDecompositionCore H U \ regularized).card +
      (2 * (actualWeakCellThreshold a n - 1) * U.card.choose 2 +
        (level ^ 8) ^ 2 * U.card ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 +
        (completion.K \ (clearUsedParentThenReciprocal completion).K).card)
  master : 10 * H.card + (rankFourNonprivateFacets (clearUsedParentThenReciprocal completion).K U).card +
      6 * (rankFourAllPrivateEdges (clearUsedParentThenReciprocal completion).K U).card ≤
    10 * U.card.choose 3 + 2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) + 4 * overlap +
      10 * (outerLoss + ((fixedDecompositionCore H U \ regularized).card +
        (2 * (actualWeakCellThreshold a n - 1) * U.card.choose 2 +
          (level ^ 8) ^ 2 * U.card ^ 2 * (actualUsedCenterCap (level ^ 8) (level ^ 8) a) ^ 2 +
          (completion.K \ (clearUsedParentThenReciprocal completion).K).card)))

/-- Initial outer-cover caps imply actual master data for every sufficiently
large size.  The threshold depends only on the fixed level and weak-cell coefficient. -/
theorem eventually_actual_end_to_end_data
    (level : ℕ) (hLevel : 256 ≤ level) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (H : Family (Fin n)) (U V : Edge (Fin n)) (_fallback : Fin n)
      (L : Fin n → Family (Fin n)) (centers : Finset (Fin n))
      (owner : Edge (Fin n) → Fin n) (overlap outerLoss : ℕ),
    Admissible H → Uniform 4 H → U ⊆ V →
    (∀ v, (((fixedDecompositionCore H U).filter fun E => v ∈ E).card : ℝ) ≤ (n : ℝ) ^ (27 / 10 : ℝ)) →
    (∀ Q : Edge (Fin n), Q.card = 3 →
      (rankFourFacetParents (fixedDecompositionCore H U) Q).card < initialOuterTripleThreshold n) →
    (∀ c ∈ centers, c ∈ V) → (∀ c ∈ centers, c ∉ U) →
    (∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H) →
    (∀ c ∈ centers, ∀ Q ∈ L c, Q ∈ U.powersetCard 3) → 3 ≤ U.card →
    ((centers.biUnion (pairOwnerCleanedLink L owner) ∩ rankFourFacetShadow (fixedDecompositionCore H U) U).card ≤ overlap) →
    (H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card + (fixedDecompositionCore H U).card + outerLoss) →
    Nonempty (ActualEndToEndData H U level a overlap outerLoss) := by
  filter_upwards [eventually_initial_outer_regularization_caps,
    actual_weak_cell_threshold_eventually_large (level ^ 8) a ha] with n hCaps hLarge
  intro H U V fallback L centers owner overlap outerLoss hH hUniform hUV hVertex hFacet hCV hCU hLE hLG hU hOverlap hOriginal
  have hUniformB : Uniform 4 (fixedDecompositionCore H U) := by
    intro E hE
    exact hUniform (Finset.mem_filter.mp hE).1
  obtain ⟨hRange, hVB, hPB, hFB⟩ := hCaps (fixedDecompositionCore H U) hUniformB hVertex hFacet
  obtain ⟨B₁, D, hB₁, hReg, hDU, hD, hFiber, hCap, hCleanup, hMaster⟩ :=
    exists_actual_master_from_initial_degree_range H U V (initialOuterRegularizationScale n) level a
      fallback L centers owner overlap outerLoss hH hUniform hUV hLevel hRange ha hVB hPB hFB hLarge
      hCV hCU hLE hLG hU hOverlap hOriginal
  exact ⟨⟨B₁, D, hB₁, hReg, hDU, hD, hFiber, hCap, hCleanup, hMaster⟩⟩

/-- The record's actual completion data automatically supplies every cap
needed by the reciprocal error theorem. -/
theorem ActualEndToEndData.completion_caps
    {n level overlap outerLoss : ℕ} {H : Family (Fin n)} {U : Edge (Fin n)} {a : ℝ}
    (A : ActualEndToEndData H U level a overlap outerLoss) :
    (∀ E ∈ A.completion.K, E ⊆ A.completion.ground) ∧
    (∀ Q : Edge (Fin n), Q.card = 3 → (A.completion.K.filter fun E => Q ⊆ E).card ≤ level ^ 8) ∧
    (∀ x y, (reciprocalUsedLabelFiber A.completion x y).card ≤ actualUsedCenterCap (level ^ 8) (level ^ 8) a) := by
  refine ⟨?_, A.facet_cap, A.fiber_cap⟩
  intro E hE
  rw [A.ground_eq]
  exact (Finset.mem_filter.mp (A.regularized_sub (A.completion_sub hE))).2

end JSP523.Rank4
