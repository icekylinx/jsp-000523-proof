import JSP523.Rank4.PreprocessCenterGraphDegree
import JSP523.Rank4.PreprocessReciprocalC4Asymptotic
import JSP523.Rank4.GlobalDegreeTail

/-!
# Reciprocal cleanup from the finite center-graph count

The label-fiber cap in the rank-four reciprocal cleanup follows from the
weak-cell threshold, facet degree, pair degree, and their scale inequality.
-/

namespace JSP523.Rank4

/-- The actual reciprocal cleanup has vanishing binomial-normalized loss
under the finite degree and threshold conditions of §III.A.6. -/
theorem clear_used_parent_then_reciprocal_loss_choose_ratio_of_degree_caps
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (Dcap Kstar : ℕ) (t M : ℕ → ℕ)
    (hGround : ∀ n : ℕ, ∀ E ∈ (D n).K, E ⊆ (D n).ground)
    (hFacet : ∀ n : ℕ, ∀ T : Edge (Fin n), T.card = 3 →
      ((D n).K.filter fun E => T ⊆ E).card ≤ Dcap)
    (hClearedRoots : ∀ n : ℕ, ∀ P ∈ (D n).ground.powersetCard 2,
      (commonRootCell (D n).K (D n).ground P).card = 0 ∨
        t n ≤ (commonRootCell (D n).K (D n).ground P).card)
    (hPair : ∀ n : ℕ, ∀ a b : Fin n,
      rankFourPairDegree (D n).K ({a, b} : Edge (Fin n)) ≤ M n)
    (ht : ∀ n : ℕ, 0 < t n)
    (hScale : ∀ n : ℕ, (Dcap - 1) * M n ≤ t n * Kstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) /
          (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
  classical
  have hFacetCompletions (n : ℕ) (T : Edge (Fin n))
      (hT : T.card = 3) :
      (facetCompletions (D n).K (D n).ground T).card ≤ Dcap := by
    rw [facet_completions_card_eq_parent_edges
      (D n).K (D n).ground T (D n).uniform_four (hGround n) hT]
    exact hFacet n T hT
  have hLabel (n : ℕ) (a b : Fin n) :
      (reciprocalUsedLabelFiber (D n) a b).card ≤ Kstar := by
    by_cases ha : a ∈ (D n).ground
    · exact reciprocal_used_label_fiber_card_le_of_scale_budget
        (D n) a b (t n) Dcap (M n) Kstar (ht n) ha
        (common_triple_cells_cleared_of_common_roots
          (D n) (t n) (hGround n) (hClearedRoots n))
        (hFacetCompletions n) (hPair n a b) (hScale n)
    · rw [reciprocal_used_label_fiber_empty_of_outside_ground
        (D n) a b (hGround n) ha]
      simp
  exact clear_used_parent_then_reciprocal_loss_choose_ratio_tendsto_zero
    D Dcap Kstar hGround hFacet hLabel

end JSP523.Rank4
