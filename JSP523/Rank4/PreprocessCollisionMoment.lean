import JSP523.Rank4.PreprocessCellMoment
import JSP523.Rank4.NativeFacetDoubleCount

/-!
# Actual pair-collision moment and high-codegree regularization

The second moment of completion degrees is exactly twice the common-cell
incidence count.  This turns local degree caps into a finite deletion budget.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem two_mul_choose_two_eq (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  have hdiv : 2 * ((n * (n - 1)) / 2) = n * (n - 1) := by
    exact Nat.mul_div_cancel' heven.two_dvd
  simpa [Nat.mul_comm] using hdiv

omit [Fintype α] in
/-- The ordered collision moment is twice the actual common-cell sum. -/
theorem completion_collision_moment_eq_two_common_root_cell_sum
    (K : Family α) (U : Edge α) (hUniform : Uniform 4 K) :
    (∑ T ∈ U.powersetCard 3,
      (facetCompletions K U T).card *
        ((facetCompletions K U T).card - 1)) =
      2 * (∑ P ∈ U.powersetCard 2, (commonRootCell K U P).card) := by
  classical
  calc
    _ = ∑ T ∈ U.powersetCard 3,
        2 * (facetCompletions K U T).card.choose 2 := by
          apply Finset.sum_congr rfl
          intro T _
          symm
          exact two_mul_choose_two_eq (facetCompletions K U T).card
    _ = 2 * ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 := by
          rw [Finset.mul_sum]
    _ = 2 * ∑ P ∈ U.powersetCard 2,
        (commonRootCell K U P).card := by
          rw [common_root_facet_completion_double_count K U hUniform]

omit [Fintype α] in
/-- With actual pair and facet degree caps, deleting high-codegree triples
regularizes the four-family at explicit cost. -/
theorem high_codegree_deletion_regularizes_of_degree_caps
    (F : Family α) (U : Edge α) (R M D : ℕ)
    (hUniform : Uniform 4 F)
    (hAdmissible : Admissible F)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree F P ≤ M)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions F U T).card ≤ D) :
    ∃ K : Family α,
      K ⊆ F ∧
      R * (F \ K).card ≤
        2 * (U.powersetCard 2).card * max M (9 * D) ∧
      (∀ T ∈ U.powersetCard 3,
        (tripleCompletionVertices K U T).card ≤ R) := by
  classical
  have hCell := common_root_cell_sum_le_of_degree_caps hAdmissible hFacet hPair
  have hMoment :
      (∑ T ∈ U.powersetCard 3,
        (facetCompletions F U T).card *
          ((facetCompletions F U T).card - 1)) ≤
        2 * (U.powersetCard 2).card * max M (9 * D) := by
    rw [completion_collision_moment_eq_two_common_root_cell_sum F U hUniform]
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hCell
  obtain ⟨K, hKF, hLoss, hRegular⟩ :=
    high_codegree_deletion_regularizes F U R
      (2 * (U.powersetCard 2).card * max M (9 * D)) hMoment
  exact ⟨K, hKF, hLoss, hRegular⟩

end JSP523.Rank4
