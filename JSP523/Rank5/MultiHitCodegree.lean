import JSP523.Rank5.ShadowExtraction

/-!
# Multi-hit layer bound from actual pair codegrees

This is the exact finite count behind (IV.4.3): an edge meeting a removed
vertex set in two points is counted by at least one of its pairs there.
-/

namespace JSP523.Rank5

open JSP523

/-- Every edge meeting `X` at least twice is charged to an actual pair
codegree. No uniformity or admissibility is needed for this incidence count. -/
theorem multiple_removed_edges_le_pair_codegree
    {α : Type*} [DecidableEq α]
    (H : Family α) (X : Edge α) (D : ℕ)
    (hPair : ∀ Q ∈ X.powersetCard 2,
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    (multipleRemovedEdges H X).card ≤ X.card.choose 2 * D := by
  classical
  let pairs := X.powersetCard 2
  let fiber : Edge α → Family α := fun Q => H.filter fun E => Q ⊆ E
  have hCover : multipleRemovedEdges H X ⊆ pairs.biUnion fiber := by
    intro E hE
    obtain ⟨hEH, hTwo⟩ := Finset.mem_filter.mp hE
    obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hTwo
    have hQX : Q ⊆ X :=
      hQsub.trans (Finset.inter_subset_right)
    have hQE : Q ⊆ E :=
      hQsub.trans (Finset.inter_subset_left)
    exact Finset.mem_biUnion.mpr
      ⟨Q, Finset.mem_powersetCard.mpr ⟨hQX, hQcard⟩,
        Finset.mem_filter.mpr ⟨hEH, hQE⟩⟩
  have hUnion := Finset.card_biUnion_le (s := pairs) (t := fiber)
  have hCap : (∑ Q ∈ pairs, (fiber Q).card) ≤ pairs.card * D := by
    simpa [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul pairs (fun Q => (fiber Q).card) D hPair
  calc
    (multipleRemovedEdges H X).card ≤ (pairs.biUnion fiber).card :=
      Finset.card_le_card hCover
    _ ≤ ∑ Q ∈ pairs, (fiber Q).card := hUnion
    _ ≤ pairs.card * D := hCap
    _ = X.card.choose 2 * D := by simp [pairs, Finset.card_powersetCard]

end JSP523.Rank5
